# acquisition.py
import os, math, time, uuid, queue, threading, tempfile, datetime
from typing import List, Callable, Optional, Dict, Any, Tuple
import numpy as np

# --- NI-DAQmx ---------------------------------------------------------------
_nidaqmx_import_error = None
try:
    import nidaqmx
    from nidaqmx.system import System
    from nidaqmx.stream_readers import AnalogMultiChannelReader
except Exception as _e:
    nidaqmx = None
    System = None
    AnalogMultiChannelReader = None
    _nidaqmx_import_error = _e

# --- TDMS -------------------------------------------------------------------
from nptdms import TdmsWriter, ChannelObject, RootObject, GroupObject


def _align_up(value: int, base: int) -> int:
    if base <= 0:
        return value
    return int(math.ceil(value / float(base)) * base)


class AcquisitionManager:
    """
    Core NI-9201 con:
      • stream continuo Every N Samples
      • grafici decimati
      • writer TDMS a rotazione (default 60 s) SENZA PERDITE (sample-accurate)
      • scrittura streaming (mini-segmenti) a RAM costante
      • Time continuo in ogni file e proprietà wf_* coerenti
      • stop_graceful: svuota il buffer driver e salva il residuo
    """

    def __init__(self, sample_rate=10000.0, callback_chunk=1000, rotate_seconds=60):
        self.sample_rate = float(sample_rate)
        self.callback_chunk = int(callback_chunk)
        self.rotate_seconds = int(rotate_seconds)
        self._closing = False            # vero durante stop/chiusura
        self._cb_registered = False      # abbiamo registrato l'Every N Samples?
        self.current_rate_hz: Optional[float] = None
        self.current_agg_rate_hz: Optional[float] = None
        self.max_single_rate_hz: Optional[float] = None
        self.max_multi_rate_hz: Optional[float] = None

        self._start_channel_names: List[str] = []

        self._task = None
        self._reader: Optional[AnalogMultiChannelReader] = None
        self._running = False

        # Coda: (start_index_globale, buffer[chan x samples])
        self._queue: "queue.Queue[Tuple[int, np.ndarray]]" = queue.Queue(maxsize=4000)
        self._writer_thread: Optional[threading.Thread] = None
        self._writer_stop = threading.Event()

        # Cartella writer (sostituita dalla UI quando parte il salvataggio)
        self.temp_dir = os.path.join(tempfile.gettempdir(), f"ni9201_acq_{uuid.uuid4().hex}")
        os.makedirs(self.temp_dir, exist_ok=True)

        # Zero / mappe / canali
        self._zero: Dict[str, Optional[float]] = {}
        self._ai_channels: List[str] = []
        self._channel_names: List[str] = []

        self._last_raw: Dict[str, Optional[float]] = {f"ai{i}": None for i in range(8)}
        self._sensor_map_by_phys: Dict[str, Dict[str, Any]] = {}

        # Registrazione TDMS
        self._recording_enabled = False
        self._recording_toggle = threading.Event()

        # Callback UI
        self.on_channel_value: Optional[Callable[[str, float], None]] = None
        self.on_new_instant_block: Optional[Callable[[np.ndarray, List[np.ndarray], List[str]], None]] = None
        self.on_new_chart_points: Optional[Callable[[np.ndarray, List[np.ndarray], List[str]], None]] = None

        # Decimazione grafico concatenato
        self._chart_decim = 10

        # Temporalizzazione sample-accurate
        self._t0_epoch_s: Optional[float] = None  # tempo assoluto del campione #0
        self._global_samples: int = 0             # contatore globale campioni per canale

    # -------------------- API verso la UI --------------------
    def set_output_directory(self, path: str):
        if not path:
            return
        self.temp_dir = os.path.abspath(path)
        os.makedirs(self.temp_dir, exist_ok=True)

    def set_sensor_map(self, sensor_map_by_phys: Dict[str, Dict[str, Any]]):
        self._sensor_map_by_phys = dict(sensor_map_by_phys or {})

    @property
    def recording_enabled(self) -> bool:
        return self._recording_enabled

    def set_recording(self, enable: bool):
        prev = self._recording_enabled
        self._recording_enabled = bool(enable)
        if prev != self._recording_enabled:
            self._recording_toggle.set()

    def zero_channel(self, chan_name: str):
        self._zero[chan_name] = None  # al prossimo giro memorizza come zero

    def get_last_value(self, chan_name: str, apply_zero: bool = False) -> Optional[float]:
        val = self._last_raw.get(chan_name)
        if val is None:
            return None
        if apply_zero and chan_name in self._zero and self._zero[chan_name] is not None:
            return abs(val - self._zero[chan_name])
        return val

    # -------------------- Scoperta / limiti modulo --------------------
    def list_ni9201_devices(self) -> List[str]:
        """Versione tollerante: include moduli simulati anche quando product_type è vuoto."""
        if System is None:
            return []
        found = []
        try:
            for dev in System.local().devices:
                name = getattr(dev, "name", "")
                pt = (getattr(dev, "product_type", "") or "")
                pt_u = pt.upper()
                is_9201 = "9201" in pt_u

                # Heuristica di fallback: 9201 ha 8 analog input fisici
                try:
                    n_ai = len(getattr(dev, "ai_physical_chans", []))
                except Exception:
                    n_ai = 0
                looks_like_9201 = (n_ai == 8)

                if is_9201 or looks_like_9201:
                    found.append(name)
        except Exception:
            pass
        return found

    def list_ni9201_devices_meta(self) -> List[Dict[str, Any]]:
        """
        Restituisce metadati robusti per i moduli NI-9201 (reali o simulati).
        Ogni elemento: {"name","product_type","is_simulated","chassis"}
        """
        if System is None:
            return []
        out: List[Dict[str, Any]] = []
        try:
            for dev in System.local().devices:
                name = getattr(dev, "name", "")
                pt = (getattr(dev, "product_type", "") or "")
                pt_u = pt.upper()

                # match flessibile
                try:
                    n_ai = len(getattr(dev, "ai_physical_chans", []))
                except Exception:
                    n_ai = 0
                if "9201" not in pt_u and n_ai != 8:
                    continue

                # simulato?
                is_sim = bool(getattr(dev, "is_simulated", False))

                # chassis: prima prova con property, poi fallback sul prefisso 'cDAQxMody' → 'cDAQx'
                ch_name = ""
                try:
                    ch = getattr(dev, "chassis_device", None)
                    ch_name = getattr(ch, "name", "") if ch is not None else ""
                except Exception:
                    ch_name = ""
                if not ch_name:
                    ch_name = name.split("Mod")[0] if "Mod" in name else ""

                out.append({
                    "name": name,
                    "product_type": pt if pt else "NI 9201",
                    "is_simulated": is_sim,
                    "chassis": ch_name,
                })
        except Exception:
            pass
        return out

    def _get_device_by_name(self, name):
        if System is None:
            return None
        for d in System.local().devices:
            if d.name == name:
                return d
        return None

    def _read_device_caps(self, device_name: str):
        self.max_single_rate_hz = None
        self.max_multi_rate_hz = None
        dev = self._get_device_by_name(device_name)
        if dev is None:
            self.max_multi_rate_hz = 500_000.0
            self.max_single_rate_hz = 500_000.0
            return
        try:
            v = getattr(dev, "ai_max_single_chan_rate", None)
            self.max_single_rate_hz = float(v) if v is not None else None
        except Exception:
            pass
        try:
            v = getattr(dev, "ai_max_multi_chan_rate", None)
            self.max_multi_rate_hz = float(v) if v is not None else None
        except Exception:
            pass
        if not self.max_multi_rate_hz or self.max_multi_rate_hz <= 0:
            self.max_multi_rate_hz = 500_000.0
        if not self.max_single_rate_hz or self.max_single_rate_hz <= 0:
            self.max_single_rate_hz = self.max_multi_rate_hz

    def _compute_per_channel_rate(self, device_name: str, n_channels: int) -> float:
        self._read_device_caps(device_name)
        agg_max = float(self.max_multi_rate_hz or 500_000.0)
        single_max = float(self.max_single_rate_hz or agg_max)
        n = max(1, int(n_channels))
        return float(single_max) if n == 1 else float(agg_max) / n

    # -------------------- Start / Stop --------------------
    def start(self, device_name: str, ai_channels: List[str], channel_names: List[str]) -> bool:
        if nidaqmx is None:
            return False
        if self._running:
            return True

        self._ai_channels = ai_channels[:]
        self._channel_names = channel_names[:]
        self._start_channel_names = channel_names[:]

        try:
            # --- rate per-canale (rispetta i limiti del 9201) ---
            per_chan = self._compute_per_channel_rate(device_name, len(self._ai_channels))
            self.current_rate_hz = per_chan
            self.current_agg_rate_hz = per_chan * max(1, len(self._ai_channels))

            # --- callback ogni ~10 ms, multipli di 16 ---
            target_cb_ms = 10.0
            raw_chunk = max(200, int(per_chan * target_cb_ms / 1000.0))
            self.callback_chunk = _align_up(raw_chunk, 16)

            # --- buffer driver capiente (evita -200279) ---
            daq_buf_seconds = 15.0
            desired = int(per_chan * daq_buf_seconds)
            daq_buf_samps = _align_up(max(desired, self.callback_chunk * 100), self.callback_chunk)

            # --- QUEUE dimensionata (max ~30 s o 256 MB) ---
            nch = max(1, len(self._ai_channels))
            bytes_per_block = nch * self.callback_chunk * 8  # float64
            queue_target_seconds = 30
            blocks_target = max(50, int(per_chan * queue_target_seconds / self.callback_chunk))
            MEMORY_BUDGET_MB = 256
            blocks_mem = max(50, int((MEMORY_BUDGET_MB * 1024 * 1024) / max(1, bytes_per_block)))
            queue_capacity = min(blocks_target, blocks_mem)
            self._queue = queue.Queue(maxsize=queue_capacity)

            # --- reset timing globale ---
            self._t0_epoch_s = None
            self._global_samples = 0

            # --- config NI-DAQmx ---
            self._task = nidaqmx.Task()
            for ch in self._ai_channels:
                self._task.ai_channels.add_ai_voltage_chan(
                    f"{device_name}/{ch}", min_val=-10.0, max_val=10.0
                )

            timing_prealloc = self.callback_chunk * 20
            self._task.timing.cfg_samp_clk_timing(
                rate=per_chan,
                sample_mode=nidaqmx.constants.AcquisitionType.CONTINUOUS,
                samps_per_chan=timing_prealloc
            )
            self._task.in_stream.input_buf_size = daq_buf_samps

            self._reader = AnalogMultiChannelReader(self._task.in_stream)
            self._task.register_every_n_samples_acquired_into_buffer_event(
                self.callback_chunk, self._on_every_n_samples
            )
            self._cb_registered = True

            # --- writer thread ---
            self._writer_stop.clear()
            self._writer_thread = threading.Thread(target=self._writer_loop, daemon=True)
            self._writer_thread.start()

            # --- start acquisizione ---
            self._running = True
            self._task.start()

            # --- decimazione per grafico ---
            self._chart_decim = max(1, int(self.current_rate_hz // 50))
            return True

        except Exception as e:
            print("Errore start:", e)
            self._cleanup()
            return False

    def stop(self):
        """Stop immediato: deregistra il callback PRIMA di fermare/chiudere il task."""
        self._closing = True
        self._running = False
        self.set_recording(False)

        # stacca il callback per evitare chiamate mentre chiudiamo
        self._unregister_callbacks()
        time.sleep(0.01)  # piccolo respiro per drenare callback in volo

        try:
            if self._task:
                self._task.stop()
        except Exception:
            pass
        try:
            if self._task:
                self._task.close()
        except Exception:
            pass
        self._task = None

        # chiusura writer
        self._writer_stop.set()
        self._recording_toggle.set()
        if self._writer_thread and self._writer_thread.is_alive():
            self._writer_thread.join(timeout=10)
        self._writer_thread = None
        self._closing = False

    def stop_graceful(self, wait_ms: int = 150):
        """
        Stop con salvataggio completo fino all'istante di chiamata.
        """
        self._closing = True
        try:
            if self._task is None:
                # solo writer
                self._running = False
                self.set_recording(False)
                self._writer_stop.set()
                self._recording_toggle.set()
                if self._writer_thread and self._writer_thread.is_alive():
                    self._writer_thread.join(timeout=10)
                self._writer_thread = None
                return

            # assicura writer attivo per salvare il residuo
            self.set_recording(True)

            # breve attesa per permettere agli ultimi callback di enqueue-are
            t0 = time.time()
            while (time.time() - t0) * 1000.0 < wait_ms:
                time.sleep(0.005)

            # drena il buffer hardware con lettura sincrona finché ci sono campioni
            try:
                avail = int(self._task.in_stream.avail_samp_per_chan)
            except Exception:
                avail = 0
            while avail and avail > 0:
                nch = len(self._ai_channels)
                buf = np.empty((nch, avail), dtype=np.float64)
                # NB: leggiamo prima di deregistrare il callback
                self._reader.read_many_sample(buf, avail, timeout=1.0)
                start_idx = self._global_samples
                self._global_samples += avail
                try:
                    self._queue.put_nowait((start_idx, buf))
                except queue.Full:
                    self._queue.put((start_idx, buf), timeout=0.5)
                try:
                    avail = int(self._task.in_stream.avail_samp_per_chan)
                except Exception:
                    break

            # da qui in poi non vogliamo più callback
            self._unregister_callbacks()
            time.sleep(0.01)

            # chiudi il segmento parziale
            self.set_recording(False)
            self._recording_toggle.set()

        finally:
            # ferma e chiudi il task
            try:
                self._running = False
                if self._task:
                    self._task.stop()
            except Exception:
                pass
            try:
                if self._task:
                    self._task.close()
            except Exception:
                pass
            self._task = None

            # chiudi writer
            self._writer_stop.set()
            self._recording_toggle.set()
            if self._writer_thread and self._writer_thread.is_alive():
                self._writer_thread.join(timeout=10)
            self._writer_thread = None
            self._closing = False

    def _to_float(self, value, default):
        """Cast robusto a float: se fallisce, torna default."""
        try:
            return float(value)
        except Exception:
            return default

    # -------------------- Callback DAQ --------------------
    def _on_every_n_samples(self, task_handle, every_n_samples_event_type, number_of_samples, callback_data):
        # Uscita rapida se stiamo chiudendo o il task/reader non è più valido
        if (not self._running) or self._closing or (self._task is None) or (self._reader is None):
            return 0
        try:
            nch = len(self._ai_channels)
            if nch <= 0 or number_of_samples <= 0:
                return 0

            # Leggi dal driver
            buf = np.empty((nch, number_of_samples), dtype=np.float64)
            self._reader.read_many_sample(buf, number_of_samples, timeout=0.0)

            ts_ns = time.time_ns()

            # inizializza t0 con l'epoch del PRIMO campione del PRIMO blocco
            if self._t0_epoch_s is None:
                fs = float(self.current_rate_hz or 1.0)
                self._t0_epoch_s = (ts_ns / 1e9) - (number_of_samples / fs)

            # nomi “freeze” allo start (se non presenti, fallback ai fisici)
            start_names = list(self._start_channel_names or self._ai_channels or [])
            if len(start_names) < nch:
                start_names += [self._ai_channels[i] for i in range(len(start_names), nch)]
            elif len(start_names) > nch:
                start_names = start_names[:nch]

            # ultimo valore + zero + calibrazione → verso UI con nomi di start
            for i, ch in enumerate(self._ai_channels):
                raw_val = float(buf[i, -1])
                self._last_raw[ch] = raw_val
                val = raw_val
                baseline = self._zero.get(ch, None)
                if baseline is not None:
                    try:
                        val = val - float(baseline)   # shift sottratto
                    except Exception:
                        pass
                meta = self._sensor_map_by_phys.get(ch, {})
                a = self._to_float(meta.get("a", 1.0), 1.0)
                b = self._to_float(meta.get("b", 0.0), 0.0)
                val = a * val + b

                if self.on_channel_value:
                    try:
                        self.on_channel_value(start_names[i], val)
                    except Exception as e:
                        # Non fermare l'acquisizione per un problema lato UI
                        print("Callback warning (channel_value):", e)

            # enqueue blocco (LOSSY: se pieno, droppa il più vecchio)
            start_idx = self._global_samples
            self._global_samples += number_of_samples
            try:
                self._queue.put_nowait((start_idx, buf))
            except queue.Full:
                dropped_old = 0
                try:
                    _ = self._queue.get_nowait()  # libera 1 vecchio blocco
                    dropped_old = 1
                except queue.Empty:
                    pass
                try:
                    self._queue.put_nowait((start_idx, buf))
                except queue.Full:
                    # ancora piena ⇒ droppa il blocco corrente
                    print("Callback warning: queue full; dropped block (also dropped_oldest=%d)" % dropped_old)

            # feed grafico (nomi di start, tempo corretto)
            if self.on_new_instant_block or self.on_new_chart_points:
                fs = float(self.current_rate_hz or 1.0)
                t0 = (self._t0_epoch_s or 0.0) + (start_idx / fs)
                t = t0 + np.arange(number_of_samples, dtype=np.float64) / fs
                ys = [buf[i, :] for i in range(nch)]

                if self.on_new_instant_block:
                    try:
                        self.on_new_instant_block(t, ys, start_names)
                    except Exception as e:
                        print("Callback warning (instant_block):", e)

                if self.on_new_chart_points:
                    try:
                        dec_step = int(self._chart_decim or 1)
                        if dec_step <= 0:
                            dec_step = 1
                        dec = slice(None, None, dec_step)
                        self.on_new_chart_points(t[dec], [y[dec] for y in ys], start_names)
                    except Exception as e:
                        print("Callback warning (chart_points):", e)

            return 0
        except Exception as e:
            print("Callback error:", e)
            return 0

    # -------------------- Writer TDMS (streaming, no buchi) --------------------
    def _writer_loop(self):
        fs = float(self.current_rate_hz or 1.0)
        seg_target_samples = max(1, int(self.rotate_seconds * fs))

        # mini-scrittura (streaming) per RAM costante
        MIN_WRITE_SEC = 0.2
        mini_target_samples = max(1, int(MIN_WRITE_SEC * fs))

        writer: Optional[TdmsWriter] = None
        seg_start_idx: Optional[int] = None        # indice globale del primo campione del file corrente
        seg_written: int = 0                       # campioni già scritti nel file corrente
        open_file_path: Optional[str] = None

        def _seg_start_time_s(idx: int) -> float:
            t0 = float(self._t0_epoch_s or time.time())
            return t0 + (idx / fs)

        def _open_segment(idx0: int):
            nonlocal writer, seg_start_idx, seg_written, open_file_path
            _close_segment()
            seg_start_idx = int(idx0)
            seg_written = 0
            start_s = _seg_start_time_s(seg_start_idx)
            fname = f"segment_{int(start_s*1e9)}.tdms"
            open_file_path = os.path.join(self.temp_dir, fname)
            writer = TdmsWriter(open(open_file_path, "wb"))

        def _close_segment():
            nonlocal writer, open_file_path, seg_written
            if writer:
                try:
                    writer.close()
                except Exception:
                    pass
                # elimina segmenti senza campioni
                try:
                    if (seg_written or 0) <= 0 and open_file_path and os.path.isfile(open_file_path):
                        os.remove(open_file_path)
                except Exception:
                    pass
            writer = None
            open_file_path = None
            seg_written = 0

        def _write_miniseg(start_idx_in_file: int, block: np.ndarray):
            """
            Scrive un mini-segmento nel file corrente.
            - Il canale "Time" è continuo nel file: t = offset_in_file + arange(n)/fs
            - I dati sono salvati in unità ingegneristiche (Valore istantaneo).
            - Nomi canale TDMS: sanificati, deduplicati e con 'Time' riservato.
            """
            # Pre-condizioni minime
            if writer is None or seg_start_idx is None:
                return
            try:
                n = int(block.shape[1])
            except Exception:
                return
            if n <= 0:
                return

            # 1) Nomi TDMS effettivi, sanificati e univoci
            try:
                tdms_names = list(self._current_tdms_names())
            except Exception as e:
                print("Writer warning (names map):", e)
                tdms_names = list(self._ai_channels)

            # Se il numero di canali nel blocco > nomi disponibili, estendi con fallback sicuri
            try:
                if len(tdms_names) < block.shape[0]:
                    used = set(["Time"]) | set(tdms_names)
                    for i in range(len(tdms_names), block.shape[0]):
                        base = self._sanitize_tdms_basename(
                            self._ai_channels[i] if i < len(self._ai_channels) else f"ai{i}"
                        )
                        name = base
                        k = 2
                        while name in used:
                            name = f"{base}_{k}"
                            k += 1
                        tdms_names.append(name)
                        used.add(name)
            except Exception as e:
                print("Writer warning (extend names):", e)

            # 2) Tempo relativo del mini-segmento
            try:
                start_s = _seg_start_time_s(seg_start_idx + start_idx_in_file)
                t_rel = (start_idx_in_file / fs) + (np.arange(n, dtype=np.float64) / fs)
            except Exception as e:
                print("Writer error (time vector):", e)
                return

            # 3) Oggetti TDMS: root & group
            try:
                root = RootObject(properties={
                    "sample_rate": fs,
                    "channels": ",".join(tdms_names),
                    "start_index": int(seg_start_idx),
                    "chunk_offset": int(start_idx_in_file),
                    "start_time_epoch_s": float(start_s),
                })
                group = GroupObject("Acquisition")
            except Exception as e:
                print("Writer error (root/group):", e)
                return

            # 4) Canali: Time + dati
            chans = []

            # 4.a) Canale "Time"
            try:
                chans.append(ChannelObject(
                    "Acquisition", "Time", t_rel, properties={
                        "unit_string": "s",
                        "wf_start_time": datetime.datetime.fromtimestamp(_seg_start_time_s(seg_start_idx)),
                        "wf_increment": 1.0 / fs,
                        "stored_domain": "time",
                    }
                ))
            except Exception as e:
                print("Writer warning (Time channel):", e)

            # 4.b) Canali dati (ingegnerizzati)
            try:
                num_ch = min(len(tdms_names), block.shape[0])
                for i in range(num_ch):
                    ui_name = tdms_names[i]
                    try:
                        phys = self._ai_channels[i] if i < len(self._ai_channels) else f"ai{i}"
                        meta = self._sensor_map_by_phys.get(phys, {})
                        sensor_name = meta.get("sensor_name", "Voltage")
                        unit_eng = meta.get("unit", "") if sensor_name != "Voltage" else "V"

                        # Cast robusto per a/b
                        a = self._to_float(meta.get("a", 1.0), 1.0)
                        b = self._to_float(meta.get("b", 0.0), 0.0)

                        # Applica zero (shift) se presente
                        raw = np.ascontiguousarray(block[i])  # Volt
                        baseline = self._zero.get(phys, None)
                        zero_eng = 0.0
                        if baseline is not None:
                            try:
                                raw = raw - float(baseline)
                                zero_eng = a * float(baseline)
                            except Exception:
                                zero_eng = 0.0

                        # Scala a*x + b → unità ingegneristiche
                        data_eng = a * raw + b

                        props = {
                            "description": sensor_name,
                            "unit_string": unit_eng,
                            "wf_start_time": datetime.datetime.fromtimestamp(_seg_start_time_s(seg_start_idx)),
                            "wf_increment": 1.0 / fs,
                            "physical_channel": phys,
                            "scale_a": a,
                            "scale_b": b,
                            "zero_applied": float(zero_eng),
                        }

                        chans.append(ChannelObject("Acquisition", ui_name, data_eng, properties=props))
                    except Exception as e:
                        # Non fermare l'intero blocco per un singolo canale
                        print(f"Writer warning (data channel {i}):", e)
            except Exception as e:
                print("Writer error (data channels build):", e)
                # Proseguiamo comunque alla write_segment con i canali costruiti fin qui

            # 5) Scrittura del segmento
            try:
                writer.write_segment([root, group] + chans)
            except Exception as e:
                # L'errore classico che preveniamo è: "Duplicate object paths found"
                print("Writer error (write_segment):", e)

        # --------- MAIN LOOP DEL WRITER ---------
        try:
            while not self._writer_stop.is_set():
                # Non in registrazione → drena eventuali dati e chiudi segmento
                if not self._recording_enabled:
                    _close_segment()
                    # svuota la coda per non accumulare RAM
                    while True:
                        try:
                            _ = self._queue.get_nowait()
                        except queue.Empty:
                            break
                    # attendi toggle o breve timeout
                    self._recording_toggle.wait(timeout=0.2)
                    self._recording_toggle.clear()
                    continue

                # Registrazione attiva → prendi un blocco
                try:
                    start_idx, buf = self._queue.get(timeout=0.2)
                except queue.Empty:
                    self._recording_toggle.wait(timeout=0.05)
                    self._recording_toggle.clear()
                    continue

                if writer is None:
                    _open_segment(start_idx)

                # riallinea se necessario (buco nei campioni)
                expected = (seg_start_idx + seg_written) if seg_start_idx is not None else start_idx
                if start_idx != expected:
                    _close_segment()
                    _open_segment(start_idx)

                # confine file + scrittura streaming
                block_idx = start_idx
                block = buf
                while block.shape[1] > 0:
                    remaining_file = seg_target_samples - seg_written
                    if remaining_file <= 0:
                        _close_segment()
                        _open_segment(block_idx)
                        remaining_file = seg_target_samples

                    take = min(remaining_file, block.shape[1])  # puoi limitare anche con mini_target_samples se vuoi
                    part = block[:, :take]
                    _write_miniseg(seg_written, part)
                    seg_written += take

                    if seg_written >= seg_target_samples:
                        _close_segment()
                        _open_segment(block_idx + take)

                    block_idx += take
                    block = block[:, take:]

            # uscita: drena e chiudi
            drained_any = False
            while True:
                try:
                    start_idx, buf = self._queue.get_nowait()
                    if writer is None:
                        _open_segment(start_idx)
                    expected = (seg_start_idx + seg_written) if seg_start_idx is not None else start_idx
                    if start_idx != expected:
                        _close_segment()
                        _open_segment(start_idx)
                    _write_miniseg(seg_written, buf)
                    seg_written += buf.shape[1]
                    drained_any = True
                except queue.Empty:
                    break
            _close_segment()

        except Exception as e:
            print("Writer error:", e)
            try:
                _close_segment()
            except Exception:
                pass

    # -------------------- Cleanup --------------------
    def _cleanup(self):
        self._running = False
        try:
            if self._task:
                self._task.close()
        except Exception:
            pass
        self._task = None

    # -------------------- Zeroing API --------------------
    def set_zero_raw(self, phys_chan: str, raw_value: Optional[float]):
        """Imposta lo zero per un canale come VALORE RAW in Volt (None per rimuoverlo)."""
        if phys_chan not in self._last_raw:
            self._last_raw[phys_chan] = None
        self._zero[phys_chan] = float(raw_value) if raw_value is not None else None

    def clear_zero(self, phys_chan: str):
        """Rimuove lo zero dal canale."""
        self.set_zero_raw(phys_chan, None)

    def get_last_raw(self, phys_chan: str) -> Optional[float]:
        """Ultimo valore RAW (Volt) letto su quel canale."""
        return self._last_raw.get(phys_chan)

    def get_last_engineered(self, phys_chan: str) -> Optional[float]:
        """
        Valore istantaneo in unità ingegneristiche, applicando zero (shift) e a*x+b.
        """
        raw = self._last_raw.get(phys_chan)
        if raw is None:
            return None
        meta = self._sensor_map_by_phys.get(phys_chan, {})
        a = float(meta.get("a", 1.0))
        b = float(meta.get("b", 0.0))
        baseline = self._zero.get(phys_chan, None)
        if baseline is not None:
            raw = raw - float(baseline)
        return a * raw + b

    def _unregister_callbacks(self):
        """Rimuove il callback Every N Samples dal task in modo sicuro."""
        try:
            if self._task and self._cb_registered:
                # In nidaqmx si deregistra passando callback=None
                self._task.register_every_n_samples_acquired_into_buffer_event(
                    self.callback_chunk, None
                )
        except Exception:
            pass
        self._cb_registered = False
        self._reader = None

    # --- Aggiornamento etichette canali dal lato UI ---
    def set_ui_name_for_phys(self, phys: str, ui_name: str):
        """Aggiorna il nome canale TDMS associato al canale fisico."""
        try:
            idx = self._ai_channels.index(phys)
        except ValueError:
            return
        # allunga se serve
        if len(self._channel_names) < len(self._ai_channels):
            self._channel_names = (self._channel_names + self._ai_channels)[:len(self._ai_channels)]
        self._channel_names[idx] = ui_name or phys
        # normalizza subito (dedup + sanificazione)
        try:
            self._channel_names = self._unique_tdms_names(self._channel_names)
        except Exception:
            pass

    def set_channel_labels(self, ordered_ui_names: list[str]):
        """Sostituisce l'elenco completo di nomi canale TDMS nell'ordine corrente."""
        n = len(self._ai_channels)
        if not ordered_ui_names:
            self._channel_names = self._ai_channels[:]
        else:
            self._channel_names = (ordered_ui_names + self._ai_channels)[:n]
        # normalizza (dedup + sanificazione)
        try:
            self._channel_names = self._unique_tdms_names(self._channel_names)
        except Exception:
            pass

    # -------------------- Helper nomi TDMS (livello classe) --------------------
    def _sanitize_tdms_basename(self, name: str) -> str:
        r"""
        Sanifica un'etichetta utente per l'uso come nome canale TDMS.
        - Rimuove caratteri problematici ( / \\ : * ? " < > | )
        - Normalizza spazi
        - Evita stringhe vuote
        """
        try:
            s = (name or "").strip()
            if not s:
                return "chan"
            for ch in '/\\:*?"<>|':
                s = s.replace(ch, "_")
            s = " ".join(s.split())          # comprime spazi multipli
            return s[:128] if s else "chan"  # limite prudente
        except Exception:
            return "chan"

    def _unique_tdms_names(self, ui_names: list[str]) -> list[str]:
        """
        Ritorna nomi TDMS sanificati e univoci nel contesto corrente.
        - Riserva 'Time' per il canale temporale
        - Mantiene l'ordine
        - Aggiunge suffissi _2, _3, ... se necessario
        """
        unique = []
        used = set(["Time"])  # 'Time' è riservato
        counters = {}
        for raw in (ui_names or []):
            base = self._sanitize_tdms_basename(raw)
            if base in used:
                n = counters.get(base, 1) + 1
                counters[base] = n
                cand = f"{base}_{n}"
                while cand in used:
                    n += 1
                    counters[base] = n
                    cand = f"{base}_{n}"
                name = cand
            else:
                used.add(base)
                counters.setdefault(base, 1)
                name = base
            unique.append(name)
        return unique

    def _current_tdms_names(self) -> list[str]:
        """
        Costruisce l'elenco dei nomi TDMS effettivi da usare ORA
        partendo dalle etichette UI (fallback: nomi fisici).
        """
        try:
            src = self._channel_names or self._ai_channels
            return self._unique_tdms_names(list(src))
        except Exception:
            # fallback estremo: nomi fisici così come sono
            return list(self._ai_channels)
