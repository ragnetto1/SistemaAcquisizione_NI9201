# acquisition.py
import os, math, time, uuid, queue, threading, tempfile, datetime
from typing import List, Callable, Optional, Dict, Any
import numpy as np

# --- NI-DAQmx ---
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

# --- TDMS ---
from nptdms import TdmsWriter, ChannelObject, RootObject, GroupObject


def _align_up(value: int, base: int) -> int:
    if base <= 0:
        return value
    return int(math.ceil(value / float(base)) * base)


class AcquisitionManager:
    """
    Core di acquisizione NI-9201 con:
      • avvio automatico quando ci sono canali abilitati
      • stream continuo con callback EveryN campioni
      • writer TDMS a rotazione (default 60 s) con canale Time
      • salvataggio sicuro del segmento parziale allo STOP
    """

    def __init__(self, sample_rate=10000.0, callback_chunk=1000, rotate_seconds=60):
        self.sample_rate = float(sample_rate)
        self.callback_chunk = int(callback_chunk)
        self.rotate_seconds = int(rotate_seconds)

        self.current_rate_hz: Optional[float] = None
        self.current_agg_rate_hz: Optional[float] = None
        self.max_single_rate_hz: Optional[float] = None
        self.max_multi_rate_hz: Optional[float] = None

        self._task = None
        self._reader: Optional[AnalogMultiChannelReader] = None
        self._running = False

        self._queue: "queue.Queue[tuple[int,np.ndarray]]" = queue.Queue(maxsize=2000)
        self._writer_thread: Optional[threading.Thread] = None
        self._writer_stop = threading.Event()

        # cartella di lavoro (sostituita dalla UI quando parte il salvataggio)
        self.temp_dir = os.path.join(tempfile.gettempdir(), f"ni9201_acq_{uuid.uuid4().hex}")
        os.makedirs(self.temp_dir, exist_ok=True)

        # zero / mappe
        self._zero: Dict[str, Optional[float]] = {}
        self._ai_channels: List[str] = []
        self._channel_names: List[str] = []

        self._last_raw: Dict[str, Optional[float]] = {f"ai{i}": None for i in range(8)}
        self._sensor_map_by_phys: Dict[str, Dict[str, Any]] = {}

        # registrazione TDMS
        self._recording_enabled = False
        self._recording_toggle = threading.Event()

        # callback UI
        self.on_channel_value: Optional[Callable[[str, float], None]] = None
        self.on_new_instant_block: Optional[Callable[[np.ndarray, List[np.ndarray], List[str]], None]] = None
        self.on_new_chart_points: Optional[Callable[[np.ndarray, List[np.ndarray], List[str]], None]] = None

        # decimazione grafico concatenato
        self._chart_decim = 10

    # -------------------- API esposte alla UI --------------------
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
        self._zero[chan_name] = None  # al prossimo valore memorizza zero

    def get_last_value(self, chan_name: str, apply_zero: bool = False) -> Optional[float]:
        val = self._last_raw.get(chan_name)
        if val is None:
            return None
        if apply_zero and chan_name in self._zero and self._zero[chan_name] is not None:
            return abs(val - self._zero[chan_name])
        return val

    # -------------------- Scoperta e limiti modulo --------------------
    def list_ni9201_devices(self) -> List[str]:
        if System is None:
            return []
        out = []
        try:
            for dev in System.local().devices:
                pt = (getattr(dev, "product_type", "") or "").upper()
                if "9201" in pt:
                    out.append(dev.name)
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
            # fallback conservativo
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

        try:
            per_chan = self._compute_per_channel_rate(device_name, len(self._ai_channels))
            self.current_rate_hz = per_chan
            self.current_agg_rate_hz = per_chan * max(1, len(self._ai_channels))

            # callback ogni ~10 ms (allineato a multipli di 16)
            target_cb_ms = 10.0
            raw_chunk = max(200, int(per_chan * target_cb_ms / 1000.0))
            self.callback_chunk = _align_up(raw_chunk, 16)

            # buffer driver capiente (evita -200279)
            daq_buf_seconds = 15.0
            desired = int(per_chan * daq_buf_seconds)
            daq_buf_samps = _align_up(max(desired, self.callback_chunk * 100), self.callback_chunk)

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

            # writer
            self._writer_stop.clear()
            self._writer_thread = threading.Thread(target=self._writer_loop, daemon=True)
            self._writer_thread.start()

            self._running = True
            self._task.start()

            # decimazione per chart
            self._chart_decim = max(1, int(self.current_rate_hz // 50))
            return True

        except Exception as e:
            print("Errore start:", e)
            self._cleanup()
            return False

    def stop(self):
        self._running = False
        self.set_recording(False)
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
        self._writer_stop.set()
        self._recording_toggle.set()
        if self._writer_thread and self._writer_thread.is_alive():
            self._writer_thread.join(timeout=10)
        self._writer_thread = None

    # -------------------- Callback DAQ --------------------
    def _on_every_n_samples(self, task_handle, every_n_samples_event_type, number_of_samples, callback_data):
        if not self._running:
            return 0
        try:
            nch = len(self._ai_channels)
            buf = np.empty((nch, number_of_samples), dtype=np.float64)
            self._reader.read_many_sample(buf, number_of_samples, timeout=0.0)
            ts_ns = time.time_ns()

            # cache ultimo valore per canale + callback istantaneo
            for i, ch in enumerate(self._ai_channels):
                raw_val = float(buf[i, -1])
                self._last_raw[ch] = raw_val
                val = raw_val
                if ch in self._zero and self._zero[ch] is None:
                    self._zero[ch] = val  # memorizzo lo zero al primo passaggio
                if ch in self._zero and self._zero[ch] is not None:
                    val = abs(val - self._zero[ch])
                name = self._channel_names[i] if i < len(self._channel_names) else ch
                if self.on_channel_value:
                    self.on_channel_value(name, val)

            # writer queue
            try:
                self._queue.put_nowait((ts_ns, buf))
            except queue.Full:
                self._queue.put((ts_ns, buf), timeout=0.2)

            # feed grafici
            if self.on_new_instant_block or self.on_new_chart_points:
                n = buf.shape[1]
                t0 = ts_ns / 1e9 - n / self.current_rate_hz
                t = np.linspace(t0, t0 + (n - 1) / self.current_rate_hz, n)
                names = self._channel_names or self._ai_channels
                ys = [buf[i, :] for i in range(nch)]
                if self.on_new_instant_block:
                    self.on_new_instant_block(t, ys, names)
                if self.on_new_chart_points:
                    dec = slice(None, None, self._chart_decim)
                    self.on_new_chart_points(t[dec], [y[dec] for y in ys], names)
            return 0
        except Exception as e:
            print("Callback error:", e)
            return 0

    # -------------------- Writer TDMS (rotazione + flush parziale) --------------------
    def _writer_loop(self):
        current_file: Optional[TdmsWriter] = None
        current_start_ns: Optional[int] = None
        last_rotate_ns: Optional[int] = None
        acc: Dict[int, list] = {}

        def open_new_file():
            nonlocal current_file, current_start_ns, last_rotate_ns, acc
            if current_file:
                current_file.close()
            current_start_ns = time.time_ns()
            last_rotate_ns = current_start_ns
            fname = f"segment_{current_start_ns}.tdms"
            path = os.path.join(self.temp_dir, fname)
            acc = {i: [] for i in range(len(self._ai_channels))}
            current_file = TdmsWriter(open(path, "wb"))

        def close_and_flush():
            nonlocal current_file, acc, current_start_ns
            if not current_file:
                return

            # concatena dati
            ch_data = [
                (np.concatenate(acc[i], axis=0) if acc[i] else np.array([], dtype=np.float64))
                for i in range(len(self._ai_channels))
            ]
            n = ch_data[0].size if ch_data and ch_data[0].size else 0

            start_time_s = (current_start_ns or time.time_ns()) / 1e9
            # time relativo al segmento (riparte da 0; nel merge useremo wf_start_time)
            t = (np.arange(n, dtype=np.float64) / float(self.current_rate_hz or 1.0)) if n > 0 else np.array([], dtype=np.float64)

            root = RootObject(properties={
                "sample_rate": float(self.current_rate_hz) if self.current_rate_hz else 0.0,
                "channels": ",".join(self._channel_names or self._ai_channels),
                "start_time_ns": int(current_start_ns or 0)
            })
            group = GroupObject("Acquisition")

            channels = []
            # Time
            channels.append(
                ChannelObject("Acquisition", "Time", t, properties={
                    "unit_string": "s",
                    "wf_start_time": datetime.datetime.fromtimestamp(start_time_s),
                    "wf_increment": 1.0 / float(self.current_rate_hz or 1.0),
                    "stored_domain": "time",
                })
            )
            # Dati (Volt RAW) + meta
            for i, name in enumerate(self._channel_names or self._ai_channels):
                data = ch_data[i] if n > 0 else np.array([], dtype=np.float64)
                phys = self._ai_channels[i] if i < len(self._ai_channels) else f"ai{i}"
                meta = self._sensor_map_by_phys.get(phys, {})
                unit = meta.get("unit", "")
                a = float(meta.get("a", 1.0))
                b = float(meta.get("b", 0.0))
                disp = meta.get("display_label", name)
                props = {
                    "unit": "V",
                    "engineer_unit": unit,
                    "scale_a": a,
                    "scale_b": b,
                    "display_label": disp,
                    "physical_channel": phys,
                    "stored_domain": "Volt",
                    "wf_start_time": datetime.datetime.fromtimestamp(start_time_s),
                    "wf_increment": 1.0 / float(self.current_rate_hz or 1.0),
                }
                channels.append(ChannelObject("Acquisition", name, data, properties=props))

            current_file.write_segment([root, group] + channels)
            current_file.close()
            current_file = None
            acc = {}

        try:
            while not self._writer_stop.is_set():
                # Non in registrazione → dreno eventuali dati residui, salvo e chiudo
                if not self._recording_enabled:
                    drained = False
                    while True:
                        try:
                            _, buf = self._queue.get_nowait()
                            if current_file is None:
                                open_new_file()
                            for i in range(buf.shape[0]):
                                acc[i].append(np.ascontiguousarray(buf[i]))
                            drained = True
                        except queue.Empty:
                            break
                    if current_file:
                        # se ho raccolto qualcosa o anche nulla, chiudo il segmento parziale
                        close_and_flush()
                    # attendo finché non cambia stato
                    self._recording_toggle.wait(timeout=0.2)
                    self._recording_toggle.clear()
                    continue

                # Registrazione attiva
                if current_file is None:
                    open_new_file()

                try:
                    _, buf = self._queue.get(timeout=0.2)
                except queue.Empty:
                    # rotate time-based
                    if last_rotate_ns is not None and (time.time_ns() - last_rotate_ns > self.rotate_seconds * 1e9):
                        close_and_flush()
                        open_new_file()
                    self._recording_toggle.wait(timeout=0.05)
                    self._recording_toggle.clear()
                    continue

                # accodo blocco
                for i in range(buf.shape[0]):
                    acc[i].append(np.ascontiguousarray(buf[i]))

                # rotazione a tempo
                now_ns = time.time_ns()
                if last_rotate_ns is not None and (now_ns - last_rotate_ns > self.rotate_seconds * 1e9):
                    close_and_flush()
                    open_new_file()

            # uscita thread: flush finale (anche se recording era off)
            if current_file:
                while True:
                    try:
                        _, buf = self._queue.get_nowait()
                        for i in range(buf.shape[0]):
                            acc[i].append(np.ascontiguousarray(buf[i]))
                    except queue.Empty:
                        break
                close_and_flush()

        except Exception as e:
            print("Writer error:", e)
            try:
                if current_file:
                    current_file.close()
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
    def stop_graceful(self, wait_ms: int = 150):
        """
        Ferma l'acquisizione garantendo il salvataggio fino all'istante di Stop:
        - lascia arrivare gli ultimi callback
        - legge sincronicamente TUTTI i campioni residui nel buffer NI-DAQmx
        - mette in coda e forza il flush del writer
        - poi chiude il task e il writer thread
        """
        if self._task is None:
            # niente da fare: chiusura standard writer
            self._running = False
            self.set_recording(False)
            self._writer_stop.set()
            self._recording_toggle.set()
            if self._writer_thread and self._writer_thread.is_alive():
                self._writer_thread.join(timeout=10)
            self._writer_thread = None
            return

        try:
            # Assicurati che il writer stia registrando per catturare il residuo
            self.set_recording(True)

            # 1) piccolo wait per far arrivare eventuali callback in volo
            t0 = time.time()
            while (time.time() - t0) * 1000.0 < wait_ms:
                time.sleep(0.005)

            # 2) leggi tutto il residuo dal buffer hardware
            try:
                avail = int(self._task.in_stream.avail_samp_per_chan)
            except Exception:
                avail = 0
            while avail and avail > 0:
                nch = len(self._ai_channels)
                buf = np.empty((nch, avail), dtype=np.float64)
                # lettura bloccante con timeout breve
                self._reader.read_many_sample(buf, avail, timeout=1.0)
                ts_ns = time.time_ns()
                try:
                    self._queue.put_nowait((ts_ns, buf))
                except queue.Full:
                    self._queue.put((ts_ns, buf), timeout=0.5)
                try:
                    avail = int(self._task.in_stream.avail_samp_per_chan)
                except Exception:
                    break

            # 3) disattiva registrazione → il writer drena e chiude il segmento parziale
            self.set_recording(False)
            self._recording_toggle.set()

        finally:
            # 4) ferma il task
            try:
                self._running = False
                self._task.stop()
            except Exception:
                pass
            try:
                self._task.close()
            except Exception:
                pass
            self._task = None

            # 5) chiudi il writer thread (ha già flushato)
            self._writer_stop.set()
            self._recording_toggle.set()
            if self._writer_thread and self._writer_thread.is_alive():
                self._writer_thread.join(timeout=10)
            self._writer_thread = None

