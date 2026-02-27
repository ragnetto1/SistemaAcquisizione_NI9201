# acquisition.py
import os, math, time, uuid, queue, threading, tempfile, datetime
from typing import List, Callable, Optional, Dict, Any, Tuple
import numpy as np

from calculated_channels_engine import CalculatedChannelsEngine

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

        # User-defined per-channel sampling rate (Hz). When set to a positive value,
        # it overrides the automatic maximum rate computed from the device and
        # number of channels. If None, the automatic maximum is used.
        self._user_rate_hz: Optional[float] = None
        self._sensor_map_by_phys: Dict[str, Dict[str, Any]] = {}
        self._calc_rows: List[Dict[str, Any]] = []
        self._calc_compile_errors: Dict[str, str] = {}
        self._calc_engine = CalculatedChannelsEngine(max_channels=30)

        # Registrazione TDMS
        self._recording_enabled = False
        self._recording_toggle = threading.Event()

        # --- Memory-based saving attributes ---
        # Maximum memory allowed for accumulating blocks before flushing to disk
        self._memory_limit_bytes: int = 500 * 1024 * 1024  # 500 MB
        # List of tuples (global_start_index, numpy_array) representing blocks in memory
        self._memory_blocks: List[Tuple[int, np.ndarray]] = []
        # Current memory usage in bytes for accumulated blocks
        self._memory_bytes: int = 0
        # Counter used to increment output filenames (00001, 00002, ...)
        self._file_counter: int = 0
        # Base filename (without extension) used when saving TDMS segments
        self._base_filename_no_ext: str = "Seg"

        # Callback UI
        self.on_channel_value: Optional[Callable[[str, float], None]] = None
        self.on_new_instant_block: Optional[Callable[[np.ndarray, List[np.ndarray], List[str]], None]] = None
        self.on_new_chart_points: Optional[Callable[[np.ndarray, List[np.ndarray], List[str]], None]] = None

        # Decimazione grafico concatenato
        self._chart_decim = 10

        # Temporalizzazione sample-accurate
        self._t0_epoch_s: Optional[float] = None  # tempo assoluto del campione #0
        self._global_samples: int = 0             # contatore globale campioni per canale
        # Sync-only timing controls (used by chassis synchronized mode).
        self._sync_anchor_epoch_s: Optional[float] = None
        self._sync_write_start_index: int = 0

        # Size in bytes of a single block of samples pushed to the writer queue. This
        # value is computed when the acquisition task starts. It is used to
        # estimate the backlog queued for disk in get_backlog_estimate().
        self._block_bytes: int = 0

    # -------------------- API verso la UI --------------------
    def set_output_directory(self, path: str):
        if not path:
            return
        self.temp_dir = os.path.abspath(path)
        os.makedirs(self.temp_dir, exist_ok=True)

    def set_sensor_map(self, sensor_map_by_phys: Dict[str, Dict[str, Any]]):
        self._sensor_map_by_phys = dict(sensor_map_by_phys or {})

    def set_calculated_channels(self, rows: List[Dict[str, Any]]) -> Dict[str, str]:
        norm_rows: List[Dict[str, Any]] = []
        formula_map: Dict[str, str] = {}
        for row in list(rows or [])[:30]:
            try:
                cc = str(row.get("channel_id", "") or "").strip()
            except Exception:
                cc = ""
            if not cc.startswith("cc"):
                continue
            formula = str(row.get("formula", "") or "").strip()
            name = str(row.get("name", cc) or cc).strip() or cc
            try:
                zero = row.get("zero", None)
                zero = float(zero) if zero is not None else None
            except Exception:
                zero = None
            norm_rows.append(
                {
                    "channel_id": cc,
                    "formula": formula,
                    "enabled": bool(row.get("enabled", False)),
                    "plot_enabled": bool(row.get("plot_enabled", False)),
                    "name": name,
                    "zero": zero,
                }
            )
            formula_map[cc] = formula
        self._calc_compile_errors = self._calc_engine.configure(formula_map)
        for row in norm_rows:
            cc = row.get("channel_id", "")
            if cc in self._calc_compile_errors:
                row["enabled"] = False
        try:
            enabled_ids = [
                str(r.get("channel_id", "") or "").strip()
                for r in norm_rows
                if bool(r.get("enabled", False)) and str(r.get("formula", "") or "").strip()
            ]
            self._calc_engine.set_enabled_channels(enabled_ids)
        except Exception:
            pass
        self._calc_rows = norm_rows
        return dict(self._calc_compile_errors)

    @property
    def recording_enabled(self) -> bool:
        return self._recording_enabled

    def set_recording(self, enable: bool):
        prev = self._recording_enabled
        self._recording_enabled = bool(enable)
        if prev != self._recording_enabled:
            self._recording_toggle.set()

    def set_sync_anchor_epoch_s(self, epoch_s: Optional[float]) -> None:
        if epoch_s is None:
            self._sync_anchor_epoch_s = None
            return
        try:
            self._sync_anchor_epoch_s = float(epoch_s)
        except Exception:
            self._sync_anchor_epoch_s = None

    def set_sync_write_start_index(self, start_index: int) -> None:
        try:
            self._sync_write_start_index = max(0, int(start_index))
        except Exception:
            self._sync_write_start_index = 0

    # -------------------- Filename and memory API --------------------
    def set_base_filename(self, base_name: str):
        """
        Set the base filename (without extension) used for naming TDMS segments.
        When called, the internal file counter is reset so numbering restarts
        from 00001.
        """
        if base_name:
            # Remove any extension and keep only the basename
            bn = os.path.splitext(os.path.basename(base_name))[0]
            if bn:
                self._base_filename_no_ext = bn
                self._file_counter = 0

    def get_memory_usage(self) -> Tuple[int, int]:
        """
        Returns a tuple (used_bytes, limit_bytes) representing the current
        accumulated memory and the configured threshold. The UI can use
        this information to display progress.
        """
        return (self._memory_bytes, self._memory_limit_bytes)

    def get_backlog_estimate(self) -> float:
        """
        Estimate the size of pending samples waiting to be written to disk.

        This method computes an approximate backlog based on the current
        writer queue size and the size of a single block. It returns the
        estimated backlog in megabytes (MB). If the block size is unknown or
        the queue size cannot be determined, it returns 0.0.

        Returns
        -------
        float
            Estimated backlog in megabytes.
        """
        try:
            q = self._queue
            block_bytes = int(self._block_bytes or 0)
            # The queue may be unbounded; qsize gives an estimate of items
            queued_blocks = int(getattr(q, "qsize", lambda: 0)())
            backlog_bytes = queued_blocks * block_bytes
            # Include any in‑memory buffer that has not yet been flushed
            backlog_bytes += int(self._memory_bytes or 0)
            return backlog_bytes / float(1024 * 1024)
        except Exception:
            return 0.0

    def set_memory_limit_bytes(self, value: int) -> None:
        """
        Set the maximum allowed memory (in bytes) for accumulating blocks in RAM.
        This value controls when the writer will flush the in-memory buffer to
        disk. It must be a positive integer.

        Args:
            value: The desired memory limit in bytes. Values less than or
                equal to zero are ignored.
        """
        try:
            v = int(value)
        except Exception:
            return
        if v > 0:
            self._memory_limit_bytes = v

    def set_memory_limit_mb(self, value_mb: float) -> None:
        """
        Convenience method to set the memory limit in megabytes.

        Args:
            value_mb: The desired memory limit in megabytes (MB). Must be >0.
        """
        try:
            mb_val = float(value_mb)
        except Exception:
            return
        if mb_val > 0:
            self._memory_limit_bytes = int(mb_val * 1024 * 1024)

    def clear_memory_buffer(self) -> None:
        """
        Clears any accumulated blocks and resets the memory usage counter.

        This should be invoked before starting a new recording session to
        ensure that no leftover samples from a previous session are flushed
        to disk. It does not affect the underlying acquisition queue.
        """
        try:
            # Empty the list of blocks
            self._memory_blocks.clear()
        except Exception:
            # Fall back to assignment if clear is not available
            self._memory_blocks = []
        # Reset the byte counter
        self._memory_bytes = 0

    # -------------------- User sample rate API --------------------
    def set_user_rate_hz(self, rate: Optional[float]) -> None:
        """
        Set a user-defined per-channel sampling rate (in Hz). When a positive
        number is provided, the acquisition will use the smaller between this
        rate and the maximum hardware rate per channel. If `rate` is None or
        not a positive number, the automatic maximum rate will be used.

        Parameters
        ----------
        rate : float or None
            Desired per-channel sampling rate in samples per second. Use
            `None` or any non-positive value to revert to automatic maximum.
        """
        if rate is None:
            self._user_rate_hz = None
            return
        try:
            r = float(rate)
            if r > 0:
                self._user_rate_hz = r
            else:
                self._user_rate_hz = None
        except Exception:
            self._user_rate_hz = None

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
    def start(
        self,
        device_name: str,
        ai_channels: List[str],
        channel_names: List[str],
        sync_start_cfg: Optional[Dict[str, Any]] = None,
    ) -> bool:
        if nidaqmx is None:
            return False
        if self._running:
            return True

        self._ai_channels = ai_channels[:]
        self._channel_names = channel_names[:]
        self._start_channel_names = channel_names[:]

        try:
            # --- rate per-canale (rispetta i limiti del dispositivo e canali) ---
            # Determine the maximum rate per channel for the given device and channel count
            per_chan_max = self._compute_per_channel_rate(device_name, len(self._ai_channels))
            # Use a user-defined rate if provided and positive, clamped to the maximum
            per_chan = per_chan_max
            try:
                if self._user_rate_hz is not None:
                    r = float(self._user_rate_hz)
                    if r > 0:
                        per_chan = min(per_chan_max, r)
            except Exception:
                pass
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
            # Determine how many bytes each block occupies. Each block has shape
            # (n_channels, callback_chunk) and is stored as float64 values (8 bytes per sample).
            bytes_per_block = nch * self.callback_chunk * 8  # float64

            # Persist the block size for backlog monitoring. This value will be
            # used by get_backlog_estimate() to estimate the amount of data
            # currently waiting to be flushed to disk.
            try:
                self._block_bytes = int(bytes_per_block)
            except Exception:
                self._block_bytes = 0
            queue_target_seconds = 30
            blocks_target = max(50, int(per_chan * queue_target_seconds / self.callback_chunk))
            MEMORY_BUDGET_MB = 256
            blocks_mem = max(50, int((MEMORY_BUDGET_MB * 1024 * 1024) / max(1, bytes_per_block)))
            queue_capacity = min(blocks_target, blocks_mem)
            # Use an unbounded queue to avoid dropping data while accumulating in memory
            self._queue = queue.Queue(maxsize=0)

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

            # Optional hardware start synchronization across modules in the same chassis.
            sync_cfg = dict(sync_start_cfg or {})
            sync_mode = str(sync_cfg.get("sync_mode", "") or "").strip().lower()
            sync_role = str(sync_cfg.get("sync_role", "") or "").strip().lower()
            trig_src = str(sync_cfg.get("start_trigger_source", "") or "").strip()
            if sync_mode == "hardware" and sync_role == "slave":
                if not trig_src:
                    raise RuntimeError("Trigger source hardware non valido.")
                self._task.triggers.start_trigger.cfg_dig_edge_start_trig(
                    trigger_source=trig_src,
                    trigger_edge=nidaqmx.constants.Edge.RISING,
                )

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
        """Stop immediato robusto anche in fase di chiusura forzata UI."""
        self._closing = True
        try:
            self._running = False
            self.set_recording(False)
            self._unregister_callbacks()

            try:
                if self._task:
                    self._task.stop()
            except BaseException:
                pass
            try:
                if self._task:
                    self._task.close()
            except BaseException:
                pass
            self._task = None
        finally:
            # chiusura writer sempre garantita
            try:
                self._writer_stop.set()
                self._recording_toggle.set()
            except BaseException:
                pass
            try:
                if self._writer_thread and self._writer_thread.is_alive():
                    self._writer_thread.join(timeout=2.0)
            except BaseException:
                pass
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
                if self._sync_anchor_epoch_s is not None:
                    self._t0_epoch_s = float(self._sync_anchor_epoch_s)
                else:
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
            # Apply zero offsets to each channel before sending data to the UI
            if self.on_new_instant_block or self.on_new_chart_points:
                fs = float(self.current_rate_hz or 1.0)
                t0 = (self._t0_epoch_s or 0.0) + (start_idx / fs)
                # generate time vector for this block
                t = t0 + np.arange(number_of_samples, dtype=np.float64) / fs
                # build list of per-channel data arrays applying zero offset
                ys_corr: List[np.ndarray] = []
                for i, ch in enumerate(self._ai_channels):
                    try:
                        data = buf[i, :]
                        baseline = self._zero.get(ch, None)
                        if baseline is not None:
                            data = data - float(baseline)
                        # ensure contiguous array for PyQtGraph
                        ys_corr.append(np.ascontiguousarray(data))
                    except Exception:
                        ys_corr.append(np.ascontiguousarray(buf[i, :]))

                if self.on_new_instant_block:
                    try:
                        self.on_new_instant_block(t, ys_corr, start_names)
                    except Exception as e:
                        print("Callback warning (instant_block):", e)

                if self.on_new_chart_points:
                    try:
                        dec_step = int(self._chart_decim or 1)
                        if dec_step <= 0:
                            dec_step = 1
                        dec = slice(None, None, dec_step)
                        t_dec = t[dec]
                        ys_dec = [y[dec] for y in ys_corr]
                        self.on_new_chart_points(t_dec, ys_dec, start_names)
                    except Exception as e:
                        print("Callback warning (chart_points):", e)

            return 0
        except Exception as e:
            print("Callback error:", e)
            return 0

    # -------------------- Writer TDMS (streaming, no buchi) --------------------
    def _writer_loop(self):
        """
        Writer thread that accumulates incoming blocks in memory until a
        configurable limit (default 500 MB). Once the limit is reached or
        recording is stopped, the accumulated blocks are flushed to a new
        TDMS file. This approach guarantees that no samples are lost while
        providing larger segment files instead of the time‑based rotation.
        """
        # Sample rate for time calculations
        fs = float(self.current_rate_hz or 1.0)

        # Helper to flush accumulated blocks to disk
        def flush_memory():
            """
            Writes all accumulated blocks to a new TDMS file and clears the
            in‑memory buffer. Blocks are sorted by their global start index
            to maintain chronological order. Each block is written as a
            mini‑segment with appropriate metadata. If the output directory
            has been removed (e.g. after merging) or is unset, no file is
            written and the accumulated blocks are simply discarded.
            """
            nonlocal fs
            # Nothing to flush
            if not self._memory_blocks:
                return
            try:
                # If temp_dir is not set or no longer exists, discard accumulated data
                if not self.temp_dir or not os.path.isdir(self.temp_dir):
                    # Clear memory without writing
                    self._memory_blocks.clear()
                    self._memory_bytes = 0
                    return
                # Sort blocks by global start index
                blocks_sorted = sorted(self._memory_blocks, key=lambda x: x[0])
                seg_start_idx = blocks_sorted[0][0]
                # Determine absolute start time for the earliest sample
                t0_epoch = float(self._t0_epoch_s or time.time())
                start_time_epoch_s = t0_epoch + (seg_start_idx / fs)
                # Determine filename; reset counter if negative
                self._file_counter += 1
                base = self._base_filename_no_ext or "segment"
                fname = f"{base}_{self._file_counter:05d}.tdms"
                out_path = os.path.join(self.temp_dir, fname)
                # Ensure the output directory exists
                try:
                    os.makedirs(self.temp_dir, exist_ok=True)
                except Exception:
                    pass
                # Write to a temporary file first to ensure atomicity. Only once
                # the file has been completely written do we rename it to the
                # final filename. This avoids leaving behind a partially written
                # TDMS file in case of interruption.
                tmp_path = out_path + ".tmp"
                # Ensure no stale tmp file remains
                try:
                    if os.path.exists(tmp_path):
                        os.remove(tmp_path)
                except Exception:
                    pass
                with TdmsWriter(open(tmp_path, "wb")) as writer:
                    # Precompute the sanitized TDMS names once per flush
                    try:
                        tdms_names = list(self._current_tdms_names())
                    except Exception:
                        tdms_names = list(self._ai_channels)
                    # Extend names if there are more channels than names
                    try:
                        if len(tdms_names) < blocks_sorted[0][1].shape[0]:
                            used = set(["Time"]) | set(tdms_names)
                            for i in range(len(tdms_names), blocks_sorted[0][1].shape[0]):
                                base_nm = self._sanitize_tdms_basename(
                                    self._ai_channels[i] if i < len(self._ai_channels) else f"ai{i}"
                                )
                                name = base_nm
                                k = 2
                                while name in used:
                                    name = f"{base_nm}_{k}"
                                    k += 1
                                tdms_names.append(name)
                                used.add(name)
                    except Exception:
                        pass
                    calc_rows_enabled: List[Dict[str, Any]] = []
                    calc_tdms_name_by_cc: Dict[str, str] = {}
                    all_data_channel_names = list(tdms_names)
                    try:
                        calc_rows_enabled = [
                            dict(r) for r in list(self._calc_rows or [])
                            if bool(r.get("enabled", False))
                        ]
                        if calc_rows_enabled:
                            raw_calc_names = [
                                str(r.get("name", r.get("channel_id", "calculated")) or r.get("channel_id", "calculated"))
                                for r in calc_rows_enabled
                            ]
                            combined = self._unique_tdms_names(all_data_channel_names + raw_calc_names)
                            calc_names = combined[len(all_data_channel_names):]
                            all_data_channel_names = combined
                            for row, nm in zip(calc_rows_enabled, calc_names):
                                calc_tdms_name_by_cc[str(row.get("channel_id", ""))] = str(nm)
                    except Exception:
                        calc_rows_enabled = []
                        calc_tdms_name_by_cc = {}
                        all_data_channel_names = list(tdms_names)
                    # Precompute ISO timestamp for the segment
                    seg_iso = datetime.datetime.fromtimestamp(start_time_epoch_s).isoformat()
                    # Loop through blocks and write them
                    for (blk_start_idx, buf) in blocks_sorted:
                        # Compute starting offset within this file
                        try:
                            start_in_file = int(blk_start_idx - seg_start_idx)
                        except Exception:
                            start_in_file = 0
                        # Validate block shape
                        try:
                            n = int(buf.shape[1])
                        except Exception:
                            continue
                        if n <= 0:
                            continue
                        # Compute relative time vector for this mini‑segment
                        try:
                            t_rel = (start_in_file / fs) + (np.arange(n, dtype=np.float64) / fs)
                        except Exception:
                            continue
                        # Root and group objects with wf_* properties
                        try:
                            sync_anchor = float(self._sync_anchor_epoch_s) if self._sync_anchor_epoch_s is not None else float(start_time_epoch_s)
                        except Exception:
                            sync_anchor = float(start_time_epoch_s)
                        try:
                            sync_cutoff = int(self._sync_write_start_index or 0)
                        except Exception:
                            sync_cutoff = 0
                        try:
                            root = RootObject(properties={
                                "sample_rate": fs,
                                "channels": ",".join(all_data_channel_names),
                                "start_index": int(seg_start_idx),
                                "chunk_offset": int(start_in_file),
                                "start_time_epoch_s": float(start_time_epoch_s),
                                "segment_start_time_iso": seg_iso,
                                "sync_anchor_epoch_s": float(sync_anchor),
                                "sync_write_cutoff_index": int(sync_cutoff),
                                # Provide waveform metadata at root level as well
                                "wf_start_time": datetime.datetime.fromtimestamp(start_time_epoch_s),
                                "wf_increment": 1.0 / fs,
                            })
                            group = GroupObject("Acquisition")
                        except Exception:
                            continue
                        # Channels: build Time channel
                        channels = []
                        try:
                            # Include descriptive metadata for the time channel as well.  The
                            # NI TDMS viewer shows the capitalised "Description" and "Unit"
                            # fields in the base properties.  Adding them here makes the
                            # time channel's metadata explicit.  We also keep the lowercase
                            # variant and waveform parameters for completeness.
                            time_props = {
                                "Description": "Time",
                                "description": "Time",
                                "Unit": "s",
                                "unit_string": "s",
                                "wf_start_time": datetime.datetime.fromtimestamp(start_time_epoch_s),
                                "wf_increment": 1.0 / fs,
                                "stored_domain": "time",
                            }
                            channels.append(ChannelObject(
                                "Acquisition", "Time", t_rel, properties=time_props
                            ))
                        except Exception:
                            pass
                        # Data channels
                        try:
                            num_ch = min(len(tdms_names), buf.shape[0])
                            phys_data_eng_by_name: Dict[str, np.ndarray] = {}
                            for i in range(num_ch):
                                ui_name = tdms_names[i]
                                try:
                                    phys = self._ai_channels[i] if i < len(self._ai_channels) else f"ai{i}"
                                    meta = self._sensor_map_by_phys.get(phys, {})
                                    sensor_name = meta.get("sensor_name", "Voltage")
                                    unit_eng = meta.get("unit", "") if sensor_name != "Voltage" else "V"
                                    # Calibration coefficients
                                    a = self._to_float(meta.get("a", 1.0), 1.0)
                                    b = self._to_float(meta.get("b", 0.0), 0.0)
                                    # Apply zero offset
                                    raw = np.ascontiguousarray(buf[i])  # volts
                                    baseline = self._zero.get(phys, None)
                                    zero_eng = 0.0
                                    if baseline is not None:
                                        try:
                                            raw = raw - float(baseline)
                                            zero_eng = a * float(baseline) + b
                                        except Exception:
                                            zero_eng = 0.0
                                    # Convert to engineered units
                                    data_eng = a * raw + b
                                    # Properties for this channel. Use capitalized keys
                                    # for Description and Unit so they appear in the base
                                    # properties of NI viewers. Keep the lowercase keys
                                    # for compatibility with other tools.
                                    props = {
                                        "Description": sensor_name,
                                        "description": sensor_name,
                                        "Unit": unit_eng,
                                        "unit_string": unit_eng,
                                        "wf_start_time": datetime.datetime.fromtimestamp(start_time_epoch_s),
                                        "wf_increment": 1.0 / fs,
                                        "physical_channel": phys,
                                        "scale_a": a,
                                        "scale_b": b,
                                        "zero_applied": float(zero_eng),
                                    }
                                    channels.append(ChannelObject("Acquisition", ui_name, data_eng, properties=props))
                                    phys_data_eng_by_name[phys] = np.asarray(data_eng, dtype=np.float64)
                                except Exception as e:
                                    # Skip problematic channel but continue writing others
                                    print(f"Writer warning (data channel {i}):", e)
                            if calc_rows_enabled:
                                try:
                                    calc_out, calc_err = self._calc_engine.evaluate(phys_data_eng_by_name, fs, fill_value=0.0)
                                except Exception as e:
                                    calc_out, calc_err = {}, {"__all__": str(e)}
                                for row in calc_rows_enabled:
                                    cc = str(row.get("channel_id", "") or "").strip()
                                    if not cc:
                                        continue
                                    calc_name = calc_tdms_name_by_cc.get(cc, cc)
                                    arr = calc_out.get(cc)
                                    if not isinstance(arr, np.ndarray):
                                        arr = np.zeros(n, dtype=np.float64)
                                    else:
                                        arr = np.asarray(arr, dtype=np.float64).reshape(-1)
                                        if arr.size > n:
                                            arr = arr[:n]
                                        elif arr.size < n and arr.size > 0:
                                            arr = np.pad(arr, (0, n - arr.size), mode="edge")
                                        elif arr.size <= 0:
                                            arr = np.zeros(n, dtype=np.float64)
                                    z = row.get("zero", None)
                                    if z is not None:
                                        try:
                                            arr = arr - float(z)
                                        except Exception:
                                            pass
                                    props = {
                                        "Description": "Calculated channel",
                                        "description": "Calculated channel",
                                        "Unit": "",
                                        "unit_string": "",
                                        "wf_start_time": datetime.datetime.fromtimestamp(start_time_epoch_s),
                                        "wf_increment": 1.0 / fs,
                                        "calculated_channel_id": cc,
                                        "formula": str(row.get("formula", "") or ""),
                                        "runtime_error": str(calc_err.get(cc, "") or ""),
                                    }
                                    channels.append(
                                        ChannelObject("Acquisition", calc_name, np.ascontiguousarray(arr, dtype=np.float64), properties=props)
                                    )
                        except Exception as e:
                            print("Writer error (data channels build):", e)
                        # Write the mini‑segment
                        try:
                            writer.write_segment([root, group] + channels)
                        except Exception as e:
                            print("Writer error (write_segment):", e)
                # Clear memory after writing
                self._memory_blocks.clear()
                self._memory_bytes = 0
                # Atomically rename the temporary file to its final name
                try:
                    os.replace(tmp_path, out_path)
                except Exception as e:
                    # If rename fails, attempt to clean up and report
                    try:
                        if os.path.exists(tmp_path):
                            os.remove(tmp_path)
                    except Exception:
                        pass
                    print("Writer error (atomic rename):", e)
            except Exception as e:
                print("Writer flush error:", e)

        try:
            # Main loop: accumulate blocks and flush when needed
            while not self._writer_stop.is_set():
                # If not recording, flush any residual blocks and drain the queue
                if not self._recording_enabled:
                    if self._memory_bytes > 0:
                        flush_memory()
                    # Drain the queue to avoid memory build‑up
                    while True:
                        try:
                            _ = self._queue.get_nowait()
                        except queue.Empty:
                            break
                    # Wait for a recording toggle or short timeout
                    self._recording_toggle.wait(timeout=0.2)
                    self._recording_toggle.clear()
                    continue
                # Sync hold: while waiting for a valid common cutoff (N0), do not
                # consume queue blocks. This preserves pre-cutoff samples so all
                # modules can apply the same cutover index deterministically.
                try:
                    gate_idx = int(self._sync_write_start_index or 0)
                except Exception:
                    gate_idx = 0
                if gate_idx >= 10**11:
                    self._recording_toggle.wait(timeout=0.05)
                    self._recording_toggle.clear()
                    continue
                # Recording active: fetch next block
                try:
                    start_idx, buf = self._queue.get(timeout=0.2)
                except queue.Empty:
                    # No block available: check again soon
                    self._recording_toggle.wait(timeout=0.05)
                    self._recording_toggle.clear()
                    continue
                # Apply sync write gate by sample index (N0 common cutover).
                if gate_idx > 0:
                    try:
                        n_samp = int(buf.shape[1])
                    except Exception:
                        n_samp = 0
                    end_idx = int(start_idx + max(0, n_samp))
                    if end_idx <= gate_idx:
                        continue
                    if start_idx < gate_idx and n_samp > 0:
                        cut = int(gate_idx - start_idx)
                        if cut >= n_samp:
                            continue
                        try:
                            buf = np.ascontiguousarray(buf[:, cut:])
                        except Exception:
                            continue
                        start_idx = gate_idx
                # Accumulate this block into memory
                try:
                    self._memory_blocks.append((start_idx, buf))
                    # buf.nbytes is total bytes (all channels)
                    self._memory_bytes += int(buf.nbytes)
                except Exception:
                    pass
                # Flush if memory limit reached or exceeded
                if self._memory_bytes >= self._memory_limit_bytes:
                    flush_memory()
            # On exit: drain any remaining blocks from the queue into memory
            try:
                while True:
                    try:
                        start_idx, buf = self._queue.get_nowait()
                        self._memory_blocks.append((start_idx, buf))
                        self._memory_bytes += int(buf.nbytes)
                    except queue.Empty:
                        break
            except Exception:
                pass
            # Final flush to disk for any residual data
            if self._memory_bytes > 0:
                flush_memory()
        except Exception as e:
            print("Writer error:", e)

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
