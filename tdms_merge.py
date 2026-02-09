import os
import datetime
import numpy as np
from nptdms import TdmsFile, TdmsWriter, RootObject, GroupObject, ChannelObject
from typing import Optional, Callable


def _to_py_datetime(x):
    """Converte datetime-like (anche numpy.datetime64) in datetime.datetime naive (locale)."""
    if isinstance(x, datetime.datetime):
        return x
    try:
        if isinstance(x, np.datetime64):
            # converti a ns dal 1970-01-01, poi a datetime locale
            ns = int((x - np.datetime64("1970-01-01T00:00:00")).astype("timedelta64[ns]").astype("int64"))
            return datetime.datetime.fromtimestamp(ns / 1e9)
    except Exception:
        pass
    return None


class TdmsMerger:
    """
    Unisce i segmenti .tdms di una cartella nell'ordine cronologico.

    Risultato:
      - Canali dati salvati come WAVEFORM continue sull'intera prova
        (wf_start_time = inizio prova; wf_increment = 1/fs)
      - Canale "Time" CONTINUO sull'intera prova (secondi dall'inizio prova)

    Comportamento robusto:
      - Se un canale manca in qualche segmento, viene ignorato per quel segmento
      - Se alcuni segmenti non hanno il canale "Time", si ricava N dai canali dati
      - t0_first e fs sono ricavati dal primo segmento che li dichiara (via wf_*)
      - Se fs manca ovunque, fallback a 1.0 Hz (evita crash)
    """

    # -------------------- utilità interne --------------------
    def _pick_group(self, td: TdmsFile):
        """Preferisce il gruppo 'Acquisition', altrimenti il primo disponibile."""
        try:
            if "Acquisition" in td.groups():
                return td["Acquisition"]
        except Exception:
            pass
        try:
            groups = list(td.groups())
            if groups:
                return td[groups[0].name]
        except Exception:
            pass
        return None

    def _list_segments(self, folder: str):
        """Ritorna la lista ordinata dei .tdms (non .tdms_index) nella cartella."""
        segs = [
            os.path.join(folder, f)
            for f in os.listdir(folder)
            if f.lower().endswith(".tdms") and not f.lower().endswith(".tdms_index")
        ]
        segs.sort()
        return segs

    # -------------------- API --------------------
    def merge_temp_tdms(self, folder: str, out_path: str, progress_cb: Optional[Callable[[int, int], None]] = None):
        """
        Merge all TDMS segments in ``folder`` into a single TDMS file at
        ``out_path``.

        This implementation streams each source segment into the final file
        sequentially to avoid loading all data into memory at once. It also
        performs a post‑merge validation of the resulting file to ensure
        temporal consistency. If validation fails, no temporary data is
        removed and a ``RuntimeError`` is raised.

        Parameters
        ----------
        folder : str
            Directory containing the temporary TDMS segments to merge.
        out_path : str
            Destination path for the merged TDMS file. A temporary file with
            extension ``.tmp`` is written first and renamed atomically on
            success.
        progress_cb : callable, optional
            Callback function receiving two integers ``(current, total)`` to
            report merge progress. Called after each source segment is
            processed.
        """
        if not os.path.isdir(folder):
            raise RuntimeError(f"Cartella segmenti non trovata: {folder}")

        segs = self._list_segments(folder)
        if not segs:
            raise RuntimeError("Nessun segmento TDMS trovato da unire.")

        total_segs = len(segs)

        # First pass: gather metadata and channel names without loading all data
        ch_names = None
        props_cache = {}
        t0_first = None
        fs = None
        seg_times_iso = []

        for path in segs:
            try:
                td = TdmsFile.read(path)
            except Exception:
                continue
            grp = self._pick_group(td)
            if grp is None:
                continue
            # Determine channel names (excluding Time) once
            if ch_names is None:
                try:
                    ch_names = [c.name for c in grp.channels() if c.name != "Time"]
                except Exception:
                    ch_names = []
                if not ch_names:
                    continue
                for nm in ch_names:
                    props_cache[nm] = {}
            # Extract t0 and dt from Time channel or a data channel
            seg_t0 = None
            seg_dt = None
            if "Time" in grp:
                try:
                    p = grp["Time"].properties
                    seg_t0 = p.get("wf_start_time", None)
                    seg_dt = p.get("wf_increment", None)
                except Exception:
                    pass
            if seg_t0 is None or seg_dt in (None, 0):
                for nm in ch_names:
                    if nm in grp:
                        try:
                            p = grp[nm].properties
                            if seg_t0 is None:
                                seg_t0 = p.get("wf_start_time", seg_t0)
                            if seg_dt in (None, 0):
                                seg_dt = p.get("wf_increment", seg_dt)
                        except Exception:
                            pass
                    if seg_t0 is not None and seg_dt not in (None, 0):
                        break
            # Record global t0 and fs on first appearance
            if t0_first is None and seg_t0 is not None:
                t0_first = _to_py_datetime(seg_t0) or datetime.datetime.now()
            if fs is None and seg_dt not in (None, 0):
                try:
                    fs = 1.0 / float(seg_dt)
                except Exception:
                    pass
            # Capture per‑segment start time in ISO format for metadata
            try:
                if seg_t0 is not None:
                    iso = (_to_py_datetime(seg_t0) or datetime.datetime.now()).isoformat()
                else:
                    iso = datetime.datetime.now().isoformat()
                seg_times_iso.append(iso)
            except Exception:
                seg_times_iso.append(datetime.datetime.now().isoformat())
            # Cache channel properties from the first available occurrence for each channel.
            # We initialise props_cache lazily: when ch_names is first set we do not
            # fill props_cache to avoid blocking subsequent updates.  For each
            # segment, store the channel's properties only if they have not yet
            # been captured (props_cache[nm] is empty or missing).  This ensures
            # that custom properties such as Description, Unit, scale_a,
            # scale_b, zero_applied, etc., are preserved from the first segment
            # containing the channel.
            for nm in ch_names or []:
                try:
                    # Determine if we already have properties for this channel
                    has_props = nm in props_cache and bool(props_cache[nm])
                except Exception:
                    has_props = False
                # If we don't have properties yet and the group contains this channel,
                # capture its properties now.
                if not has_props and nm in grp:
                    try:
                        props_cache[nm] = dict(grp[nm].properties)
                    except Exception:
                        props_cache[nm] = {}

        if ch_names is None:
            raise RuntimeError("Nessun canale valido trovato nei segmenti.")
        if t0_first is None:
            t0_first = datetime.datetime.now()
        if fs is None or fs <= 0:
            fs = 1.0

        # Second pass: write data to temporary output file streaming segment by segment
        os.makedirs(os.path.dirname(out_path) or ".", exist_ok=True)
        tmp_out = out_path + ".tmp"
        # Remove any existing tmp file
        try:
            if os.path.exists(tmp_out):
                os.remove(tmp_out)
        except Exception:
            pass

        cumulative_samples = 0
        # Precompute a joined string of all segment start times for metadata
        seg_times_str = ";".join(seg_times_iso)
        # Current segment index
        seg_index = 0

        with TdmsWriter(open(tmp_out, "wb")) as w:
            for path in segs:
                seg_index += 1
                try:
                    td = TdmsFile.read(path)
                except Exception:
                    continue
                grp = self._pick_group(td)
                if grp is None:
                    continue
                # Determine N samples for this segment
                N = None
                if "Time" in grp:
                    try:
                        N = len(grp["Time"])
                    except Exception:
                        N = None
                if N is None:
                    for nm in ch_names:
                        if nm in grp:
                            try:
                                N = len(grp[nm])
                                break
                            except Exception:
                                pass
                if N is None or N <= 0:
                    if progress_cb:
                        try:
                            progress_cb(seg_index, total_segs)
                        except Exception:
                            pass
                    continue
                # Compute time vector for this segment in seconds from start of test
                dt = 1.0 / float(fs)
                t_rel = (cumulative_samples / float(fs)) + np.arange(N, dtype=np.float64) * dt
                cumulative_samples += N
                # Build root and group objects with metadata
                try:
                    root = RootObject(properties={
                        "created": datetime.datetime.now(),
                        "wf_merged": True,
                        "source_folder": os.path.abspath(folder),
                        "segment_index": seg_index,
                        "segment_start_time_iso": seg_times_iso[seg_index - 1] if seg_index - 1 < len(seg_times_iso) else "",
                        "all_segment_start_times": seg_times_str,
                        # Provide waveform metadata at root level as well
                        "wf_start_time": t0_first,
                        "wf_increment": dt,
                    })
                    group = GroupObject("Acquisition")
                except Exception:
                    if progress_cb:
                        try:
                            progress_cb(seg_index, total_segs)
                        except Exception:
                            pass
                    continue
                # Build Time channel
                channels = []
                try:
                    channels.append(
                        ChannelObject("Acquisition", "Time", t_rel, properties={
                            "unit_string": "s",
                            "wf_start_time": t0_first,
                            "wf_increment": dt,
                            "stored_domain": "time",
                        })
                    )
                except Exception:
                    pass
                # Build data channels
                try:
                    for nm in ch_names:
                        if nm not in grp:
                            # Skip channels absent in this segment
                            continue
                        try:
                            arr = grp[nm][:]
                        except Exception:
                            continue
                        # Copy properties, update waveform start time and increment
                        props = dict(props_cache.get(nm, {}))
                        props["wf_start_time"] = t0_first
                        props["wf_increment"] = dt
                        channels.append(ChannelObject("Acquisition", nm, arr, properties=props))
                    # Write this segment to the writer
                    w.write_segment([root, group] + channels)
                except Exception:
                    pass
                # Report progress
                if progress_cb:
                    try:
                        progress_cb(seg_index, total_segs)
                    except Exception:
                        pass
        # Atomically rename the temporary file to its final name
        try:
            os.replace(tmp_out, out_path)
        except Exception as e:
            # Clean up tmp file on failure
            try:
                if os.path.exists(tmp_out):
                    os.remove(tmp_out)
            except Exception:
                pass
            raise RuntimeError(f"Errore durante il rename atomico: {e}")

        # Post‑merge validation: open the final file and check consistency
        if not self._validate_merged_file(out_path, fs):
            raise RuntimeError(
                "Merge non valido: i canali hanno lunghezze inconsistenti o il tempo non è monotono. "
                "I segmenti originali sono stati conservati per permettere il recupero."
            )

    def _validate_merged_file(self, path: str, fs: float) -> bool:
        """
        Validate that the merged TDMS file at ``path`` has channels of
        consistent length and a monotonic, regularly sampled time vector.

        Parameters
        ----------
        path : str
            Path of the merged TDMS file to validate.
        fs : float
            Sampling frequency used to compute expected time increments.

        Returns
        -------
        bool
            True if the file passes all checks, False otherwise.
        """
        try:
            td = TdmsFile.read(path)
            grp = self._pick_group(td)
            if grp is None:
                return False
            # Ensure Time channel exists
            if "Time" not in grp:
                return False
            t = grp["Time"][:]
            if not isinstance(t, np.ndarray) or t.size == 0:
                return False
            # Check monotonic increase
            dt = np.diff(t)
            if not np.all(dt > 0):
                return False
            # Check approximate constant spacing
            expected = 1.0 / float(fs)
            tol = max(1e-6, 0.05 * expected)  # allow 5% variation
            if not np.all(np.abs(dt - expected) <= tol):
                return False
            # Check all data channels have same length as Time
            n = t.size
            for ch in grp.channels():
                if ch.name == "Time":
                    continue
                try:
                    arr = ch[:]
                except Exception:
                    return False
                if len(arr) != n:
                    return False
            return True
        except Exception:
            return False