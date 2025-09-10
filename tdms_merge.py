import os
import datetime
import numpy as np
from nptdms import TdmsFile, TdmsWriter, RootObject, GroupObject, ChannelObject


def _to_py_datetime(x):
    """Converte datetime-like (anche numpy.datetime64) in datetime.datetime naive."""
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


def _seconds_between(t0, t_ref):
    """Offset in secondi tra due datetime-like (supporta anche numpy.datetime64)."""
    d0 = _to_py_datetime(t0) if not isinstance(t0, datetime.datetime) else t0
    dr = _to_py_datetime(t_ref) if not isinstance(t_ref, datetime.datetime) else t_ref
    if d0 is not None and dr is not None:
        return (d0 - dr).total_seconds()
    # fallback: via numpy (se entrambi convertibili)
    try:
        t0n = np.datetime64(t0)
        trn = np.datetime64(t_ref)
        ns = (t0n - trn).astype("timedelta64[ns]").astype("int64")
        return float(ns) / 1e9
    except Exception:
        return 0.0


class TdmsMerger:
    """
    Unisce i segmenti .tdms di una cartella nell'ordine cronologico.
    - Ricostruisce il tempo continuo usando wf_start_time + wf_increment
    - Ignora file vuoti/corrotti o senza gruppi; se manca 'Acquisition', usa il primo gruppo
    """

    def _pick_group(self, td: TdmsFile):
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

    def merge_temp_tdms(self, folder: str, out_path: str):
        if not os.path.isdir(folder):
            raise RuntimeError(f"Cartella segmenti non trovata: {folder}")

        segs = [
            os.path.join(folder, f)
            for f in os.listdir(folder)
            if f.lower().endswith(".tdms") and not f.lower().endswith(".tdms_index")
        ]
        if not segs:
            raise RuntimeError("Nessun segmento TDMS trovato da unire.")
        segs.sort()

        ch_names = None
        props_cache = {}
        data_by_name = {}
        time_pieces = []

        t0_first = None
        fs = None  # 1 / wf_increment

        for path in segs:
            try:
                td = TdmsFile.read(path)
            except Exception:
                continue

            grp = self._pick_group(td)
            if grp is None:
                continue

            # elenco canali dal primo file utile (escludo 'Time')
            if ch_names is None:
                ch_names = [c.name for c in grp.channels() if c.name != "Time"]
                if not ch_names:
                    continue
                for nm in ch_names:
                    data_by_name[nm] = []

            # cache properties canale dal primo segmento che lo contiene
            for nm in ch_names:
                if nm not in props_cache and nm in grp:
                    props_cache[nm] = dict(grp[nm].properties)

            # lunghezza segmento e timing
            N = None
            wf_dt = None
            wf_t0 = None
            if "Time" in grp:
                try:
                    N = len(grp["Time"])
                    wf_dt = grp["Time"].properties.get("wf_increment", None)
                    wf_t0 = grp["Time"].properties.get("wf_start_time", None)
                    if t0_first is None and wf_t0 is not None:
                        t0_first = _to_py_datetime(wf_t0) or datetime.datetime.now()
                    if wf_dt is not None and fs is None:
                        fs = 1.0 / float(wf_dt)
                except Exception:
                    pass

            # se non ho il canale Time, deduco N da un canale dati
            if N is None:
                for nm in ch_names:
                    if nm in grp:
                        try:
                            N = len(grp[nm])
                            break
                        except Exception:
                            pass
            if N is None or N <= 0:
                continue

            # dati
            for nm in ch_names:
                try:
                    if nm in grp:
                        arr = grp[nm][:]
                        if arr.size > 0:
                            data_by_name[nm].append(arr)
                except Exception:
                    pass

            # tempo di questo segmento (ricostruito assoluto)
            if t0_first is not None and wf_t0 is not None and wf_dt is not None:
                offset = _seconds_between(wf_t0, t0_first)
                dt = float(wf_dt)
                t_seg = offset + np.arange(N, dtype=np.float64) * dt
                time_pieces.append(t_seg)

        if ch_names is None:
            raise RuntimeError("Nessun canale valido trovato nei segmenti.")

        # concatena dati
        for nm in ch_names:
            if data_by_name[nm]:
                data_by_name[nm] = np.concatenate(data_by_name[nm], axis=0)
            else:
                data_by_name[nm] = np.array([], dtype=np.float64)

        # tempo finale
        if time_pieces:
            time_total = np.concatenate(time_pieces, axis=0)
            if time_total.size > 1 and fs is None:
                dt_est = float(time_total[1] - time_total[0])
                fs = 1.0 / dt_est if dt_est > 0 else 1.0
        else:
            # fallback se non c'è nulla nei time_pieces
            n = len(next(iter(data_by_name.values()))) if data_by_name else 0
            if fs is None or fs <= 0:
                fs = 1.0
            time_total = np.arange(n, dtype=np.float64) / float(fs)

        if t0_first is None:
            t0_first = datetime.datetime.now()
        if fs is None or fs <= 0:
            fs = 1.0

        # scrittura finale
        os.makedirs(os.path.dirname(out_path) or ".", exist_ok=True)
        with TdmsWriter(open(out_path, "wb")) as w:
            root = RootObject(properties={"created": datetime.datetime.now()})
            group = GroupObject("Acquisition")
            channels = []

            # Time
            channels.append(
                ChannelObject("Acquisition", "Time", time_total, properties={
                    "unit_string": "s",
                    "wf_start_time": t0_first,
                    "wf_increment": 1.0 / float(fs),
                    "stored_domain": "time",
                })
            )

            # canali dati con properties del primo segmento
            for nm in ch_names:
                props = dict(props_cache.get(nm, {}))
                props["wf_start_time"] = t0_first
                props["wf_increment"] = 1.0 / float(fs)
                channels.append(ChannelObject("Acquisition", nm, data_by_name[nm], properties=props))

            w.write_segment([root, group] + channels)
