import os
import datetime
import numpy as np
from nptdms import TdmsFile, TdmsWriter, RootObject, GroupObject, ChannelObject


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
    def merge_temp_tdms(self, folder: str, out_path: str):
        if not os.path.isdir(folder):
            raise RuntimeError(f"Cartella segmenti non trovata: {folder}")

        segs = self._list_segments(folder)
        if not segs:
            raise RuntimeError("Nessun segmento TDMS trovato da unire.")

        # Cache strutture
        ch_names = None                 # elenco dei canali DATI (esclude 'Time')
        props_cache = {}                # properties per canale (dal primo segmento utile)
        data_by_name = {}               # lista di pezzi per canale
        time_pieces = []                # pezzi del canale Time (se ricostruito da wf_*)
        cumulative_samples = 0          # per costruire il Time se serve

        t0_first = None                 # datetime inizio prova
        fs = None                       # frequenza di campionamento (1 / wf_increment)

        # --------------- Scansione segmenti ---------------
        for path in segs:
            try:
                td = TdmsFile.read(path)
            except Exception:
                continue

            grp = self._pick_group(td)
            if grp is None:
                continue

            # Elenco canali DATI dal primo segmento (escludo "Time")
            if ch_names is None:
                try:
                    ch_names = [c.name for c in grp.channels() if c.name != "Time"]
                except Exception:
                    ch_names = []
                if not ch_names:
                    # se proprio non ci sono canali dati, prova a ignorare questo segmento
                    continue
                for nm in ch_names:
                    data_by_name[nm] = []

            # Ricava t0_first e fs dal PRIMO canale che li dichiara
            # (preferibilmente dal Time se presente, altrimenti da un canale dati)
            # --- 1) prova dal canale Time del segmento ---
            seg_t0 = None
            seg_dt = None
            if "Time" in grp:
                try:
                    p = grp["Time"].properties
                    seg_t0 = p.get("wf_start_time", None)
                    seg_dt = p.get("wf_increment", None)
                except Exception:
                    pass
            # --- 2) se mancano, prova da un canale dati ---
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

            # inizializza t0_first e fs dal primo segmento utile
            if t0_first is None and seg_t0 is not None:
                t0_first = _to_py_datetime(seg_t0) or datetime.datetime.now()
            if fs is None and seg_dt not in (None, 0):
                try:
                    fs = 1.0 / float(seg_dt)
                except Exception:
                    pass

            # Determina N campioni del segmento:
            # preferisci len(Time), altrimenti prendi len del primo canale dati presente
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
                continue

            # Accumula i dati per canale
            for nm in ch_names:
                try:
                    if nm in grp:
                        arr = grp[nm][:]
                        if arr.size > 0:
                            data_by_name[nm].append(arr)
                except Exception:
                    pass

            # Ricostruzione del Time assoluto:
            # Se abbiamo già t0_first e fs, calc Time del segmento come offset cumulativo
            if t0_first is not None and fs not in (None, 0):
                dt = 1.0 / float(fs)
                t_seg = (cumulative_samples / float(fs)) + np.arange(N, dtype=np.float64) * dt
                time_pieces.append(t_seg)
            cumulative_samples += (N or 0)

            # Cache delle properties per ogni canale (solo la prima volta che lo si vede)
            for nm in ch_names:
                if nm not in props_cache and nm in grp:
                    try:
                        props_cache[nm] = dict(grp[nm].properties)
                    except Exception:
                        props_cache[nm] = {}

        # --------------- Validazioni e fallback ---------------
        if ch_names is None:
            raise RuntimeError("Nessun canale valido trovato nei segmenti.")
        if t0_first is None:
            t0_first = datetime.datetime.now()
        if fs is None or fs <= 0:
            fs = 1.0  # fallback prudente

        # --------------- Concatena dati ---------------
        for nm in ch_names:
            if data_by_name[nm]:
                data_by_name[nm] = np.concatenate(data_by_name[nm], axis=0)
            else:
                data_by_name[nm] = np.array([], dtype=np.float64)

        # --------------- Costruisci il canale Time continuo ---------------
        if time_pieces:
            time_total = np.concatenate(time_pieces, axis=0)
        else:
            # fallback: genera Time da 0 a N-1 / fs
            n = len(next(iter(data_by_name.values()))) if data_by_name else 0
            time_total = np.arange(n, dtype=np.float64) / float(fs)

        # --------------- Scrittura finale ---------------
        os.makedirs(os.path.dirname(out_path) or ".", exist_ok=True)
        with TdmsWriter(open(out_path, "wb")) as w:
            root = RootObject(properties={
                "created": datetime.datetime.now(),
                "wf_merged": True,
                "source_folder": os.path.abspath(folder),
            })
            group = GroupObject("Acquisition")
            channels = []

            # Canale Time CONTINUO (secondi dall'inizio prova)
            channels.append(
                ChannelObject("Acquisition", "Time", time_total, properties={
                    "unit_string": "s",
                    "wf_start_time": t0_first,                 # inizio della prova
                    "wf_increment": 1.0 / float(fs),          # passo temporale
                    "stored_domain": "time",
                })
            )

            # Canali dati come waveform continue
            for nm in ch_names:
                props = dict(props_cache.get(nm, {}))
                # Aggiorna/forza wf_* per l'intero file unito
                props["wf_start_time"] = t0_first
                props["wf_increment"] = 1.0 / float(fs)
                channels.append(ChannelObject("Acquisition", nm, data_by_name[nm], properties=props))

            w.write_segment([root, group] + channels)
