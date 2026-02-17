from __future__ import annotations

from pathlib import Path
import argparse

import numpy as np
from nptdms import TdmsFile


def _print_group_summary(tdms: TdmsFile, group_name: str) -> None:
    try:
        group = tdms[group_name]
    except Exception:
        print(f"[WARN] Gruppo non trovato: {group_name}")
        return

    print(f"\n[{group_name}]")
    for ch in group.channels():
        try:
            data = ch[:]
            n = int(len(data))
        except Exception:
            n = 0
            data = np.array([])
        print(f"- {ch.name}: {n} samples")

        # Stampa alcune proprieta' utili per i file prodotti dal core.
        props = dict(getattr(ch, "properties", {}) or {})
        wf_inc = props.get("wf_increment")
        unit = props.get("Unit", props.get("unit_string", ""))
        if wf_inc is not None or unit:
            print(f"  wf_increment={wf_inc} unit={unit}")

        if ch.name == "Time" and n > 1:
            try:
                dt = float(np.median(np.diff(np.asarray(data, dtype=np.float64))))
                if dt > 0:
                    print(f"  Fs stimata={1.0 / dt:.6g} Hz")
            except Exception:
                pass


def main() -> int:
    parser = argparse.ArgumentParser(description="Lettura rapida file TDMS prodotti dal core.")
    parser.add_argument("tdms_path", nargs="?", help="Percorso file .tdms")
    args = parser.parse_args()

    if args.tdms_path:
        path = Path(args.tdms_path)
    else:
        path = Path(r"C:\UG-WORK\SistemaAcquisizione_NI9201\0_aa.tdms")

    if not path.is_file():
        print(f"[ERRORE] File non trovato: {path}")
        return 1

    try:
        tdms = TdmsFile.read(str(path))
    except Exception as exc:
        print(f"[ERRORE] Impossibile aprire TDMS: {exc}")
        return 1

    print(f"File: {path}")
    group_names = [g.name for g in tdms.groups()]
    print("Gruppi:", ", ".join(group_names) if group_names else "<nessuno>")

    # Il core salva i segnali principali nel gruppo Acquisition e,
    # per il modulo 9234, opzionalmente lo spettro nel gruppo FFT.
    if "Acquisition" in group_names:
        _print_group_summary(tdms, "Acquisition")
    if "FFT" in group_names:
        _print_group_summary(tdms, "FFT")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
