from __future__ import annotations

from pathlib import Path
import sys


def _bootstrap_repo_imports() -> None:
    repo_root = Path(__file__).resolve().parents[1]
    root_str = str(repo_root)
    if root_str not in sys.path:
        sys.path.insert(0, root_str)


def main() -> int:
    _bootstrap_repo_imports()

    from find_cdaq_nimax_like import discover_cdaq_nimax_like

    result = discover_cdaq_nimax_like()
    if result.error_message:
        print(f"[ERRORE] {result.error_message}")
        return 1

    print(f"Chassis trovati: {len(result.chassis_list)}")
    for ch in result.chassis_list:
        print(
            f"- {ch.alias} | {ch.model} | {'simulata' if ch.is_simulated else 'collegata'} "
            f"| slot={ch.slot_count} | max={ch.max_rate_hz:.6g} Hz"
        )

    all_rows = list(result.connected_rows) + list(result.simulated_rows)
    print(f"\nModuli/slot rilevati: {len(all_rows)}")
    for row in all_rows:
        slot = f"slot {row.slot_index}" if row.slot_index else "slot ?"
        status = "empty" if row.is_empty else (row.board_label or "sconosciuta")
        kind = "simulata" if row.is_simulated else "collegata"
        print(f"- {row.chassis_alias} {slot}: {status} [{kind}]")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
