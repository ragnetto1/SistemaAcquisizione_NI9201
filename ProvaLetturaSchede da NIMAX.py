#!/usr/bin/env python3
"""
Robust NI MAX enumerator (physical + simulated) with diagnostics.

What’s new vs v1:
- Clear diagnostics if Python modules are missing or if no devices are found.
- Broader discovery with nisyscfg:
    * Do NOT require is_present=True (some simulated/remote may be filtered out).
    * Query all available experts (DAQmx, etc.) explicitly.
    * Do not skip chassis by default (you can filter later).
- Fallback to nidaqmx still included and now clearly reported.
"""

from typing import Any, Dict, List, Optional, Tuple
import sys
import importlib

def try_import(module_name: str) -> Tuple[Optional[object], Optional[Exception]]:
    try:
        return importlib.import_module(module_name), None
    except Exception as e:
        return None, e

def safe_get(obj: Any, name: str, default=None):
    try:
        return getattr(obj, name)
    except Exception:
        return default

def as_bool(val) -> Optional[bool]:
    if isinstance(val, bool):
        return val
    if val in (0, 1):
        return bool(val)
    return None

def fmt(val):
    if isinstance(val, (list, tuple)):
        return ", ".join(str(x) for x in val)
    return "" if val is None else str(val)

def collect_with_nisyscfg(diag: List[str]) -> List[Dict[str, Any]]:
    nisyscfg, err = try_import("nisyscfg")
    if not nisyscfg:
        diag.append(f"[diag] Modulo Python 'nisyscfg' non disponibile: {err}")
        return []

    devices: List[Dict[str, Any]] = []
    try:
        with nisyscfg.Session() as session:
            # Enumerate available experts so we’re sure DAQmx is included
            experts = []
            try:
                for ex in session.experts:
                    experts.append(ex)
                diag.append("[diag] nisyscfg experts trovati: " + ", ".join(e.name for e in experts))
            except Exception as e:
                diag.append(f"[diag] Impossibile leggere gli experts: {e}")
                experts = []

            # create a broad filter (do not force is_present)
            base_filter = session.create_filter()
            base_filter.is_present = None  # include everything
            # Enumerate twice: once without expert, then per-expert (defensive)
            search_specs = [("no-expert", None)] + [(e.name, e) for e in experts]

            seen_ids = set()
            for label, expert in search_specs:
                try:
                    with session.find_hardware(base_filter, expert_handle=expert) as found:
                        for hw in found or []:
                            # Make a synthetic unique key to avoid duplicates across passes
                            key = (safe_get(hw, "expert_name", ""), safe_get(hw, "product_name", ""), safe_get(hw, "serial_number", ""), safe_get(hw, "name",""))
                            if key in seen_ids:
                                continue
                            seen_ids.add(key)
                            devices.append({
                                "source": f"nisyscfg:{label}",
                                "alias": safe_get(hw, "name", ""),
                                "product_name": safe_get(hw, "product_name", ""),
                                "product_type": safe_get(hw, "product_type", ""),
                                "vendor_name": safe_get(hw, "vendor_name", ""),
                                "serial_number": safe_get(hw, "serial_number", ""),
                                "expert_name": safe_get(hw, "expert_name", ""),
                                "device_class": safe_get(hw, "device_class", ""),
                                "bus_type": safe_get(hw, "bus_type", ""),
                                "is_simulated": as_bool(safe_get(hw, "is_simulated", None)),
                                "is_present": as_bool(safe_get(hw, "is_present", None)),
                                "slot_number": safe_get(hw, "slot", safe_get(hw, "slot_number", "")),
                                "chassis_name": safe_get(hw, "chassis_name", ""),
                                "chassis_product_name": safe_get(hw, "chassis_product_name", ""),
                                "chassis_serial_number": safe_get(hw, "chassis_serial_number", ""),
                                "_handle": hw,
                            })
                except Exception as e:
                    diag.append(f"[diag] find_hardware({label}) ha dato errore: {e}")
    except Exception as e:
        diag.append(f"[diag] Errore durante la sessione nisyscfg: {e}")
        return []
    return devices

def collect_with_nidaqmx(diag: List[str]) -> List[Dict[str, Any]]:
    nidaqmx, err = try_import("nidaqmx")
    if not nidaqmx:
        diag.append(f"[diag] Modulo Python 'nidaqmx' non disponibile: {err}")
        return []
    try:
        from nidaqmx.system import System
    except Exception as e:
        diag.append(f"[diag] Impossibile importare nidaqmx.system.System: {e}")
        return []

    devices: List[Dict[str, Any]] = []
    try:
        sysobj = System.local()
        for d in sysobj.devices:
            def g(name, default=""):
                try:
                    return getattr(d, name)
                except Exception:
                    return default
            devices.append({
                "source": "nidaqmx",
                "alias": g("name"),
                "product_name": g("product_type"),
                "product_type": g("product_category"),
                "vendor_name": "NI",
                "serial_number": g("serial_num"),
                "expert_name": "NI-DAQmx",
                "device_class": "DAQ",
                "bus_type": g("bus_type"),
                "is_simulated": as_bool(g("is_simulated", None)),
                "is_present": True,
                "slot_number": g("slot_num"),
                "chassis_name": "",
                "chassis_product_name": "",
                "chassis_serial_number": "",
                "_handle": d,
            })
        if not devices:
            diag.append("[diag] nidaqmx ha restituito 0 dispositivi. Il driver NI-DAQmx è installato? Il device è visibile in MAX sotto 'NI-DAQmx Devices'?")
    except Exception as e:
        diag.append(f"[diag] Errore in nidaqmx.System.local(): {e}")
        return []
    return devices

def pretty_print_table(rows: List[Dict[str, Any]]):
    if not rows:
        print("Nessuna scheda trovata.")
        return
    headers = ["#", "Alias", "Prodotto", "Seriale", "Simulata", "Driver/Expert", "Fonte"]
    col_widths = [3, 20, 26, 14, 9, 16, 14]

    def trunc(s, w):
        s = fmt(s)
        return s if len(s) <= w else s[: w-1] + "…"

    line = "  ".join(h.ljust(w) for h, w in zip(headers, col_widths))
    print(line)
    print("-" * len(line))
    for i, r in enumerate(rows, 1):
        cells = [
            str(i).rjust(col_widths[0]),
            trunc(r.get("alias", ""), col_widths[1]).ljust(col_widths[1]),
            trunc(r.get("product_name", ""), col_widths[2]).ljust(col_widths[2]),
            trunc(r.get("serial_number", ""), col_widths[3]).ljust(col_widths[3]),
            ("Sì" if r.get("is_simulated") else "No" if r.get("is_simulated") is not None else "").ljust(col_widths[4]),
            trunc(r.get("expert_name", ""), col_widths[5]).ljust(col_widths[5]),
            trunc(r.get("source", ""), col_widths[6]).ljust(col_widths[6]),
        ]
        print("  ".join(cells))

def dump_details(dev: Dict[str, Any]):
    print("\nDettagli dispositivo selezionato (letti dall'API):\n")
    keys = [
        ("Alias", "alias"),
        ("Prodotto", "product_name"),
        ("Tipo", "product_type"),
        ("Classe", "device_class"),
        ("Vendor", "vendor_name"),
        ("Seriale", "serial_number"),
        ("Driver/Expert", "expert_name"),
        ("Bus", "bus_type"),
        ("Simulata", "is_simulated"),
        ("Presente", "is_present"),
        ("Slot", "slot_number"),
        ("Chassis", "chassis_name"),
        ("Chassis (prodotto)", "chassis_product_name"),
        ("Chassis (seriale)", "chassis_serial_number"),
    ]
    for label, key in keys:
        val = dev.get(key)
        if isinstance(val, bool):
            val = "Sì" if val else "No"
        print(f"  {label:20}: {fmt(val)}")

    h = dev.get("_handle")
    if h is not None:
        extra_props = [
            "firmware_version",
            "pci_bus_number",
            "pci_device_number",
            "tcpip_hostname",
            "tcpip_ipv4",
            "tcpip_mac",
            "product_id",
            "chassis_slot_number",
        ]
        printed_any = False
        for p in extra_props:
            v = safe_get(h, p, None)
            if v not in (None, "", 0):
                if not printed_any:
                    print("\nProprietà extra:")
                    printed_any = True
                print(f"  {p:20}: {fmt(v)}")

def main():
    diagnostics: List[str] = []

    all_devices = []
    all_devices.extend(collect_with_nisyscfg(diagnostics))
    existing_aliases = {d.get("alias") for d in all_devices}
    daq_devs = collect_with_nidaqmx(diagnostics)
    for d in daq_devs:
        if d.get("alias") not in existing_aliases:
            all_devices.append(d)

    # Sort for stable output
    all_devices.sort(key=lambda d: (fmt(d.get("alias")), fmt(d.get("product_name"))))

    print("\n=== Dispositivi NI in NI MAX (fisici + simulati/virtuali) ===\n")
    pretty_print_table(all_devices)

    if not all_devices:
        print("\n--- DIAGNOSTICA ---")
        for line in diagnostics:
            print(line)
        print("\nSuggerimenti:")
        print(" 1) Verifica l'architettura: Python 64-bit con driver NI 64-bit (o 32/32).")
        print(" 2) Installa i pacchetti Python:  pip install nisyscfg nidaqmx")
        print(" 3) In NI MAX, assicurati che i device siano sotto 'NI-DAQmx Devices' e che non siano disconnessi.")
        print(" 4) Per dispositivi simulati DAQmx: in MAX > Dispositivi e Interfacce > Crea dispositivo DAQmx simulato.")
        return

    while True:
        try:
            sel = input("\nScegli il numero della scheda per vedere i dettagli (Invio per uscire): ").strip()
            if not sel:
                break
            idx = int(sel)
            if 1 <= idx <= len(all_devices):
                dump_details(all_devices[idx - 1])
            else:
                print("Indice non valido.")
        except ValueError:
            print("Per favore inserisci un numero valido.")
        except KeyboardInterrupt:
            print("\nInterrotto dall'utente.")
            break

if __name__ == "__main__":
    main()
