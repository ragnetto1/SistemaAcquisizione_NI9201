# Data/Ora: 2026-02-12 20:41:44
import importlib.util
import os
import sys
import traceback
from pathlib import Path
from typing import Optional, Tuple


MODULE_DIR = Path(__file__).resolve().parent
REPO_ROOT = MODULE_DIR.parent
if str(REPO_ROOT) not in sys.path:
    # Keep module directory precedence so "import main" resolves to ni9201/main.py.
    sys.path.append(str(REPO_ROOT))


def _install_quiet_keyboardinterrupt_excepthook() -> None:
    previous = sys.excepthook

    def _quiet_excepthook(exc_type, exc_value, exc_tb):
        if exc_type is KeyboardInterrupt or isinstance(exc_value, KeyboardInterrupt):
            return
        try:
            previous(exc_type, exc_value, exc_tb)
        except Exception:
            pass

    sys.excepthook = _quiet_excepthook


def _load_signaldoki_icon():
    from PyQt5 import QtGui
    try:
        names = ("signaldoki-appicon.ico", "signaldoki-appicon.svg", "signaldoki-icon.svg") if sys.platform.startswith("win") else ("signaldoki-appicon.svg", "signaldoki-appicon.ico", "signaldoki-icon.svg")
        for name in names:
            icon_path = REPO_ROOT / "icone" / name
            if icon_path.is_file():
                return QtGui.QIcon(str(icon_path))
    except Exception:
        pass
    return QtGui.QIcon()


def _apply_windows_app_id(app_id: str) -> None:
    try:
        if sys.platform.startswith("win"):
            import ctypes
            ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID(str(app_id))
    except Exception:
        pass


def main():
    _install_quiet_keyboardinterrupt_excepthook()
    _apply_windows_app_id("signaldoki.ni9201")
    from PyQt5 import QtWidgets
    from acquisition import AcquisitionManager
    from tdms_merge import TdmsMerger

    app = QtWidgets.QApplication.instance()
    created_app = False
    if app is None:
        app = QtWidgets.QApplication(sys.argv)
        created_app = True
    icon = _load_signaldoki_icon()
    if not icon.isNull():
        try:
            app.setWindowIcon(icon)
        except Exception:
            pass

    # In questa versione l'applicazione e progettata esclusivamente per la NI-9201.
    # Non viene richiesto all'utente di selezionare il modello della scheda.
    acq_manager = AcquisitionManager()
    WindowCls = _resolve_window_class(acq_manager, default_digits="9201")
    window = WindowCls(acq_manager=acq_manager, merger=TdmsMerger())
    if not icon.isNull():
        try:
            window.setWindowIcon(icon)
        except Exception:
            pass
    window.show()

    exit_code = app.exec_()
    if created_app:
        sys.exit(exit_code)
    return exit_code


def _has_physical_device(acq_manager, default_digits: str) -> bool:
    digits = str(default_digits or "").strip()
    try:
        board = str(getattr(acq_manager, "board_type", "") or "")
        only_digits = "".join(ch for ch in board if ch.isdigit())
        if only_digits:
            digits = only_digits
    except Exception:
        pass

    methods = ["list_current_devices_meta"]
    if digits:
        methods.extend([f"list_ni{digits}_devices_meta", f"list_ni{digits}_devices"])

    board_keys = set()
    if digits:
        board_keys.add(f"NI{digits}")
    try:
        board_keys.add(str(getattr(acq_manager, "board_type", "") or "").upper().replace(" ", ""))
    except Exception:
        pass
    board_keys = {k for k in board_keys if k}

    def _matches_board(item: dict) -> bool:
        ptype = str(item.get("product_type", "") or "").upper().replace(" ", "")
        if not ptype:
            return True
        return any(k in ptype for k in board_keys)

    for meth in methods:
        fn = getattr(acq_manager, meth, None)
        if not callable(fn):
            continue
        try:
            out = list(fn() or [])
        except Exception:
            continue
        if not out:
            continue
        first = out[0]
        if isinstance(first, dict):
            matched_any = False
            unknown_state_found = False
            for item in out:
                if not isinstance(item, dict):
                    continue
                if not _matches_board(item):
                    continue
                matched_any = True
                sim = item.get("is_simulated", None)
                if sim is False:
                    return True
                if sim is None:
                    unknown_state_found = True
            if matched_any and unknown_state_found:
                return True
            continue
        return True
    return False


def _resolve_window_class(acq_manager, default_digits: str):
    use_color_ui = _has_physical_device(acq_manager, default_digits=default_digits)
    module_name = "color_ui" if use_color_ui else "ui"
    try:
        mod = __import__(module_name, fromlist=["AcquisitionWindow"])
        cls = getattr(mod, "AcquisitionWindow", None)
        if cls is not None:
            return cls
    except Exception:
        pass
    from ui import AcquisitionWindow

    return AcquisitionWindow


def _extract_missing_module_name(exc: BaseException) -> str:
    if isinstance(exc, ModuleNotFoundError):
        name = getattr(exc, "name", "")
        if name:
            return str(name)
    return ""


def _show_startup_error_and_exit(board_label: str, exc: Optional[BaseException], tb_text: str) -> None:
    from PyQt5 import QtWidgets

    _apply_windows_app_id(f"signaldoki.{str(board_label or 'module').lower()}")
    app = QtWidgets.QApplication.instance()
    created_app = False
    if app is None:
        app = QtWidgets.QApplication(sys.argv)
        created_app = True
    icon = _load_signaldoki_icon()
    if not icon.isNull():
        try:
            app.setWindowIcon(icon)
        except Exception:
            pass

    missing_name = _extract_missing_module_name(exc) if exc else ""
    if missing_name:
        reason = f'modulo Python non installato: "{missing_name}"'
    elif exc is not None:
        reason = f"{exc.__class__.__name__}: {exc}"
    else:
        reason = "errore sconosciuto durante il bootstrap"

    msg = QtWidgets.QMessageBox()
    msg.setIcon(QtWidgets.QMessageBox.Critical)
    msg.setWindowTitle("Errore avvio modulo")
    msg.setText(
        f'Impossibile avviare il modulo "{board_label}".\n'
        f'Errore in "UI avvio e import moduli.py": {reason}.'
    )
    if tb_text:
        msg.setDetailedText(tb_text)
    msg.setStandardButtons(QtWidgets.QMessageBox.NoButton)
    msg.addButton("Stop", QtWidgets.QMessageBox.RejectRole)
    msg.exec_()

    if created_app:
        app.quit()
    sys.exit(1)


def _run_startup_import_ui() -> Tuple[bool, Optional[BaseException], str]:
    startup_path = os.path.join(os.path.dirname(__file__), "UI avvio e import moduli.py")
    if not os.path.isfile(startup_path):
        err = FileNotFoundError(f'File non trovato: "{startup_path}"')
        return False, err, str(err)

    try:
        spec = importlib.util.spec_from_file_location("ui_avvio_import_moduli", startup_path)
        if spec is None or spec.loader is None:
            err = ImportError("Impossibile creare lo spec di import della UI di avvio.")
            return False, err, str(err)

        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        startup_cls = getattr(mod, "ImportStartupUI", None)
        if startup_cls is None:
            err = AttributeError('Classe "ImportStartupUI" non trovata nel modulo di avvio.')
            return False, err, str(err)

        startup_cls().run()
        return True, None, ""
    except Exception as exc:
        return False, exc, traceback.format_exc()


if __name__ == "__main__":
    # main.py resta il punto di avvio ufficiale.
    # La UI di avvio e obbligatoria: in caso di errore viene mostrato un popup e il processo termina.
    ok, err, tb = _run_startup_import_ui()
    if not ok:
        _show_startup_error_and_exit("NI9201", err, tb)
