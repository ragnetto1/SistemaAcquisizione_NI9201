# Data/Ora: 2026-02-12 20:41:44
import importlib.util
import os
import sys
import traceback


def main():
    from PyQt5 import QtWidgets
    from acquisition import AcquisitionManager
    from tdms_merge import TdmsMerger
    from ui import AcquisitionWindow

    app = QtWidgets.QApplication.instance()
    created_app = False
    if app is None:
        app = QtWidgets.QApplication(sys.argv)
        created_app = True

    # In questa versione l'applicazione e progettata esclusivamente per la NI-9234.
    # Non viene richiesto all'utente di selezionare il modello della scheda.
    acq_manager = AcquisitionManager()
    window = AcquisitionWindow(acq_manager=acq_manager, merger=TdmsMerger())
    window.show()

    exit_code = app.exec_()
    if created_app:
        sys.exit(exit_code)
    return exit_code


def _run_startup_import_ui() -> bool:
    startup_path = os.path.join(os.path.dirname(__file__), "UI avvio e import moduli.py")
    if not os.path.isfile(startup_path):
        return False

    try:
        spec = importlib.util.spec_from_file_location("ui_avvio_import_moduli", startup_path)
        if spec is None or spec.loader is None:
            return False

        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        startup_cls = getattr(mod, "ImportStartupUI", None)
        if startup_cls is None:
            return False

        startup_cls().run()
        return True
    except Exception:
        traceback.print_exc()
        return False


if __name__ == "__main__":
    # main.py resta il punto di avvio ufficiale.
    # Se la UI di avvio non e disponibile, avvia direttamente l'app.
    if not _run_startup_import_ui():
        main()
