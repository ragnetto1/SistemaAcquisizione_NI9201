# Data/Ora: 2026-02-12 20:42:58
import importlib
import sys
import time
import traceback

from PyQt5 import QtCore, QtWidgets


IMPORT_STEPS = [
    ("acquisition", "import acquisition"),
    ("tdms_merge", "import tdms_merge"),
    ("ui", "import ui"),
    ("main", "import main"),
]


class ImportWorker(QtCore.QObject):
    sigStepStart = QtCore.pyqtSignal(int, int, str)
    sigStepDone = QtCore.pyqtSignal(int, int, str)
    sigError = QtCore.pyqtSignal(str, str)
    sigFinished = QtCore.pyqtSignal()

    @QtCore.pyqtSlot()
    def run(self) -> None:
        total = len(IMPORT_STEPS)
        for idx, (module_name, label) in enumerate(IMPORT_STEPS):
            self.sigStepStart.emit(idx, total, label)
            try:
                importlib.import_module(module_name)
            except Exception:
                self.sigError.emit(label, traceback.format_exc())
                return
            self.sigStepDone.emit(idx, total, label)

        self.sigFinished.emit()


class ImportStartupUI:
    def __init__(self) -> None:
        self._app = QtWidgets.QApplication.instance()
        if self._app is None:
            self._app = QtWidgets.QApplication(sys.argv)

        self._progress = 0.0
        self._target = 0.0
        self._all_done = False
        self._launch_scheduled = False
        self._launch_requested = False
        self._failed = False
        self._error_title = ""
        self._error_message = ""

        self._build_ui()
        self._setup_worker()

        self._timer = QtCore.QTimer(self._window)
        self._timer.setInterval(30)
        self._timer.timeout.connect(self._tick)

    def _build_ui(self) -> None:
        self._window = QtWidgets.QWidget()
        self._window.setWindowTitle("Avvio e import moduli")
        self._window.setFixedSize(560, 170)

        main = QtWidgets.QVBoxLayout(self._window)
        main.setContentsMargins(12, 12, 12, 12)
        main.setSpacing(8)

        self._lbl_title = QtWidgets.QLabel("SistemaAcquisizione_NI9201")
        f_title = self._lbl_title.font()
        f_title.setPointSize(11)
        f_title.setBold(True)
        self._lbl_title.setFont(f_title)
        main.addWidget(self._lbl_title)

        self._lbl_status = QtWidgets.QLabel("Preparazione import...")
        f_status = self._lbl_status.font()
        f_status.setPointSize(10)
        self._lbl_status.setFont(f_status)
        main.addWidget(self._lbl_status)

        bar_row = QtWidgets.QHBoxLayout()
        self._bar = QtWidgets.QProgressBar()
        self._bar.setRange(0, 100)
        self._bar.setValue(0)
        self._bar.setTextVisible(False)
        bar_row.addWidget(self._bar, 1)

        self._lbl_percent = QtWidgets.QLabel("0%")
        self._lbl_percent.setFixedWidth(40)
        self._lbl_percent.setAlignment(QtCore.Qt.AlignRight | QtCore.Qt.AlignVCenter)
        bar_row.addWidget(self._lbl_percent)
        main.addLayout(bar_row)

        self._lbl_detail = QtWidgets.QLabel("In attesa...")
        f_detail = self._lbl_detail.font()
        f_detail.setFamily("Consolas")
        f_detail.setPointSize(10)
        self._lbl_detail.setFont(f_detail)
        main.addWidget(self._lbl_detail)

    def _setup_worker(self) -> None:
        self._thread = QtCore.QThread(self._window)
        self._worker = ImportWorker()
        self._worker.moveToThread(self._thread)

        self._thread.started.connect(self._worker.run)
        self._worker.sigStepStart.connect(self._on_step_start)
        self._worker.sigStepDone.connect(self._on_step_done)
        self._worker.sigError.connect(self._on_error)
        self._worker.sigFinished.connect(self._on_finished)

    def _on_step_start(self, idx: int, total: int, label: str) -> None:
        step = 100.0 / max(1, total)
        step_start = idx * step
        self._lbl_status.setText("Import moduli in corso...")
        self._lbl_detail.setText(label)
        self._target = max(self._target, step_start + (step * 0.92))

    def _on_step_done(self, idx: int, total: int, label: str) -> None:
        step = 100.0 / max(1, total)
        step_end = (idx + 1) * step
        self._lbl_status.setText("Modulo importato")
        self._lbl_detail.setText(f"{label} completato")
        self._target = max(self._target, step_end)

    def _on_error(self, label: str, message: str) -> None:
        self._failed = True
        self._error_title = f"Errore durante {label}"
        self._error_message = message

    def _on_finished(self) -> None:
        self._all_done = True
        self._lbl_status.setText("Import completati")
        self._lbl_detail.setText("Avvio applicazione...")
        self._target = 100.0

    def _tick(self) -> None:
        self._animate_progress()

        if self._failed:
            self._timer.stop()
            QtWidgets.QMessageBox.critical(
                self._window,
                self._error_title or "Errore import",
                self._error_message,
            )
            self._shutdown(launch=False)
            return

        if self._all_done and not self._launch_scheduled and self._progress >= 99.9:
            self._launch_scheduled = True
            QtCore.QTimer.singleShot(120, lambda: self._shutdown(launch=True))

    def _animate_progress(self) -> None:
        if self._progress >= self._target:
            return

        gap = self._target - self._progress
        speed = max(0.20, min(2.20, 0.18 * gap + 0.28))
        self._progress = min(self._target, self._progress + speed)

        self._bar.setValue(int(round(self._progress)))
        self._lbl_percent.setText(f"{int(round(self._progress))}%")

    def _cleanup_thread(self) -> None:
        try:
            if self._thread.isRunning():
                self._thread.quit()
                self._thread.wait(1500)
        except Exception:
            pass

    def _shutdown(self, launch: bool) -> None:
        self._timer.stop()
        self._launch_requested = bool(launch and not self._failed)
        self._cleanup_thread()
        self._window.close()
        self._app.quit()

    def _launch_main(self) -> None:
        try:
            main_module = sys.modules.get("main")
            if main_module is None:
                main_module = importlib.import_module("main")

            entry = getattr(main_module, "main", None)
            if not callable(entry):
                raise RuntimeError("Funzione main() non trovata nel modulo main.")

            time.sleep(0.08)
            entry()
        except Exception:
            traceback.print_exc()

    def run(self) -> None:
        self._window.show()
        self._thread.start()
        self._timer.start()
        self._app.exec_()

        if self._launch_requested and not self._failed:
            self._launch_main()


if __name__ == "__main__":
    ImportStartupUI().run()
