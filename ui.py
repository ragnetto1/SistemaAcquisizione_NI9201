# ui.py
from PyQt5 import QtCore, QtWidgets, QtGui
import sys
import configparser
import re
import shutil  # per rimuovere cartelle temporanee dopo merge
import glob
import pyqtgraph as pg
from collections import deque
import numpy as np
import os
import xml.etree.ElementTree as ET
import datetime
import json
import time
from typing import List, Callable, Optional, Dict, Any, Tuple

try:
    from syncronizzation import ModuleSyncAgent
except Exception:
    ModuleSyncAgent = None

# Path to store persistent configuration. It resides alongside this script.
CONFIG_FILE = os.path.join(os.path.dirname(__file__), "settings.json")

#
# Disable OpenGL rendering for pyqtgraph.  Using OpenGL together with
# PlotCurveItem.setData can lead to a memory leak on some systems.  See
# https://github.com/pyqtgraph/pyqtgraph/issues/3372 for discussion.  By
# disabling OpenGL here we force pyqtgraph to use its native Qt painting
# backend which has much more predictable memory usage.  Antialiasing is
# also disabled to keep CPU usage modest.
pg.setConfigOptions(useOpenGL=False, antialias=False)

# Colonne tabella
COL_ENABLE   = 0
COL_PHYS     = 1
COL_TYPE     = 2   # Tipo risorsa (Voltage o sensori dal DB)
COL_LABEL    = 3   # Nome canale (etichetta utente)
COL_VALUE    = 4   # Valore istantaneo (con unit? se selezionata)
COL_ZERO_BTN = 5
COL_ZERO_VAL = 6

# Percorso di default richiesto
DEFAULT_SAVE_DIR = r"C:\UG-WORK\SistemaAcquisizione_NI9201"
SENSOR_DB_DEFAULT = r"C:\UG-WORK\SistemaAcquisizione_NI9201\Sensor database.xml"

# XML tag (compat vecchio e nuovo formato multi-punti)
XML_ROOT  = "Sensors"
XML_ITEM  = "Sensor"
XML_NAME  = "NomeRisorsa"
XML_UNIT  = "GrandezzaFisica"
XML_CAL   = "CalibrationPoints"
XML_POINT = "Point"          # attr: volt, value
# vecchio (2 punti)
XML_V1V = "Valore1Volt"
XML_V1  = "Valore1"
XML_V2V = "Valore2Volt"
XML_V2  = "Valore2"


class AcquisitionWindow(QtWidgets.QMainWindow):
    # segnali thread-safe verso UI
    sigInstantBlock = QtCore.pyqtSignal(object, object, object)   # (t, [ys...], [names...])
    sigChartPoints  = QtCore.pyqtSignal(object, object, object)
    channelValueUpdated = QtCore.pyqtSignal(str, float)           # (start_label_name, value)

    def __init__(self, acq_manager, merger, parent=None):
        super().__init__(parent)
        self.acq = acq_manager
        self.merger = merger

        self.setWindowTitle("NI 9201 Acquisition - Demo Architettura")
        self.resize(1200, 740)

        # stati UI/logica
        self._building_table = False
        self._auto_change = False
        self._device_ready = False

        # mappature canali
        self._current_phys_order = []                    # ordine fisico corrente avviato
        self._label_by_phys = {f"ai{i}": f"ai{i}" for i in range(8)}   # label utente "Nome canaleâ€
        self._sensor_type_by_phys = {f"ai{i}": "Voltage" for i in range(8)}
        self._calib_by_phys = {f"ai{i}": {"unit":"", "a":1.0, "b":0.0} for i in range(8)}
        self._start_label_by_phys = {}                   # mapping phys -> nome al momento dello start
        self._last_enabled_phys = []

        # grafici: buffer
        MAXPTS = 12000
        self._chart_x = deque(maxlen=MAXPTS)
        self._chart_y_by_phys = {f"ai{i}": deque(maxlen=MAXPTS) for i in range(8)}
        self._instant_t = np.array([], dtype=float)
        self._instant_y_by_phys = {f"ai{i}": np.array([], dtype=float) for i in range(8)}
        self._chart_curves_by_phys = {}
        self._instant_curves_by_phys = {}

        # TDMS saving
        self._save_dir = DEFAULT_SAVE_DIR
        self._base_filename = "SenzaNome.tdms"
        self._active_subdir = None
        self._countdown = 60
        self._count_timer = QtCore.QTimer(self)
        self._count_timer.setInterval(1000)
        self._count_timer.timeout.connect(self._tick_countdown)

        # Timer to monitor disk stall/backlog
        self._backlog_timer = QtCore.QTimer(self)
        self._backlog_timer.setInterval(1000)  # check every second
        self._backlog_timer.timeout.connect(self._check_backlog)
        # Default update interval for charts; used to restore after stall.
        # A longer refresh interval (e.g. 100 ms) reduces CPU usage and memory
        # churn associated with converting deques to arrays at high rates.  The
        # memory footprint of charts grows if arrays are reallocated too often.
        self._default_gui_interval = 100
        # Track if we are in stall mode to avoid repeated adjustments
        self._stall_active = False

        # Path for the current sensor database. Default to SENSOR_DB_DEFAULT.
        self._sensor_db_path = SENSOR_DB_DEFAULT

        # Controllo remoto da chassis (attivo solo se lanciato dal root con env sync).
        self._sync_agent = None
        self._sync_remote_active = False
        self._sync_arm_requested = False

        # UI
        self._build_ui()
        self._connect_signals()

        # Load persistent configuration (if available)
        try:
            self._load_config()
        except Exception:
            pass

        # inizializzazione
        self.refresh_devices()

        # Start backlog monitoring timer
        self._backlog_timer.start()

        # Avvia l'agent solo in modalita chassis-control.
        self._init_sync_agent()

    # ----------------------------- Build UI -----------------------------
    def _build_ui(self):
        central = QtWidgets.QWidget()
        self.setCentralWidget(central)
        main = QtWidgets.QVBoxLayout(central)

        # Riga superiore: rileva + device + frequenza campionamento + definisci risorse
        top = QtWidgets.QHBoxLayout()
        # Pulsante per rilevare le schede NI presenti
        self.btnRefresh = QtWidgets.QPushButton("Rileva schede")
        top.addWidget(self.btnRefresh)
        # Etichetta e combobox per il dispositivo NI
        top.addWidget(QtWidgets.QLabel("Dispositivo:"))
        self.cmbDevice = QtWidgets.QComboBox()
        top.addWidget(self.cmbDevice, 1)
        # Campo di input per la frequenza di campionamento per canale
        top.addWidget(QtWidgets.QLabel("Fs [Hz]:"))
        self.rateEdit = QtWidgets.QLineEdit()
        # Imposta dimensione fissa per il campo del rate
        self.rateEdit.setFixedWidth(80)
        # Se non impostato, mostra "Max" come suggerimento
        self.rateEdit.setPlaceholderText("Max")
        top.addWidget(self.rateEdit)
        # Pulsante per definire i sensori/risorse
        self.btnDefineTypes = QtWidgets.QPushButton("Definisci Tipo Risorsa")
        top.addWidget(self.btnDefineTypes)
        # Pulsanti per salvare e caricare workspace
        self.btnSaveWorkspace = QtWidgets.QPushButton("Salva workspace")
        self.btnLoadWorkspace = QtWidgets.QPushButton("Carica workspace")
        top.addWidget(self.btnSaveWorkspace)
        top.addWidget(self.btnLoadWorkspace)
        # Allineamento a destra per riempire lo spazio residuo
        main.addLayout(top)

        # Tabs
        self.tabs = QtWidgets.QTabWidget()
        main.addWidget(self.tabs, 1)

        # Tab Canali: tabella
        tabTable = QtWidgets.QWidget()
        v = QtWidgets.QVBoxLayout(tabTable)
        self.table = QtWidgets.QTableWidget(0, 7)
        self.table.setHorizontalHeaderLabels([
            "Abilita", "Canale fisico", "Tipo risorsa", "Nome canale",
            "Valore istantaneo", "Azzeramento", "Valore azzerato"
        ])
        self.table.horizontalHeader().setStretchLastSection(True)
        v.addWidget(self.table)
        self.tabs.addTab(tabTable, "Canali")

        # Tab Grafici: sotto-tab (chart + instant)
        tabPlots = QtWidgets.QTabWidget()

        self.tabChart = QtWidgets.QWidget()
        vchart = QtWidgets.QVBoxLayout(self.tabChart)
        self.pgChart = pg.PlotWidget(title="Chart concatenato (decimato)")
        self._chart_legend = pg.LegendItem()
        self._chart_legend.setParentItem(self.pgChart.getPlotItem().graphicsItem())
        self._chart_legend.anchor((0, 1), (0, 1), offset=(10, -10))
        vchart.addWidget(self.pgChart, 1)
        # Etichetta per mostrare il valore medio di ciascun canale attivo
        self.lblAvgChart = QtWidgets.QLabel("")
        # Riduce leggermente la dimensione del carattere per la stringa di media
        try:
            fnt_avg = self.lblAvgChart.font()
            fnt_avg.setPointSize(max(8, fnt_avg.pointSize() - 1))
            self.lblAvgChart.setFont(fnt_avg)
        except Exception:
            pass
        self.lblAvgChart.setWordWrap(True)
        vchart.addWidget(self.lblAvgChart)
        hctrl = QtWidgets.QHBoxLayout()
        self.btnClearChart = QtWidgets.QPushButton("Pulizia grafico")
        hctrl.addStretch(1)
        hctrl.addWidget(self.btnClearChart)
        vchart.addLayout(hctrl)
        tabPlots.addTab(self.tabChart, "Chart concatenato")

        self.tabInstant = QtWidgets.QWidget()
        vinst = QtWidgets.QVBoxLayout(self.tabInstant)
        self.pgInstant = pg.PlotWidget(title="Ultimo blocco (non concatenato)")
        self._instant_legend = pg.LegendItem()
        self._instant_legend.setParentItem(self.pgInstant.getPlotItem().graphicsItem())
        self._instant_legend.anchor((0, 1), (0, 1), offset=(10, -10))
        vinst.addWidget(self.pgInstant, 1)
        tabPlots.addTab(self.tabInstant, "Blocchi istantanei")

        self.tabs.addTab(tabPlots, "Grafici")

        # Barra salvataggio in basso
        bottom = QtWidgets.QHBoxLayout()
        self.txtSaveDir = QtWidgets.QLineEdit(self._save_dir)
        self.btnBrowseDir = QtWidgets.QPushButton("Sfoglia cartella...")
        self.txtBaseName = QtWidgets.QLineEdit(self._base_filename)
        # SpinBox per impostare la dimensione del buffer in RAM (MB) per il salvataggio
        self.spinRam = QtWidgets.QSpinBox()
        # Limiti ragionevoli: da 10 MB fino a 16 GB
        self.spinRam.setRange(10, 16384)
        # Valore di default basato sul limite corrente dell'acquisition manager
        try:
            _u, _lim = self.acq.get_memory_usage()
            self.spinRam.setValue(max(1, int(_lim / (1024 * 1024))))
        except Exception:
            self.spinRam.setValue(500)
        self.spinRam.setSuffix(" MB")
        self.spinRam.setSingleStep(50)
        self.btnStart = QtWidgets.QPushButton("Salva dati")            # passa a "Salvo in (xx s)?â€
        self.btnStop = QtWidgets.QPushButton("Stop e ricomponi...")
        self.btnStop.setEnabled(False)

        bottom.addWidget(QtWidgets.QLabel("Percorso salvataggio:"))
        bottom.addWidget(self.txtSaveDir, 1)
        bottom.addWidget(self.btnBrowseDir)
        bottom.addSpacing(12)
        bottom.addWidget(QtWidgets.QLabel("Nome file:"))
        bottom.addWidget(self.txtBaseName)
        # Controllo per la dimensione del buffer in RAM
        bottom.addSpacing(12)
        bottom.addWidget(QtWidgets.QLabel("Buffer RAM:"))
        bottom.addWidget(self.spinRam)
        bottom.addStretch(1)
        bottom.addWidget(self.btnStart)
        bottom.addWidget(self.btnStop)
        main.addLayout(bottom)

        # Timer per l'aggiornamento dei grafici.  Un intervallo pi? lungo
        # (100 ms invece dei 50 ms precedenti) riduce il numero di
        # conversioni da deque a array e di chiamate a setData, riducendo
        # l'uso di memoria nel lungo periodo.  Questo valore pu? essere
        # ulteriormente modificato dinamicamente dalla routine di controllo
        # dello stall.
        self.guiTimer = QtCore.QTimer(self)
        self.guiTimer.setInterval(100)
        self.guiTimer.timeout.connect(self._refresh_plots)

        # Status bar + etichetta sempre visibile con rate
        self.statusBar = QtWidgets.QStatusBar()
        self.setStatusBar(self.statusBar)
        self.lblRateInfo = QtWidgets.QLabel("-")
        our_font = self.lblRateInfo.font()
        our_font.setPointSize(9)
        self.lblRateInfo.setFont(our_font)
        self.statusBar.addPermanentWidget(self.lblRateInfo)

    # ------------------------- Configuration persistence -------------------------
    def _load_config(self):
        """
        Load persistent settings from a JSON file if it exists. The settings
        include the last used save directory, base filename, memory buffer
        size and sampling rate. This method should be called after the UI
        widgets have been created so that values can be applied.
        """
        if not os.path.isfile(CONFIG_FILE):
            return
        try:
            with open(CONFIG_FILE, "r", encoding="utf-8") as f:
                cfg = json.load(f)
        except Exception:
            return
        # Apply known settings if present
        try:
            sd = cfg.get("save_dir")
            if sd:
                self._save_dir = sd
                self.txtSaveDir.setText(sd)
        except Exception:
            pass
        try:
            bn = cfg.get("base_filename")
            if bn:
                self._base_filename = bn
                self.txtBaseName.setText(bn)
        except Exception:
            pass
        try:
            ram_mb = int(cfg.get("ram_mb", 0))
            if ram_mb > 0:
                self.spinRam.setValue(ram_mb)
        except Exception:
            pass
        try:
            fs = cfg.get("fs")
            if fs:
                # Show the saved sampling rate in the rateEdit field
                self.rateEdit.setText(str(fs))
        except Exception:
            pass

    def _save_config(self):
        """
        Save current UI settings to a JSON configuration file. Only basic
        values (save directory, base filename, buffer size and sample rate)
        are persisted. This method is called automatically on application
        close.
        """
        cfg = {}
        try:
            cfg["save_dir"] = self.txtSaveDir.text().strip()
        except Exception:
            pass
        try:
            cfg["base_filename"] = self.txtBaseName.text().strip()
        except Exception:
            pass
        try:
            cfg["ram_mb"] = int(self.spinRam.value())
        except Exception:
            pass
        try:
            txt = self.rateEdit.text().strip()
            if txt:
                cfg["fs"] = float(txt)
        except Exception:
            pass
        try:
            with open(CONFIG_FILE, "w", encoding="utf-8") as f:
                json.dump(cfg, f, indent=2)
        except Exception:
            pass

    def closeEvent(self, event):
        """
        Reimplement the close event to persist settings before the
        application terminates.
        """
        try:
            self._save_config()
        except Exception:
            pass
        super().closeEvent(event)

    # -------------------------- Backlog/Disk stall check --------------------------
    def _check_backlog(self):
        """
        Periodically monitor the estimated disk write backlog. If the backlog
        exceeds a predefined threshold, a warning is shown in the status bar
        and the chart refresh interval is reduced to minimize CPU overhead.
        When the backlog drops below the threshold, the refresh interval is
        restored and the warning message cleared.
        """
        try:
            # Only monitor when recording is active
            if not self.acq.recording_enabled:
                # When not recording, ensure GUI timer uses default interval and clear warning
                if self._stall_active:
                    self.guiTimer.setInterval(self._default_gui_interval)
                    self.statusBar.showMessage("")
                    self._stall_active = False
                return
            backlog_mb = 0.0
            try:
                backlog_mb = float(self.acq.get_backlog_estimate())
            except Exception:
                backlog_mb = 0.0
            # Threshold for disk stall warning (MB)
            threshold_mb = 200.0
            if backlog_mb >= threshold_mb and not self._stall_active:
                # Enter stall mode: slow down UI updates and display warning
                self._stall_active = True
                # Reduce chart refresh frequency to ease CPU and I/O pressure
                try:
                    self.guiTimer.setInterval(max(self._default_gui_interval, 200))
                except Exception:
                    pass
                msg = f"DISK STALL: backlog {backlog_mb:.0f} MB. Rallento l'aggiornamento grafici per evitare perdite."
                self.statusBar.showMessage(msg)
            elif backlog_mb < threshold_mb and self._stall_active:
                # Exit stall mode
                self._stall_active = False
                try:
                    self.guiTimer.setInterval(self._default_gui_interval)
                except Exception:
                    pass
                self.statusBar.showMessage("")
        except Exception:
            pass

    def _connect_signals(self):
        # pulsanti
        self.btnRefresh.clicked.connect(self.refresh_devices)
        self.btnBrowseDir.clicked.connect(self._choose_folder)
        self.btnStart.clicked.connect(self._on_start_saving)
        self.btnStop.clicked.connect(self._on_stop)
        self.btnClearChart.clicked.connect(self._clear_chart)
        self.btnDefineTypes.clicked.connect(self._open_resource_manager)

        # collegamenti per salvataggio/caricamento workspace
        try:
            self.btnSaveWorkspace.clicked.connect(self._save_workspace)
            self.btnLoadWorkspace.clicked.connect(self._load_workspace)
        except Exception:
            pass

        # tabella: prima puliamo eventuali collegamenti generici che
        # potrebbero riconfigurare anche quando si rinomina
        try:
            self.table.cellChanged.disconnect()
        except Exception:
            pass
        try:
            self.table.itemChanged.disconnect()
        except Exception:
            pass
        self.table.itemChanged.connect(self._on_table_item_changed)

        self.cmbDevice.currentIndexChanged.connect(self._on_device_changed)

        # Aggiorna la frequenza di campionamento quando l'utente conferma il valore
        try:
            self.rateEdit.editingFinished.connect(self._on_rate_edit_finished)
        except Exception:
            pass

        # callback dal core (rimappati in segnali Qt)
        self.channelValueUpdated.connect(self._update_table_value)
        self.sigInstantBlock.connect(self._slot_instant_block)
        self.sigChartPoints.connect(self._slot_chart_points)

        self.acq.on_channel_value = lambda name, val: self.channelValueUpdated.emit(name, val)
        self.acq.on_new_instant_block = lambda t, ys, names: self.sigInstantBlock.emit(t, ys, names)
        self.acq.on_new_chart_points = lambda t_pts, ys_pts, names: self.sigChartPoints.emit(t_pts, ys_pts, names)

    def _init_sync_agent(self):
        if ModuleSyncAgent is None:
            return
        try:
            agent = ModuleSyncAgent(self)
        except Exception:
            return
        if not agent.is_active():
            return

        self._sync_agent = agent
        self._sync_agent.register_handler("APPLY_CHASSIS_CONFIG", self._sync_cmd_apply_chassis_config)
        self._sync_agent.register_handler("PREPARE_SAVE", self._sync_cmd_prepare_save)
        self._sync_agent.register_handler("CONFIGURE_SYNC", self._sync_cmd_configure_sync)
        self._sync_agent.register_handler("ARM_ACQUISITION", self._sync_cmd_arm_acquisition)
        self._sync_agent.register_handler("START_SYNC", self._sync_cmd_start_sync)
        self._sync_agent.register_handler("START_SAVE", self._sync_cmd_start_save)
        self._sync_agent.register_handler("STOP_AND_MERGE", self._sync_cmd_stop_and_merge)
        self._sync_agent.register_handler("UNLOCK_UI", self._sync_cmd_unlock_ui)
        self._sync_agent.register_handler("ABORT_PREPARED", self._sync_cmd_abort_prepared)
        self._sync_agent.start(
            {
                "board": "NI9201",
                "pid": int(os.getpid()),
                "device_name": str(self._forced_device_name_from_env() or ""),
            }
        )

    def _is_current_device_simulated(self) -> bool:
        txt = str(self.cmbDevice.currentText() or "")
        return "[SIMULATED]" in txt.upper()

    def _set_remote_control_lock(self, lock: bool):
        lock = bool(lock)
        self._set_table_lock(lock)
        self.txtSaveDir.setEnabled(not lock)
        self.btnBrowseDir.setEnabled(not lock)
        self.txtBaseName.setEnabled(not lock)
        self.spinRam.setEnabled(not lock)
        self.rateEdit.setEnabled(not lock)
        self.btnDefineTypes.setEnabled(not lock)
        self.btnSaveWorkspace.setEnabled(not lock)
        self.btnLoadWorkspace.setEnabled(not lock)
        forced_device_name = self._forced_device_name_from_env()
        self.cmbDevice.setEnabled((not lock) and (not bool(forced_device_name)))
        self.btnRefresh.setEnabled((not lock) and (not bool(forced_device_name)))
        if lock:
            self.btnStart.setEnabled(False)
            self.btnStop.setEnabled(False)
        else:
            self.btnStart.setEnabled(not bool(self.acq.recording_enabled))
            self.btnStop.setEnabled(bool(self.acq.recording_enabled))

    def _run_without_message_boxes(self, fn):
        orig_info = QtWidgets.QMessageBox.information
        orig_warn = QtWidgets.QMessageBox.warning
        orig_crit = QtWidgets.QMessageBox.critical

        def _silent(*_args, **_kwargs):
            return QtWidgets.QMessageBox.Ok

        try:
            QtWidgets.QMessageBox.information = _silent
            QtWidgets.QMessageBox.warning = _silent
            QtWidgets.QMessageBox.critical = _silent
            return fn()
        finally:
            QtWidgets.QMessageBox.information = orig_info
            QtWidgets.QMessageBox.warning = orig_warn
            QtWidgets.QMessageBox.critical = orig_crit

    def _find_latest_tdms(self) -> str:
        base_dir = str(self._save_dir or "").strip()
        if not base_dir or not os.path.isdir(base_dir):
            return ""
        files = glob.glob(os.path.join(base_dir, "*.tdms"))
        if not files:
            return ""
        try:
            files.sort(key=lambda p: os.path.getmtime(p))
        except Exception:
            files.sort()
        return files[-1]

    def _sync_cmd_apply_chassis_config(self, payload: Dict[str, Any]) -> Dict[str, Any]:
        save_dir = str(payload.get("save_dir", "") or "").strip()
        base_name = str(payload.get("base_filename", "") or "").strip()
        fs_hz = float(payload.get("fs_hz", 0.0) or 0.0)
        ram_mb = payload.get("ram_mb", None)

        if save_dir:
            self.txtSaveDir.setText(save_dir)
        if base_name:
            if not base_name.lower().endswith(".tdms"):
                base_name += ".tdms"
            self.txtBaseName.setText(base_name)
        if ram_mb is not None:
            try:
                ram_i = int(float(ram_mb))
                ram_i = max(self.spinRam.minimum(), min(self.spinRam.maximum(), ram_i))
                self.spinRam.setValue(ram_i)
            except Exception:
                pass
        if fs_hz > 0:
            self.rateEdit.setText(str(int(round(fs_hz))))
            self._run_without_message_boxes(self._on_rate_edit_finished)

        return {
            "device_name": str((self.cmbDevice.currentData() or self.cmbDevice.currentText() or "").strip()),
            "is_simulated": self._is_current_device_simulated(),
        }

    def _sync_cmd_prepare_save(self, _payload: Dict[str, Any]) -> Dict[str, Any]:
        if not self._device_ready:
            raise RuntimeError("Dispositivo non pronto.")
        phys, _labels = self._enabled_phys_and_labels()
        if not phys:
            raise RuntimeError("Nessun canale abilitato.")
        if not bool(getattr(self.acq, "_running", False)):
            self._run_without_message_boxes(self._update_acquisition_from_table)
        if not bool(getattr(self.acq, "_running", False)):
            raise RuntimeError("Acquisizione non avviata.")
        return {"channels": len(phys)}

    def _sync_cmd_configure_sync(self, payload: Dict[str, Any]) -> Dict[str, Any]:
        fs_hz = float(payload.get("fs_hz", 0.0) or 0.0)
        if fs_hz > 0:
            self.rateEdit.setText(str(int(round(fs_hz))))
            self._run_without_message_boxes(self._on_rate_edit_finished)
        return {
            "hardware_supported": False,
            "is_simulated": self._is_current_device_simulated(),
        }

    def _sync_cmd_arm_acquisition(self, payload: Dict[str, Any]) -> Dict[str, Any]:
        fs_hz = float(payload.get("fs_hz", 0.0) or 0.0)
        if fs_hz > 0:
            self.rateEdit.setText(str(int(round(fs_hz))))
            self._run_without_message_boxes(self._on_rate_edit_finished)
        try:
            if bool(getattr(self.acq, "_running", False)):
                self.acq.stop()
        except Exception:
            pass
        phys, _labels = self._enabled_phys_and_labels()
        if not phys:
            raise RuntimeError("Nessun canale abilitato per arm.")
        self._sync_arm_requested = True
        return {"armed": True, "channels": len(phys)}

    def _sync_cmd_start_sync(self, payload: Dict[str, Any]) -> Dict[str, Any]:
        if not self._sync_arm_requested:
            raise RuntimeError("Modulo non armato.")
        start_epoch_ns = int(payload.get("start_epoch_ns", 0) or 0)
        if start_epoch_ns > 0:
            while True:
                now = time.time_ns()
                dt_ns = start_epoch_ns - now
                if dt_ns <= 0:
                    break
                if dt_ns > 3_000_000:
                    time.sleep((dt_ns - 1_000_000) / 1_000_000_000.0)
                else:
                    break
            while time.time_ns() < start_epoch_ns:
                pass
        self._run_without_message_boxes(self._update_acquisition_from_table)
        if not bool(getattr(self.acq, "_running", False)):
            raise RuntimeError("Start sincronizzato fallito.")
        self._sync_arm_requested = False
        return {"running": True, "start_ns": time.time_ns()}

    def _sync_cmd_start_save(self, _payload: Dict[str, Any]) -> Dict[str, Any]:
        self._sync_remote_active = True
        self._set_remote_control_lock(True)
        self._run_without_message_boxes(self._on_start_saving)
        if not bool(self.acq.recording_enabled):
            self._sync_remote_active = False
            self._set_remote_control_lock(False)
            raise RuntimeError("Salvataggio non avviato.")
        return {"recording": True}

    def _sync_cmd_stop_and_merge(self, _payload: Dict[str, Any]) -> Dict[str, Any]:
        before = self._find_latest_tdms()
        self._run_without_message_boxes(self._on_stop)
        after = self._find_latest_tdms()
        self._sync_remote_active = False
        self._sync_arm_requested = False
        return {"recording": bool(self.acq.recording_enabled), "final_tdms": after or before}

    def _sync_cmd_unlock_ui(self, _payload: Dict[str, Any]) -> Dict[str, Any]:
        self._sync_remote_active = False
        self._sync_arm_requested = False
        self._set_remote_control_lock(False)
        return {"unlocked": True}

    def _sync_cmd_abort_prepared(self, _payload: Dict[str, Any]) -> Dict[str, Any]:
        try:
            self.acq.set_recording(False)
        except Exception:
            pass
        try:
            self.acq.stop()
        except Exception:
            pass
        self._sync_remote_active = False
        self._sync_arm_requested = False
        self._set_remote_control_lock(False)
        return {"aborted": True}

    # ----------------------------- Devices -----------------------------
    def refresh_devices(self):
        """
        Popola la combo dispositivi includendo anche i moduli simulati.
        Se sono presenti piu NI-9201, apre un dialog per scegliere:
        mostra nome modulo, chassis e tag [SIMULATED].
        """
        try:
            metas = self.acq.list_ni9201_devices_meta()
        except AttributeError:
            names = self.acq.list_ni9201_devices()
            metas = [{"name": n, "product_type": "NI 9201", "is_simulated": False,
                      "chassis": n.split("Mod")[0] if "Mod" in n else ""} for n in names]
        except Exception:
            metas = []

        metas, preferred_idx = self._prioritize_preferred_devices(metas)
        forced_device_name = self._forced_device_name_from_env()
        if forced_device_name:
            forced_idx = -1
            for idx, meta in enumerate(metas):
                if str(meta.get("name", "") or "").strip() == forced_device_name:
                    forced_idx = idx
                    break

            if forced_idx < 0:
                QtWidgets.QMessageBox.critical(
                    self,
                    "Dispositivo non disponibile",
                    f'Il dispositivo assegnato "{forced_device_name}" non e disponibile.',
                )
                self._abort_startup_on_device_cancel()
                return

            if forced_idx > 0:
                ordered = list(metas)
                target = ordered.pop(forced_idx)
                ordered.insert(0, target)
                metas = ordered
                preferred_idx = 0

        self.cmbDevice.blockSignals(True)
        self.cmbDevice.clear()
        for m in metas:
            name = m.get("name", "?")
            pt = m.get("product_type", "")
            ch = m.get("chassis", "")
            sim = " [SIMULATED]" if m.get("is_simulated") else ""
            label = f"{name} - {pt} - ({ch}){sim}" if ch else f"{name} - {pt}{sim}"
            self.cmbDevice.addItem(label, userData=name)
        self.cmbDevice.blockSignals(False)

        self._device_ready = bool(metas)

        if not metas:
            QtWidgets.QMessageBox.information(self, "Nessun dispositivo",
                                              "Nessun NI-9201 trovato. Verifica in NI-MAX (anche simulati).")
            if forced_device_name:
                self._abort_startup_on_device_cancel()
                return
        elif forced_device_name:
            self.cmbDevice.setCurrentIndex(0)
        elif len(metas) == 1:
            self.cmbDevice.setCurrentIndex(0)
        else:
            chosen = self._prompt_device_choice(metas, preferred_idx=preferred_idx)
            if chosen:
                for i in range(self.cmbDevice.count()):
                    if self.cmbDevice.itemData(i) == chosen:
                        self.cmbDevice.setCurrentIndex(i)
                        break
            else:
                self._abort_startup_on_device_cancel()
                return

        # Se il processo e stato avviato per un device specifico, vincola la selezione.
        self.cmbDevice.setEnabled(not bool(forced_device_name))
        self.btnRefresh.setEnabled(not bool(forced_device_name))

        self._populate_table()
        self._populate_type_column()
        self._recompute_all_calibrations()
        self.lblRateInfo.setText("-")

    def _abort_startup_on_device_cancel(self):
        # Chiusura pulita del modulo: evita sys.exit immediato mentre Qt
        # sta ancora gestendo oggetti/eventi.
        self._device_ready = False
        QtCore.QTimer.singleShot(0, self.close)

    def _preferred_chassis_from_env(self):
        alias = str(os.environ.get("CDAQ_SELECTED_ALIAS", "") or "").strip()
        raw = str(os.environ.get("CDAQ_SELECTED_SIMULATED", "") or "").strip().lower()

        is_sim = None
        if raw in ("1", "true", "yes"):
            is_sim = True
        elif raw in ("0", "false", "no"):
            is_sim = False

        return alias, is_sim

    def _forced_device_name_from_env(self):
        return str(os.environ.get("CDAQ_TARGET_DEVICE_NAME", "") or "").strip()

    def _prioritize_preferred_devices(self, metas):
        if not metas:
            return metas, 0

        preferred_alias, preferred_is_sim = self._preferred_chassis_from_env()
        if not preferred_alias:
            return metas, 0

        preferred_idx = -1
        target_alias = preferred_alias.lower()

        for idx, meta in enumerate(metas):
            chassis_alias = str(meta.get("chassis", "") or "").strip().lower()
            if chassis_alias != target_alias:
                continue
            is_sim = bool(meta.get("is_simulated"))
            if preferred_is_sim is None or is_sim == preferred_is_sim:
                preferred_idx = idx
                break

        if preferred_idx <= 0:
            return metas, 0

        ordered = list(metas)
        preferred_meta = ordered.pop(preferred_idx)
        ordered.insert(0, preferred_meta)
        return ordered, 0

    def _prompt_device_choice(self, metas, preferred_idx=0):
        items = []
        for m in metas:
            name = m.get("name", "?")
            pt = m.get("product_type", "")
            ch = m.get("chassis", "")
            sim = " [SIMULATED]" if m.get("is_simulated") else ""
            label = f"{name} - {pt} - ({ch}){sim}" if ch else f"{name} - {pt}{sim}"
            items.append(label)

        dialog = QtWidgets.QDialog(self)
        dialog.setWindowTitle("Seleziona dispositivo")
        layout = QtWidgets.QVBoxLayout(dialog)
        layout.addWidget(QtWidgets.QLabel("Sono presenti piu moduli NI-9201.\nScegli quello da usare:"))

        cmb = QtWidgets.QComboBox(dialog)
        cmb.addItems(items)
        if cmb.count() > 0:
            preferred_idx = max(0, min(int(preferred_idx or 0), cmb.count() - 1))
            cmb.setCurrentIndex(preferred_idx)
        else:
            preferred_idx = 0
        layout.addWidget(cmb)

        buttons = QtWidgets.QDialogButtonBox(
            QtWidgets.QDialogButtonBox.Ok | QtWidgets.QDialogButtonBox.Cancel, parent=dialog
        )
        buttons.accepted.connect(dialog.accept)
        buttons.rejected.connect(dialog.reject)
        layout.addWidget(buttons)

        if dialog.exec_() != QtWidgets.QDialog.Accepted:
            return None

        chosen_idx = cmb.currentIndex()
        if chosen_idx < 0 or chosen_idx >= len(metas):
            return None
        return str(metas[chosen_idx].get("name", "") or "")

    def _on_device_changed(self, _):
        self._stop_acquisition_ui_only()
        self._reset_plots()
        self.lblRateInfo.setText("-")

    # ----------------------------- Sensor defs -----------------------------
    def _read_sensor_defs(self) -> dict:
        """
        Legge il file XML (multi-punti o 2-punti) e ritorna dict:
            name -> {unit, a, b}
        """
        defs = {}
        # Use the current sensor DB path if available; fallback to default
        try:
            p = self._sensor_db_path
        except Exception:
            p = SENSOR_DB_DEFAULT
        if not os.path.isfile(p):
            return defs
        # Determine supported DAQ models for this application.
        # Il programma deve caricare solo i sensori compatibili con NI9201.
        board_tag = "NI9201"
        try:
            tree = ET.parse(p)
            root = tree.getroot()
            for s in root.findall(XML_ITEM):
                try:
                    name = (s.findtext(XML_NAME, default="") or "").strip()
                except Exception:
                    continue
                if not name:
                    continue
                # Read unit and supportedDAQ (if present)
                try:
                    unit = (s.findtext(XML_UNIT, default="") or "").strip()
                except Exception:
                    unit = ""
                # Check supportedDAQ
                try:
                    supported = (s.findtext("supportedDAQ", default="") or "").strip()
                    # If a supportedDAQ tag is present, ensure NI9201 appears among the comma-separated values
                    if supported:
                        items = [x.strip().upper() for x in supported.split(",") if x.strip()]
                        # Se NI9201 non ? tra gli elementi, salta questo sensore
                        if all(item != board_tag for item in items):
                            continue
                    else:
                        # Se il tag non esiste o ? vuoto, non includere il sensore
                        continue
                except Exception:
                    # In caso di errore, non includere il sensore
                    continue
                # nuovo schema multi-punti
                cal = s.find(XML_CAL)
                if cal is not None:
                    V, X = [], []
                    for pt in cal.findall(XML_POINT):
                        try:
                            v = float(pt.get("volt", "nan"))
                            x = float(pt.get("value", "nan"))
                        except Exception:
                            continue
                        if np.isfinite(v) and np.isfinite(x):
                            V.append(v); X.append(x)
                    if len(V) >= 2:
                        A = np.vstack([np.asarray(V), np.ones(len(V))]).T
                        a, b = np.linalg.lstsq(A, np.asarray(X), rcond=None)[0]
                        defs[name] = {"unit": unit, "a": float(a), "b": float(b)}
                        continue
                # compat vecchio schema (2 punti)
                def _f(tag):
                    try: return float(s.findtext(tag, default="0") or "0")
                    except Exception: return 0.0
                v1v = _f(XML_V1V); x1 = _f(XML_V1)
                v2v = _f(XML_V2V); x2 = _f(XML_V2)
                if abs(v2v - v1v) > 1e-12:
                    a = (x2 - x1) / (v2v - v1v)
                    b = x1 - a * v1v
                else:
                    a, b = 1.0, 0.0
                defs[name] = {"unit": unit, "a": a, "b": b}
        except Exception:
            pass
        return defs

    def _populate_type_column(self):
        """Popola 'Tipo risorsa' con: Voltage + nomi da Sensor DB."""
        # Read sensor definitions filtered by supported DAQ and use keys as names
        names = []
        try:
            defs = self._read_sensor_defs()
            names = sorted(defs.keys())
        except Exception:
            names = []
        for r in range(self.table.rowCount()):
            cmb: QtWidgets.QComboBox = self.table.cellWidget(r, COL_TYPE)
            if not isinstance(cmb, QtWidgets.QComboBox):
                continue
            cur = cmb.currentText()
            cmb.blockSignals(True)
            cmb.clear()
            cmb.setEditable(False)
            cmb.addItem("Voltage")
            for n in names:
                cmb.addItem(n)
            if cur and cur != "Voltage":
                idx = cmb.findText(cur)
                if idx >= 0:
                    cmb.setCurrentIndex(idx)
                else:
                    cmb.setCurrentIndex(0)
            else:
                cmb.setCurrentIndex(0)
            cmb.blockSignals(False)

    def _recompute_all_calibrations(self):
        defs = self._read_sensor_defs()
        for r in range(self.table.rowCount()):
            phys = self.table.item(r, COL_PHYS).text().strip()
            cmb: QtWidgets.QComboBox = self.table.cellWidget(r, COL_TYPE)
            chosen = cmb.currentText().strip() if cmb else "Voltage"
            if chosen == "Voltage" or chosen == "":
                self._calib_by_phys[phys] = {"unit":"", "a":1.0, "b":0.0}
            else:
                self._calib_by_phys[phys] = defs.get(chosen, {"unit":"", "a":1.0, "b":0.0})
        self._rebuild_legends()
        self._push_sensor_map_to_core()

    def _push_sensor_map_to_core(self):
        mapping = {}
        for r in range(self.table.rowCount()):
            phys = self.table.item(r, COL_PHYS).text().strip()
            base_label = self.table.item(r, COL_LABEL).text().strip() or phys
            cal = self._calib_by_phys.get(phys, {"unit":"", "a":1.0, "b":0.0})
            unit = cal.get("unit",""); a = float(cal.get("a",1.0)); b = float(cal.get("b",0.0))
            display_label = f"{base_label} [{unit}]" if unit else base_label
            mapping[phys] = {
                "unit": unit, "a": a, "b": b,
                "sensor_name": self._sensor_type_by_phys.get(phys, "Voltage"),
                "display_label": display_label
            }
        try:
            self.acq.set_sensor_map(mapping)
        except Exception:
            pass

    # ----------------------------- Tabella -----------------------------
    def _populate_table(self):
        self._building_table = True
        self.table.setRowCount(8)
        for i in range(8):
            phys = f"ai{i}"

            # Abilita
            it = QtWidgets.QTableWidgetItem()
            it.setFlags(it.flags() | QtCore.Qt.ItemIsUserCheckable)
            it.setCheckState(QtCore.Qt.Unchecked)
            self.table.setItem(i, COL_ENABLE, it)

            # Canale fisico
            physItem = QtWidgets.QTableWidgetItem(phys)
            physItem.setFlags(physItem.flags() & ~QtCore.Qt.ItemIsEditable)
            self.table.setItem(i, COL_PHYS, physItem)

            # Tipo risorsa (selezione vincolata ai sensori supportati + Voltage)
            cmbType = QtWidgets.QComboBox()
            cmbType.setEditable(False)
            cmbType.addItem("Voltage")
            cmbType.currentTextChanged.connect(lambda _t, row=i: self._type_changed_for_row(row))
            self.table.setCellWidget(i, COL_TYPE, cmbType)

            # Nome canale (label utente)
            labelItem = QtWidgets.QTableWidgetItem(self._label_by_phys.get(phys, phys))
            self.table.setItem(i, COL_LABEL, labelItem)

            # Valore istantaneo (solo display)
            valItem = QtWidgets.QTableWidgetItem("-")
            valItem.setFlags(valItem.flags() & ~QtCore.Qt.ItemIsUserCheckable & ~QtCore.Qt.ItemIsEditable)
            self.table.setItem(i, COL_VALUE, valItem)

            # Azzeramento
            btnZero = QtWidgets.QPushButton("Azzeramento")
            btnZero.clicked.connect(lambda _, c=phys: self._on_zero_button_clicked(c))
            self.table.setCellWidget(i, COL_ZERO_BTN, btnZero)

            # Valore azzerato (display/placeholder)
            zeroItem = QtWidgets.QTableWidgetItem("0.0")
            zeroItem.setFlags(zeroItem.flags() & ~QtCore.Qt.ItemIsEditable)
            self.table.setItem(i, COL_ZERO_VAL, zeroItem)
        self._building_table = False

    def _type_changed_for_row(self, row: int):
        phys = self.table.item(row, COL_PHYS).text().strip()
        cmb: QtWidgets.QComboBox = self.table.cellWidget(row, COL_TYPE)
        chosen = cmb.currentText().strip() if cmb else "Voltage"
        self._sensor_type_by_phys[phys] = chosen

        if chosen == "Voltage" or chosen == "":
            calib = {"unit":"", "a":1.0, "b":0.0}
        else:
            defs = self._read_sensor_defs()
            calib = defs.get(chosen, {"unit":"", "a":1.0, "b":0.0})

        self._calib_by_phys[phys] = calib
        self._rebuild_legends()
        self._push_sensor_map_to_core()

    def _push_channel_labels_to_core(self):
        """Invia al core i nomi canale (per ogni riga della tabella)."""
        n = self.table.rowCount()
        for r in range(n):
            phys = self.table.item(r, COL_PHYS).text() if self.table.item(r, COL_PHYS) else ""
            lbl_item = self.table.item(r, COL_LABEL)
            label = lbl_item.text().strip() if lbl_item else ""
            if not label:
                label = phys
            try:
                self.acq.set_ui_name_for_phys(phys, label)
            except Exception:
                pass

    def _on_table_item_changed(self, item: QtWidgets.QTableWidgetItem):
        if item is None:
            return

        # evita rientri durante build/aggiornamenti programmatici
        if self._building_table or self._auto_change:
            return

        row = item.row()
        col = item.column()

        if col == COL_LABEL:
            # --- Rinominare NON deve toccare l'acquisizione ---
            phys = self.table.item(row, COL_PHYS).text().strip() if self.table.item(row, COL_PHYS) else ""
            # Etichetta digitata dall'utente (fallback al nome fisico se vuota)
            new_label = (item.text() or "").strip() or phys

            # Deduplica il nuovo nome rispetto agli altri canali.  Se esiste gi? un
            # altro canale con la stessa etichetta (ignorando la differenza
            # maiuscole/minuscole), appende un suffisso _2, _3, ... fino a trovare
            # un nome non in uso.  Questa logica evita ambiguit? quando i nomi
            # duplicati vengono usati per instradare i dati dal core alla UI.
            try:
                base = new_label
                if base:
                    # Raccogli tutte le etichette degli altri canali (case-insensitive)
                    existing = []
                    for r in range(self.table.rowCount()):
                        if r == row:
                            continue
                        it_lbl = self.table.item(r, COL_LABEL)
                        if it_lbl:
                            txt = (it_lbl.text() or "").strip()
                            if txt:
                                existing.append(txt.lower())
                    # Se il nuovo nome ? gi? presente, trova un suffisso libero
                    if base.lower() in existing:
                        suffix = 2
                        candidate = f"{base}_{suffix}"
                        while candidate.lower() in existing:
                            suffix += 1
                            candidate = f"{base}_{suffix}"
                        # Aggiorna la cella con il nome deduplicato evitando eventi di ricorsione
                        self._auto_change = True
                        item.setText(candidate)
                        self._auto_change = False
                        new_label = candidate
            except Exception:
                # In caso di errore durante la deduplicazione, continua con il nome originale
                pass

            # Aggiorna il mapping locale e le legende con l'etichetta (deduplicata)
            self._label_by_phys[phys] = new_label
            self._rebuild_legends()

            # Invia subito il nome canale deduplicato al core, in modo che i TDMS
            # utilizzino nomi univoci e coerenti.
            try:
                self.acq.set_ui_name_for_phys(phys, new_label)
            except Exception:
                pass

            # Opzionale: aggiorna l'etichetta della frequenza se l'acquisizione ? attiva.
            # Usiamo il flag interno _running invece dello stato del pulsante Stop,
            # poich? quest'ultimo viene abilitato solo durante il salvataggio.
            try:
                if getattr(self.acq, '_running', False):
                    self._update_rate_label(self._current_phys_order)
            except Exception:
                pass
            return  # <? importante: NON proseguire

        # altri casi che possono richiedere riconfigurazione
        if col == COL_ENABLE:
            self._update_acquisition_from_table()

    def _enabled_phys_and_labels(self):
        phys, labels = [], []
        for r in range(self.table.rowCount()):
            it = self.table.item(r, COL_ENABLE)
            if it and it.checkState() == QtCore.Qt.Checked:
                p = self.table.item(r, COL_PHYS).text().strip()
                l = self.table.item(r, COL_LABEL).text().strip() or p
                phys.append(p); labels.append(l)
        return phys, labels

    def _find_row_by_phys(self, phys: str):
        for r in range(self.table.rowCount()):
            if self.table.item(r, COL_PHYS).text().strip() == phys:
                return r
        return -1

    # ----------------------------- Start/Stop auto -----------------------------
    def _update_acquisition_from_table(self):
        if not self._device_ready:
            QtWidgets.QMessageBox.warning(self, "Attenzione", "Seleziona un dispositivo prima.")
            self._auto_change = True
            for r in range(self.table.rowCount()):
                it = self.table.item(r, COL_ENABLE)
                if it: it.setCheckState(QtCore.Qt.Unchecked)
            self._auto_change = False
            return

        # PRENDE SEMPRE IL "NAME" PULITO dal userData della combo
        device = (self.cmbDevice.currentData() or self.cmbDevice.currentText()).strip()
        phys, labels = self._enabled_phys_and_labels()

        if not phys:
            self._stop_acquisition_ui_only()
            self.lblRateInfo.setText("-")
            return

        # If the set of enabled channels has not changed and an acquisition is
        # currently running, simply update the rate label and return.  We no
        # longer rely on the state of the Stop/Recompose button here because
        # that button is only enabled when recording is active, not when the
        # acquisition is running.
        if phys == self._last_enabled_phys and getattr(self.acq, '_running', False):
            self._update_rate_label(phys)
            return

        # If an acquisition is already running, stop it before starting a new
        # one with the updated list of channels.  Use the internal running flag
        # rather than the Stop/Recompose button state.
        if getattr(self.acq, '_running', False):
            try:
                self.acq.stop()
            except Exception:
                pass

        ok = self.acq.start(device_name=device, ai_channels=phys, channel_names=labels)
        if not ok:
            QtWidgets.QMessageBox.critical(self, "Errore", "Impossibile avviare l'acquisizione.")
            return

        # Ensure that channel names used by the core are unique.  Duplicated labels
        # can cause the mapping from start names back to physical channels to be
        # ambiguous.  Use the acquisition manager helper to deduplicate labels.
        try:
            # set_channel_labels updates the internal _channel_names list with
            # unique names.  These names will be used for TDMS channels.  To
            # ensure that callbacks from the acquisition core provide these
            # deduplicated names as well, also update _start_channel_names.
            self.acq.set_channel_labels(labels)
            # Retrieve the sanitized names; fall back to the original list on error
            labels = list(self.acq._channel_names)
            # Update the start_channel_names so that callback events emit the
            # deduplicated names.  Without this assignment, the acquisition
            # core would continue to use the original (possibly duplicated)
            # names for callbacks, leading to ambiguous routing in the UI.
            try:
                self.acq._start_channel_names = labels[:]
            except Exception:
                pass
        except Exception:
            # In case of any error, keep the provided labels
            pass
        # Record the current order of physical channels and the labels used at
        # acquisition start.  These mappings are used to route incoming data
        # (start names) back to the correct physical channel.
        self._current_phys_order = phys[:]
        self._start_label_by_phys = dict(zip(phys, labels))
        self._last_enabled_phys = phys[:]

        # grafici
        self._reset_plots_curves()
        # Enable the Stop/Recompose button only when recording is active.  At this
        # point a new acquisition has just started but recording (salvataggio) has
        # not yet been enabled via the "Salva dati" button, so leave it disabled.
        try:
            self.btnStop.setEnabled(bool(self.acq.recording_enabled))
        except Exception:
            # Fallback: disable the button if we cannot read the recording state
            self.btnStop.setEnabled(False)
        if not self.guiTimer.isActive():
            self.guiTimer.start()

        self._update_rate_label(phys)
        self._push_sensor_map_to_core()

    def _update_rate_label(self, phys_list):
        try:
            labels = [self._label_by_phys.get(p, p) for p in phys_list]
            cur_per = (self.acq.current_rate_hz or 0) / 1e3
            cur_agg = (self.acq.current_agg_rate_hz or 0) / 1e3
            lim_single = (self.acq.max_single_rate_hz or 0) / 1e3
            lim_multi  = (self.acq.max_multi_rate_hz  or 0) / 1e3
            self.lblRateInfo.setText(
                f"Canali: {', '.join(labels)}  |  "
                f"Rate per-canale {cur_per:.1f} kS/s  (agg: {cur_agg:.1f} kS/s)  |  "
                f"Limiti modulo â†’ single {lim_single:.1f} kS/s, aggregato {lim_multi:.1f} kS/s"
            )
        except Exception:
            self.lblRateInfo.setText("-")

    def _on_rate_edit_finished(self):
        """
        Slot invoked when the user finishes editing the sample rate field (Fs [Hz]).
        Validates the input, applies the user-defined sampling rate to the
        acquisition manager, and restarts the acquisition if it is currently
        running. The special value "Max" (case-insensitive) or an empty field
        reverts to the automatic maximum rate.
        """
        # Read and normalize the text
        txt = (self.rateEdit.text() or "").strip()
        # Determine if the user wants the maximum rate
        use_max = False
        if txt == "" or txt.lower() == "max":
            use_max = True
        # Try to parse a numeric rate
        user_rate: Optional[float] = None
        if not use_max:
            try:
                val = float(txt)
                if val > 0:
                    user_rate = val
                else:
                    use_max = True
            except Exception:
                use_max = True
        # Apply the rate to the acquisition manager
        try:
            if use_max:
                # Use automatic maximum: reset text to "Max"
                self.rateEdit.setText("Max")
                self.acq.set_user_rate_hz(None)
            else:
                # Set the user-defined rate
                self.acq.set_user_rate_hz(user_rate)
        except Exception:
            pass
        # If an acquisition is currently running, restart it with the new sampling rate.
        # We use the internal running flag rather than the state of the Stop/Recompose
        # button because that button is only enabled when recording (salvataggio) is active.
        if getattr(self.acq, '_running', False):
            try:
                # Get current enabled channels and labels
                phys, labels = self._enabled_phys_and_labels()
                if phys:
                    # Identify the selected device
                    device = (self.cmbDevice.currentData() or self.cmbDevice.currentText()).strip()
                    # Stop the current acquisition
                    try:
                        self.acq.stop()
                    except Exception:
                        pass
                    # Restart with the same channels and labels
                    ok = False
                    try:
                        ok = self.acq.start(device_name=device, ai_channels=phys, channel_names=labels)
                    except Exception:
                        ok = False
                    if ok:
                        # Update state variables as in _update_acquisition_from_table()
                        self._current_phys_order = phys[:]
                        self._start_label_by_phys = dict(zip(phys, labels))
                        self._last_enabled_phys = phys[:]
                        # Recreate curves with distinct colours
                        self._reset_plots_curves()
                        # Enable the Stop/Recompose button only if we are currently recording.
                        try:
                            self.btnStop.setEnabled(bool(self.acq.recording_enabled))
                        except Exception:
                            self.btnStop.setEnabled(False)
                        if not self.guiTimer.isActive():
                            self.guiTimer.start()
                        # Update the rate label and push the sensor map to core
                        try:
                            self._update_rate_label(phys)
                        except Exception:
                            pass
                        try:
                            self._push_sensor_map_to_core()
                        except Exception:
                            pass
            except Exception:
                pass

    def _stop_acquisition_ui_only(self):
        try:
            if self.acq.recording_enabled:
                self.acq.set_recording(False)
        except Exception:
            pass
        try:
            self.acq.stop()
        except Exception:
            pass
        self.btnStop.setEnabled(False)
        if self.guiTimer.isActive():
            self.guiTimer.stop()
        self.lblRateInfo.setText("-")

    # ----------------------------- TDMS: folder/name, start/stop, countdown -----------------------------
    def _choose_folder(self):
        folder = QtWidgets.QFileDialog.getExistingDirectory(
            self, "Seleziona cartella di salvataggio", self.txtSaveDir.text() or DEFAULT_SAVE_DIR
        )
        if folder:
            self.txtSaveDir.setText(folder)

    def _on_start_saving(self):
        # Deve essere attiva un'acquisizione per iniziare a salvare.  Usiamo lo
        # stato interno dell'acquisition manager invece del pulsante Stop, che
        # viene abilitato solo durante il salvataggio.
        try:
            is_running = bool(getattr(self.acq, '_running', False))
        except Exception:
            is_running = False
        if not is_running:
            QtWidgets.QMessageBox.warning(self, "Attenzione", "Abilita almeno un canale per avviare il salvataggio.")
            return

        base_dir = self.txtSaveDir.text().strip() or DEFAULT_SAVE_DIR
        os.makedirs(base_dir, exist_ok=True)
        base_name = self.txtBaseName.text().strip() or "SenzaNome.tdms"
        if not base_name.lower().endswith(".tdms"):
            base_name += ".tdms"

        ts = datetime.datetime.now().strftime("%Y-%m-%d_%H-%M-%S")
        subdir_name = f"{os.path.splitext(base_name)[0]}_{ts}"
        subdir = os.path.join(base_dir, subdir_name)
        os.makedirs(subdir, exist_ok=True)

        # invia i nomi canale al core (per ogni riga della tabella)
        # send channel labels and configure base filename for TDMS segments
        self._push_channel_labels_to_core()
        # imposta il limite di memoria in base al valore selezionato nella spinbox
        try:
            mem_mb = self.spinRam.value()
            if hasattr(self.acq, "set_memory_limit_mb"):
                self.acq.set_memory_limit_mb(mem_mb)
        except Exception:
            pass
        # reset any residual in-memory blocks before changing the output directory
        try:
            if hasattr(self.acq, "clear_memory_buffer"):
                self.acq.clear_memory_buffer()
        except Exception:
            pass
        # prepare a fresh output directory
        self.acq.set_output_directory(subdir)
        # set base filename (without extension) for naming the TDMS segments
        self.acq.set_base_filename(base_name)
        # enable recording so the writer will start accumulating blocks in RAM
        self.acq.set_recording(True)

        # Now that recording is active, the Stop/Recompose button can be used to
        # stop and merge the temporary TDMS files.  Enable it explicitly.
        try:
            self.btnStop.setEnabled(True)
        except Exception:
            pass

        self._active_subdir = subdir
        self._save_dir = base_dir
        self._base_filename = base_name

        self._set_table_lock(True)

        # Reset and start memory usage timer for updating the save button text
        if not self._count_timer.isActive():
            self._count_timer.start()
        # Immediately update the button text with memory usage
        try:
            used, limit = self.acq.get_memory_usage()
            mb = used / (1024 * 1024)
            total_mb = limit / (1024 * 1024)
            self.btnStart.setText(f"Salvataggio ({mb:.1f} / {total_mb:.0f} MB)")
        except Exception:
            self.btnStart.setText("Salvataggio (0 / 500 MB)")

        # blocca i campi
        self.txtSaveDir.setEnabled(False)
        self.btnBrowseDir.setEnabled(False)
        self.txtBaseName.setEnabled(False)
        self.btnStart.setEnabled(False)

    def _tick_countdown(self):
        # Update the save button text with current memory usage while recording
        if not self.acq.recording_enabled:
            self._count_timer.stop()
            self.btnStart.setText("Salva dati")
            self.btnStart.setEnabled(True)
            return
        # Query memory usage from the acquisition manager
        try:
            used_bytes, limit_bytes = self.acq.get_memory_usage()
            used_mb = used_bytes / (1024 * 1024)
            total_mb = limit_bytes / (1024 * 1024)
            self.btnStart.setText(f"Salvataggio ({used_mb:.1f} / {total_mb:.0f} MB)")
        except Exception:
            self.btnStart.setText("Salvataggio")

    def _update_start_button_text(self):
        self.btnStart.setText(f"Salvo in ({self._countdown:02d} s) ...")

    def _on_stop(self):
        # ferma core
        try:
            self.acq.stop_graceful()
        except Exception:
            pass
        try:
            self.acq.stop()
        except Exception:
            pass

        if self._count_timer.isActive():
            self._count_timer.stop()
        self.btnStart.setText("Salva dati")
        self.btnStart.setEnabled(True)
        self.btnStop.setEnabled(False)
        self.guiTimer.stop()

        # riabilita campi
        self.txtSaveDir.setEnabled(True)
        self.btnBrowseDir.setEnabled(True)
        self.txtBaseName.setEnabled(True)

        # merge
        if not self._active_subdir:
            QtWidgets.QMessageBox.information(self, "Info", "Acquisizione fermata. Nessuna cartella di salvataggio attiva.")
            return

        # Determine the desired final TDMS path.  If a file with the same
        # name already exists in the save directory, append the current date and
        # time (dd_mm_yy_hh_mm_ss) to avoid overwriting it.
        final_path = os.path.join(self._save_dir, self._base_filename)
        try:
            if os.path.exists(final_path):
                # Split the base filename into name and extension
                base_name, ext = os.path.splitext(self._base_filename)
                # Current date/time string
                dt_str = datetime.datetime.now().strftime("%d_%m_%y_%H_%M_%S")
                # Compose a new filename with the date/time appended
                new_name = f"{base_name}_{dt_str}{ext or '.tdms'}"
                final_path = os.path.join(self._save_dir, new_name)
        except Exception:
            pass
        # Merge the temporary TDMS files into the final file with progress feedback
        try:
            from tdms_merge import TdmsMerger
            merger = TdmsMerger()
            # Progress dialog
            dlg = QtWidgets.QProgressDialog("Unione file TDMS in corso...", "Annulla", 0, 1, self)
            dlg.setWindowTitle("Unione in corso")
            dlg.setWindowModality(QtCore.Qt.WindowModal)
            dlg.setValue(0)
            # memorizza la cartella temporanea perch? _active_subdir verr? azzerata
            tmp_subdir = self._active_subdir
            # Define progress callback
            def _merge_progress(curr: int, total: int):
                try:
                    dlg.setMaximum(total)
                    dlg.setValue(curr)
                    QtWidgets.QApplication.processEvents()
                    if dlg.wasCanceled():
                        raise RuntimeError("Operazione di unione annullata dall'utente.")
                except Exception:
                    pass
            # Perform merge with progress callback
            merger.merge_temp_tdms(tmp_subdir, final_path, progress_cb=_merge_progress)
            dlg.close()
            QtWidgets.QMessageBox.information(self, "Completato", f"TDMS finale creato:\n{final_path}")
            # Una volta uniti i segmenti, elimina la cartella temporanea
            try:
                if tmp_subdir and os.path.isdir(tmp_subdir):
                    shutil.rmtree(tmp_subdir, ignore_errors=True)
            except Exception:
                pass
        except Exception as e:
            try:
                dlg.close()
            except Exception:
                pass
            QtWidgets.QMessageBox.critical(self, "Errore ricomposizione", str(e))
        finally:
            self._active_subdir = None

        self._set_table_lock(False)
        self._uncheck_all_enabled()

    # ----------------------------- Grafici -----------------------------
    def _reset_plots(self):
        self._chart_x.clear()
        for dq in self._chart_y_by_phys.values(): dq.clear()
        self._instant_t = np.array([], dtype=float)
        self._instant_y_by_phys = {k: np.array([], dtype=float) for k in self._instant_y_by_phys}

        for c in list(self._chart_curves_by_phys.values()):
            try: self.pgChart.removeItem(c)
            except Exception: pass
        for c in list(self._instant_curves_by_phys.values()):
            try: self.pgInstant.removeItem(c)
            except Exception: pass
        self._chart_curves_by_phys.clear()
        self._instant_curves_by_phys.clear()
        self._chart_legend.clear()
        self._instant_legend.clear()

        # Cancella la stringa delle medie quando si resettano i grafici
        try:
            if hasattr(self, 'lblAvgChart'):
                self.lblAvgChart.setText("")
        except Exception:
            pass

    def _reset_plots_curves(self):
        self._reset_plots()
        # Assign distinct colors to each channel for better readability
        num_ch = max(1, len(self._current_phys_order))
        for idx, phys in enumerate(self._current_phys_order):
            unit = self._calib_by_phys.get(phys, {}).get("unit", "")
            base_label = self._label_by_phys.get(phys, phys)
            label = f"{base_label} [{unit}]" if unit else base_label
            # Use a distinct color based on the index; pg.intColor returns a QColor
            try:
                color = pg.intColor(idx, hues=max(8, num_ch))
            except Exception:
                color = (255, 0, 0)  # fallback to red
            # Chart (concatenated)
            c = self.pgChart.plot(name=label, pen=pg.mkPen(color=color, width=1.5))
            try:
                c.setClipToView(True)
                c.setDownsampling(auto=True, mode='peak')
            except Exception:
                pass
            self._chart_curves_by_phys[phys] = c
            self._chart_legend.addItem(c, label)
            # Instant block plot
            ic = self.pgInstant.plot(name=label, pen=pg.mkPen(color=color, width=1.5))
            try:
                ic.setClipToView(True)
                ic.setDownsampling(auto=True, mode='peak')
            except Exception:
                pass
            self._instant_curves_by_phys[phys] = ic
            self._instant_legend.addItem(ic, label)

    def _rebuild_legends(self):
        self._chart_legend.clear()
        self._instant_legend.clear()
        for phys, curve in self._chart_curves_by_phys.items():
            unit = self._calib_by_phys.get(phys, {}).get("unit", "")
            base_label = self._label_by_phys.get(phys, phys)
            label = f"{base_label} [{unit}]" if unit else base_label
            try: curve.setName(label)
            except Exception: pass
            self._chart_legend.addItem(curve, label)
        for phys, curve in self._instant_curves_by_phys.items():
            unit = self._calib_by_phys.get(phys, {}).get("unit", "")
            base_label = self._label_by_phys.get(phys, phys)
            label = f"{base_label} [{unit}]" if unit else base_label
            try: curve.setName(label)
            except Exception: pass
            self._instant_legend.addItem(curve, label)

    def _clear_chart(self):
        self._chart_x.clear()
        for phys, curve in self._chart_curves_by_phys.items():
            self._chart_y_by_phys[phys].clear()
            curve.clear()

    # slot dai segnali (main thread)
    def _slot_instant_block(self, t: np.ndarray, ys: list, names: list):
        try:
            self._instant_t = np.asarray(t, dtype=float)
            # mappa nome di start -> phys
            start_to_phys = {name: phys for phys, name in self._start_label_by_phys.items()}
            for name, y in zip(names, ys):
                phys = start_to_phys.get(name)
                if not phys: continue
                cal = self._calib_by_phys.get(phys, {"a":1.0,"b":0.0})
                a = float(cal.get("a",1.0)); b = float(cal.get("b",0.0))
                y_eng = a * np.asarray(y, dtype=float) + b
                self._instant_y_by_phys[phys] = y_eng
        except RuntimeError:
            pass

    def _slot_chart_points(self, t_pts: np.ndarray, ys_pts: list, names: list):
        try:
            t_pts = np.asarray(t_pts, dtype=float)
            self._chart_x.extend(t_pts.tolist())
            start_to_phys = {name: phys for phys, name in self._start_label_by_phys.items()}
            for name, ypts in zip(names, ys_pts):
                phys = start_to_phys.get(name)
                if not phys: continue
                cal = self._calib_by_phys.get(phys, {"a":1.0,"b":0.0})
                a = float(cal.get("a",1.0)); b = float(cal.get("b",0.0))
                y_eng = a * np.asarray(ypts, dtype=float) + b
                self._chart_y_by_phys[phys].extend(y_eng.tolist())
        except RuntimeError:
            pass

    def _refresh_plots(self):
        # chart concatenato
        n = len(self._chart_x)
        if n > 1:
            x = np.fromiter(self._chart_x, dtype=float, count=n)
            for phys, curve in self._chart_curves_by_phys.items():
                dq = self._chart_y_by_phys.get(phys)
                if not dq:
                    continue
                y = np.fromiter(dq, dtype=float, count=len(dq))
                if y.size == x.size and y.size > 1:
                    curve.setData(x, y)

        # blocco istantaneo
        if isinstance(self._instant_t, np.ndarray) and self._instant_t.size > 1:
            for phys, curve in self._instant_curves_by_phys.items():
                y = self._instant_y_by_phys.get(phys)
                if isinstance(y, np.ndarray) and y.size == self._instant_t.size and y.size > 1:
                    curve.setData(self._instant_t, y)

        # Calcola il valore medio per ogni canale attivo e aggiorna l'etichetta
        try:
            if hasattr(self, 'lblAvgChart'):
                avg_strings = []
                # Usa l'ordine dei canali avviati per mantenere la coerenza
                for phys in self._current_phys_order:
                    dq = self._chart_y_by_phys.get(phys)
                    if dq and len(dq) > 0:
                        try:
                            # Converte il deque in array per calcolare la media
                            y_vals = np.fromiter(dq, dtype=float, count=len(dq))
                            if y_vals.size > 0:
                                avg_val = float(np.mean(y_vals))
                                # Determina il nome da visualizzare (label al momento dello start) o fallback
                                label = self._start_label_by_phys.get(phys, self._label_by_phys.get(phys, phys))
                                unit = self._calib_by_phys.get(phys, {}).get('unit', '')
                                avg_strings.append(f"{label}: {avg_val:.6g}" + (f" {unit}" if unit else ""))
                        except Exception:
                            pass
                # Aggiorna il testo dell'etichetta con le medie separate da virgola
                self.lblAvgChart.setText(", ".join(avg_strings) if avg_strings else "")
        except Exception:
            pass

    # ----------------------------- Definisci Tipo Risorsa -----------------------------
    def _open_resource_manager(self):
        try:
            from gestione_risorse import ResourceManagerDialog
        except Exception as e:
            QtWidgets.QMessageBox.critical(self, "Errore", f"Impossibile importare gestione_risorse:\n{e}")
            return
        # Apri il dialog con il percorso corrente del database dei sensori
        try:
            dlg = ResourceManagerDialog(self.acq, xml_path=self._sensor_db_path, parent=self)
        except Exception:
            dlg = ResourceManagerDialog(self.acq, xml_path=SENSOR_DB_DEFAULT, parent=self)
        dlg.exec_()
        # Se l'utente ha cambiato il percorso del DB, aggiorna la variabile
        try:
            if dlg.xml_path:
                self._sensor_db_path = dlg.xml_path
        except Exception:
            pass
        # refresh liste e scale
        self._populate_type_column()
        self._recompute_all_calibrations()

    # ----------------------------- Workspace management -----------------------------
    def _workspace_supported_daq(self):
        return "NI9201"

    def _workspace_current_device_name(self):
        try:
            return str((self.cmbDevice.currentData() or self.cmbDevice.currentText() or "")).strip()
        except Exception:
            return ""

    def _workspace_section_base(self, supported_daq, device_name):
        daq = str(supported_daq or "").strip().upper() or "NI9201"
        dev = str(device_name or "").strip()
        normalized = re.sub(r"[^A-Za-z0-9_-]+", "_", dev).strip("_")
        if not normalized:
            normalized = "DEVICE"
        return f"ws.{daq}.{normalized}"

    def _workspace_find_entry_base(self, cfg, supported_daq, device_name):
        if not device_name:
            return None
        target_daq = str(supported_daq or "").strip().upper()
        target_dev = str(device_name or "").strip().lower()
        for sec in cfg.sections():
            if not sec.startswith("ws.") or not sec.endswith(".general"):
                continue
            gen = cfg[sec]
            sec_daq = str(gen.get("supporteddaq", "") or "").strip().upper()
            sec_dev = str(gen.get("device_name", "") or "").strip()
            if not sec_dev:
                continue
            if sec_daq == target_daq and sec_dev.lower() == target_dev:
                base = sec[: -len(".general")]
                if f"{base}.channels" in cfg:
                    return base
        return None

    def _workspace_next_free_base(self, cfg, base):
        candidate = base
        idx = 2
        while (f"{candidate}.general" in cfg) or (f"{candidate}.channels" in cfg):
            candidate = f"{base}_{idx}"
            idx += 1
        return candidate

    def _save_workspace(self):
        path = ""
        try:
            dlg = QtWidgets.QFileDialog(self, "Salva workspace")
            dlg.setAcceptMode(QtWidgets.QFileDialog.AcceptSave)
            dlg.setNameFilter("INI (*.ini)")
            dlg.setDefaultSuffix("ini")
            dlg.setOption(QtWidgets.QFileDialog.DontConfirmOverwrite, True)
            if dlg.exec_() == QtWidgets.QDialog.Accepted:
                files = dlg.selectedFiles() or []
                path = files[0] if files else ""
        except Exception:
            path = ""
        if not path:
            return
        if not path.lower().endswith(".ini"):
            path += ".ini"

        cfg = configparser.ConfigParser()
        if os.path.isfile(path):
            try:
                cfg.read(path, encoding="utf-8")
            except Exception as e:
                QtWidgets.QMessageBox.critical(self, "Errore", f"Impossibile leggere workspace:\n{e}")
                return

        supported_daq = self._workspace_supported_daq()
        device_name = self._workspace_current_device_name()
        if not device_name:
            QtWidgets.QMessageBox.critical(self, "Errore", "Nessun workspace per la scheda corrente")
            return

        entry_base = self._workspace_find_entry_base(cfg, supported_daq, device_name)
        if entry_base is not None:
            ans = QtWidgets.QMessageBox.question(
                self,
                "Conferma sovrascrittura",
                "Scheda già presente vuoi sovrascriverla?",
                QtWidgets.QMessageBox.Yes | QtWidgets.QMessageBox.No,
                QtWidgets.QMessageBox.No,
            )
            if ans != QtWidgets.QMessageBox.Yes:
                return
        else:
            proposed = self._workspace_section_base(supported_daq, device_name)
            entry_base = self._workspace_next_free_base(cfg, proposed)

        sec_general = f"{entry_base}.general"
        sec_channels = f"{entry_base}.channels"
        cfg[sec_general] = {}
        cfg[sec_channels] = {}

        gen = cfg[sec_general]
        try:
            gen["sensor_db_path"] = self._sensor_db_path or ""
        except Exception:
            gen["sensor_db_path"] = ""
        gen["supporteddaq"] = supported_daq
        gen["device_name"] = device_name
        gen["save_dir"] = self.txtSaveDir.text().strip()
        gen["base_filename"] = self.txtBaseName.text().strip()
        try:
            gen["ram_mb"] = str(int(self.spinRam.value()))
        except Exception:
            gen["ram_mb"] = ""
        gen["fs"] = (self.rateEdit.text() or "").strip()

        chsec = cfg[sec_channels]
        all_phys = []
        enabled_list = []
        type_list = []
        label_list = []
        zero_raw_list = []
        zero_display_list = []
        for r in range(self.table.rowCount()):
            try:
                phys = self.table.item(r, COL_PHYS).text()
            except Exception:
                phys = f"ai{r}"

            enable_item = self.table.item(r, COL_ENABLE)
            enabled = bool(enable_item and enable_item.checkState() == QtCore.Qt.Checked)

            cmb = self.table.cellWidget(r, COL_TYPE)
            typ = ""
            if isinstance(cmb, QtWidgets.QComboBox):
                try:
                    typ = cmb.currentText().strip()
                except Exception:
                    typ = ""

            lbl_item = self.table.item(r, COL_LABEL)
            label = lbl_item.text().strip() if lbl_item else ""

            try:
                baseline_raw = None
                if hasattr(self.acq, "_zero"):
                    baseline_raw = self.acq._zero.get(phys)
                if baseline_raw is None:
                    zero_raw_list.append("")
                else:
                    zero_raw_list.append(f"{float(baseline_raw):.12g}")
            except Exception:
                zero_raw_list.append("")

            try:
                zero_item = self.table.item(r, COL_ZERO_VAL)
                if zero_item:
                    zero_display_list.append(zero_item.text().strip())
                else:
                    zero_display_list.append("")
            except Exception:
                zero_display_list.append("")

            all_phys.append(phys)
            enabled_list.append("1" if enabled else "0")
            type_list.append(typ)
            label_list.append(label)

        chsec["phys"] = ",".join(all_phys)
        chsec["enabled"] = ",".join(enabled_list)
        chsec["type"] = ",".join(type_list)
        chsec["label"] = ",".join(label_list)
        chsec["zero_raw"] = ",".join(zero_raw_list)
        chsec["zero_display"] = ",".join(zero_display_list)

        try:
            with open(path, "w", encoding="utf-8") as f:
                cfg.write(f)
        except Exception as e:
            QtWidgets.QMessageBox.critical(self, "Errore", f"Impossibile salvare il workspace:\n{e}")
            return
        QtWidgets.QMessageBox.information(self, "Salvato", f"Workspace salvato:\n{path}")

    def _load_workspace(self):
        try:
            fname, _ = QtWidgets.QFileDialog.getOpenFileName(
                self, "Carica workspace", "", "INI (*.ini)"
            )
        except Exception:
            fname = ""
        if not fname:
            return

        cfg = configparser.ConfigParser()
        try:
            cfg.read(fname, encoding="utf-8")
        except Exception as e:
            QtWidgets.QMessageBox.critical(self, "Errore", f"Impossibile leggere workspace:\n{e}")
            return

        supported_daq = self._workspace_supported_daq()
        current_device = self._workspace_current_device_name()
        if not current_device:
            QtWidgets.QMessageBox.warning(self, "Attenzione", "Nessun workspace per la scheda corrente")
            return

        entry_base = self._workspace_find_entry_base(cfg, supported_daq, current_device)
        if entry_base is None:
            QtWidgets.QMessageBox.warning(self, "Attenzione", "Nessun workspace per la scheda corrente")
            return

        sec_general = f"{entry_base}.general"
        sec_channels = f"{entry_base}.channels"
        if sec_general not in cfg or sec_channels not in cfg:
            QtWidgets.QMessageBox.warning(self, "Attenzione", "Nessun workspace per la scheda corrente")
            return

        gen = cfg[sec_general]
        chsec = cfg[sec_channels]

        sensor_db = gen.get("sensor_db_path", "").strip()
        if sensor_db:
            self._sensor_db_path = sensor_db

        sd = gen.get("save_dir", "").strip()
        if sd:
            self._save_dir = sd
            self.txtSaveDir.setText(sd)

        bn = gen.get("base_filename", "").strip()
        if bn:
            self._base_filename = bn
            self.txtBaseName.setText(bn)

        try:
            ram_mb = int(gen.get("ram_mb", "").strip())
            if ram_mb > 0:
                self.spinRam.setValue(ram_mb)
        except Exception:
            pass

        fs_txt = gen.get("fs", "").strip()
        if fs_txt:
            self.rateEdit.setText(fs_txt)
            try:
                self._on_rate_edit_finished()
            except Exception:
                pass

        self._populate_type_column()
        self._recompute_all_calibrations()

        phys_raw = chsec.get("phys", "")
        enabled_raw = chsec.get("enabled", "")
        type_raw = chsec.get("type", "")
        label_raw = chsec.get("label", "")
        phys_list = [p.strip() for p in phys_raw.split(",")] if phys_raw else []
        enabled_list = [e.strip() for e in enabled_raw.split(",")] if enabled_raw else []
        type_list = [t.strip() for t in type_raw.split(",")] if type_raw else []
        label_list = [l.strip() for l in label_raw.split(",")] if label_raw else []
        zero_raw_raw = chsec.get("zero_raw", "")
        zero_display_raw = chsec.get("zero_display", "")
        zero_raw_list = [z.strip() for z in zero_raw_raw.split(",")] if zero_raw_raw else []
        zero_display_list = [z.strip() for z in zero_display_raw.split(",")] if zero_display_raw else []

        baseline_raw_map = {}
        baseline_disp_map = {}
        self._populate_table()
        self._populate_type_column()

        self.table.blockSignals(True)
        for r in range(self.table.rowCount()):
            phys = None
            try:
                phys = self.table.item(r, COL_PHYS).text()
            except Exception:
                phys = None
            if not phys:
                continue

            try:
                idx = phys_list.index(phys)
            except Exception:
                idx = -1

            enable_item = self.table.item(r, COL_ENABLE)
            if enable_item:
                state = False
                if idx >= 0 and idx < len(enabled_list):
                    state = enabled_list[idx].strip().lower() in ("1", "true")
                enable_item.setCheckState(QtCore.Qt.Checked if state else QtCore.Qt.Unchecked)

            cmb = self.table.cellWidget(r, COL_TYPE)
            if isinstance(cmb, QtWidgets.QComboBox):
                if idx >= 0 and idx < len(type_list):
                    tval = type_list[idx] or "Voltage"
                    pos = cmb.findText(tval)
                    if pos >= 0:
                        cmb.setCurrentIndex(pos)
                    else:
                        cmb.setCurrentIndex(0)
                else:
                    cmb.setCurrentIndex(0)

            it = self.table.item(r, COL_LABEL)
            if it is None:
                it = QtWidgets.QTableWidgetItem("")
                self.table.setItem(r, COL_LABEL, it)
            if idx >= 0 and idx < len(label_list):
                it.setText(label_list[idx])
            else:
                it.setText(phys)

            if idx >= 0:
                if idx < len(zero_raw_list):
                    baseline_raw_map[phys] = zero_raw_list[idx]
                if idx < len(zero_display_list):
                    baseline_disp_map[phys] = zero_display_list[idx]
        self.table.blockSignals(False)

        self._recompute_all_calibrations()
        self._update_acquisition_from_table()
        try:
            for r in range(self.table.rowCount()):
                phys_item = self.table.item(r, COL_PHYS)
                if phys_item is None:
                    continue
                phys = phys_item.text()
                br = baseline_raw_map.get(phys, "")
                baseline_value = None
                if br not in ("", None):
                    try:
                        baseline_value = float(br)
                    except Exception:
                        baseline_value = None
                try:
                    self.acq.set_zero_raw(phys, baseline_value)
                except Exception:
                    pass
                zero_disp = baseline_disp_map.get(phys, "")
                if zero_disp:
                    self.table.item(r, COL_ZERO_VAL).setText(zero_disp)
                else:
                    try:
                        self.table.item(r, COL_ZERO_VAL).setText("0.0")
                    except Exception:
                        pass
        except Exception:
            pass
        QtWidgets.QMessageBox.information(self, "Caricato", f"Workspace caricato:\n{fname}")

    # ----------------------------- Channel helpers per ResourceManager -----------------------------
    def is_channel_enabled(self, phys: str) -> bool:
        """Restituisce True se il canale fisico ? abilitato nella tabella."""
        try:
            for r in range(self.table.rowCount()):
                phys_item = self.table.item(r, COL_PHYS)
                if phys_item and phys_item.text() == phys:
                    # colonna abilita ? una QTableWidgetItem con stato di check
                    enable_item = self.table.item(r, COL_ENABLE)
                    if enable_item:
                        return enable_item.checkState() == QtCore.Qt.Checked
                    return False
        except Exception:
            pass
        return False

    def enable_physical_channel(self, phys: str):
        """Abilita il canale fisico nella tabella."""
        try:
            for r in range(self.table.rowCount()):
                phys_item = self.table.item(r, COL_PHYS)
                if phys_item and phys_item.text() == phys:
                    enable_item = self.table.item(r, COL_ENABLE)
                    if enable_item and enable_item.checkState() != QtCore.Qt.Checked:
                        enable_item.setCheckState(QtCore.Qt.Checked)
                    break
        except Exception:
            pass

    # ----------------------------- Valore istantaneo in tabella -----------------------------
    def _update_table_value(self, start_label_name, val_volt_zeroed):
        # mappa dal nome al phys usato allo start
        phys = None
        for p, nm in self._start_label_by_phys.items():
            if nm == start_label_name:
                phys = p; break
        if phys is None:
            return
        r = self._find_row_by_phys(phys)
        if r < 0:
            return
        cal = self._calib_by_phys.get(phys, {"a":1.0,"b":0.0,"unit":""})
        a = float(cal.get("a",1.0)); b = float(cal.get("b",0.0))
        unit = cal.get("unit","")
        eng = a * float(val_volt_zeroed) + b
        text = f"{eng:.6g}" + (f" {unit}" if unit else "")
        self._auto_change = True
        self.table.item(r, COL_VALUE).setText(text)
        self._auto_change = False

    # ----------------------------- Chiusura ordinata -----------------------------
    def closeEvent(self, event: QtGui.QCloseEvent):
        try:
            if self._sync_agent is not None:
                self._sync_agent.close()
        except Exception:
            pass
        # stop timer UI
        try:
            if self.guiTimer.isActive():
                self.guiTimer.stop()
        except Exception:
            pass
        # ferma core
        try:
            self.acq.set_recording(False)
        except Exception:
            pass
        try:
            self.acq.stop()
        except Exception:
            pass
        # disconnetti segnali
        try:
            self.sigInstantBlock.disconnect()
        except Exception:
            pass
        try:
            self.sigChartPoints.disconnect()
        except Exception:
            pass
        try:
            self.channelValueUpdated.disconnect()
        except Exception:
            pass
        super().closeEvent(event)

    def _on_zero_button_clicked(self, phys: str):
        """
        Azzeramento canale:
        - Legge il valore istantaneo ATTUALE (in unit? ingegneristiche)
        - Lo mostra in colonna 'Valore azzerato'
        - Fissa lo zero nel core come valore RAW (Volt) dell'istante
        """
        # riga del canale
        r = self._find_row_by_phys(phys)
        if r < 0:
            return

        # 1) valore istantaneo in unit? ingegneristiche (quello che vedi in UI)
        try:
            val_eng = self.acq.get_last_engineered(phys)
        except Exception:
            val_eng = None

        # unit? per visualizzazione
        unit = self._calib_by_phys.get(phys, {}).get("unit", "")
        if val_eng is not None:
            txt = f"{val_eng:.6g}" + (f" {unit}" if unit else "")
            self._auto_change = True
            self.table.item(r, COL_ZERO_VAL).setText(txt)
            self._auto_change = False

        # 2) imposta lo zero nel core come baseline RAW (Volt)
        try:
            last_raw = self.acq.get_last_raw(phys)
            if last_raw is not None:
                self.acq.set_zero_raw(phys, last_raw)
        except Exception:
            pass

    def _set_row_bg(self, row: int, col: int, color: QtGui.QColor):
        item = self.table.item(row, col)
        if item is None:
            item = QtWidgets.QTableWidgetItem("")
            self.table.setItem(row, col, item)
        item.setBackground(color)

    def _set_table_lock(self, lock: bool):
        """
        Blocca/sblocca le 5 colonne: Abilita, Canale fisico, Tipo risorsa,
        Nome canale, Valore istantaneo. Grigio chiaro quando lock=True.
        """
        gray = QtGui.QColor("#e9ecef")
        white = QtGui.QColor("#ffffff")
        nrows = self.table.rowCount()

        for r in range(nrows):
            # --- Abilita (QTableWidgetItem con checkbox) ---
            it = self.table.item(r, COL_ENABLE)
            if it:
                if lock:
                    # rimuovo la possibilit? di spuntare
                    it.setFlags(QtCore.Qt.ItemIsSelectable | QtCore.Qt.ItemIsEnabled)
                else:
                    # riabilito la spunta
                    it.setFlags(QtCore.Qt.ItemIsSelectable | QtCore.Qt.ItemIsEnabled | QtCore.Qt.ItemIsUserCheckable)
            self._set_row_bg(r, COL_ENABLE, gray if lock else white)

            # --- Canale fisico (sempre non editabile; solo colore) ---
            it = self.table.item(r, COL_PHYS)
            if it:
                it.setFlags(QtCore.Qt.ItemIsSelectable | QtCore.Qt.ItemIsEnabled)
            self._set_row_bg(r, COL_PHYS, gray if lock else white)

            # --- Tipo risorsa (QComboBox) ---
            w = self.table.cellWidget(r, COL_TYPE)
            if isinstance(w, QtWidgets.QComboBox):
                w.setEnabled(not lock)
            self._set_row_bg(r, COL_TYPE, gray if lock else white)

            # --- Nome canale (item editabile quando unlock) ---
            it = self.table.item(r, COL_LABEL)
            if it:
                if lock:
                    it.setFlags(QtCore.Qt.ItemIsSelectable | QtCore.Qt.ItemIsEnabled)
                else:
                    it.setFlags(QtCore.Qt.ItemIsSelectable | QtCore.Qt.ItemIsEnabled | QtCore.Qt.ItemIsEditable)
            self._set_row_bg(r, COL_LABEL, gray if lock else white)

            # --- Valore istantaneo (display only; solo colore) ---
            self._set_row_bg(r, COL_VALUE, gray if lock else white)

    def _uncheck_all_enabled(self):
        """Rimuove tutte le spunte 'Abilita' (senza scatenare ricalcoli ripetuti)."""
        self._auto_change = True
        try:
            nrows = self.table.rowCount()
            for r in range(nrows):
                it = self.table.item(r, COL_ENABLE)
                if it and it.flags() & QtCore.Qt.ItemIsUserCheckable:
                    it.setCheckState(QtCore.Qt.Unchecked)
        finally:
            self._auto_change = False
        # applica lo stato all'acquisizione
        self._update_acquisition_from_table()

