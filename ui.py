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
import traceback
import threading
from typing import List, Callable, Optional, Dict, Any, Tuple

from calculated_channels_engine import CalculatedChannelsEngine
from formula_editor_dialog import FormulaEditorDialog

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
COL_VALUE    = 4   # Valore istantaneo (con unitase selezionata)
COL_ZERO_BTN = 5
COL_ZERO_VAL = 6

# Colonne tabella canali calcolati
CCOL_ENABLE = 0
CCOL_ID = 1
CCOL_FORMULA = 2
CCOL_LABEL = 3
CCOL_VALUE = 4
CCOL_ZERO_BTN = 5
CCOL_ZERO_VAL = 6
CCOL_PLOT = 7

MAX_CALCULATED_CHANNELS = 30
DEFAULT_CALCULATED_ROWS = 4

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


class FloatRingBuffer:
    """Fixed-size float32 ring buffer for UI preview plotting."""

    __slots__ = ("capacity", "_data", "_start", "_size")

    def __init__(self, capacity: int, dtype=np.float32):
        cap = int(capacity or 0)
        if cap <= 0:
            cap = 1
        self.capacity = cap
        self._data = np.empty(cap, dtype=dtype)
        self._start = 0
        self._size = 0

    def __len__(self) -> int:
        return int(self._size)

    def clear(self) -> None:
        self._start = 0
        self._size = 0

    def append(self, value) -> None:
        self.extend([value])

    def extend(self, values) -> None:
        arr = np.asarray(values, dtype=self._data.dtype).reshape(-1)
        n = int(arr.size)
        if n <= 0:
            return
        cap = int(self.capacity)
        if n >= cap:
            self._data[:] = arr[-cap:]
            self._start = 0
            self._size = cap
            return
        size = int(self._size)
        start = int(self._start)
        end = (start + size) % cap
        first = min(n, cap - end)
        self._data[end:end + first] = arr[:first]
        rest = n - first
        if rest > 0:
            self._data[0:rest] = arr[first:first + rest]
        new_size = size + n
        if new_size <= cap:
            self._size = new_size
            return
        overflow = new_size - cap
        self._size = cap
        self._start = (start + overflow) % cap

    def to_numpy(self, dtype=np.float64) -> np.ndarray:
        size = int(self._size)
        if size <= 0:
            return np.array([], dtype=dtype)
        cap = int(self.capacity)
        start = int(self._start)
        if start + size <= cap:
            out = self._data[start:start + size]
        else:
            first = self._data[start:cap]
            second = self._data[0:(start + size) % cap]
            out = np.concatenate((first, second), axis=0)
        return np.asarray(out, dtype=dtype)

    def resize(self, new_capacity: int) -> None:
        cap = int(new_capacity or 0)
        if cap <= 0:
            cap = 1
        if cap == int(self.capacity):
            return
        old = self.to_numpy(dtype=self._data.dtype)
        if old.size > cap:
            old = old[-cap:]
        self.capacity = cap
        self._data = np.empty(cap, dtype=self._data.dtype)
        self._start = 0
        self._size = 0
        n = int(old.size)
        if n > 0:
            self._data[:n] = old
            self._size = n


class AcquisitionWindow(QtWidgets.QMainWindow):
    # segnali thread-safe verso UI
    sigInstantBlock = QtCore.pyqtSignal(object, object, object)   # (t, [ys...], [names...])
    sigChartPoints  = QtCore.pyqtSignal(object, object, object)
    channelValueUpdated = QtCore.pyqtSignal(str, float)           # (start_label_name, value)

    def __init__(self, acq_manager, merger, parent=None):
        super().__init__(parent)
        self.acq = acq_manager
        self.merger = merger

        self.setWindowTitle("NI 9201 Acquisition - Architettura")
        self.resize(1200, 740)

        # stati UI/logica
        self._building_table = False
        self._auto_change = False
        self._device_ready = False

        # mappature canali
        self._current_phys_order = []                    # ordine fisico corrente avviato
        self._label_by_phys = {f"ai{i}": f"ai{i}" for i in range(8)}   # label utente "Nome canale"
        self._sensor_type_by_phys = {f"ai{i}": "Voltage" for i in range(8)}
        self._calib_by_phys = {f"ai{i}": {"unit":"", "a":1.0, "b":0.0} for i in range(8)}
        self._start_label_by_phys = {}                   # mapping phys -> nome al momento dello start
        self._last_enabled_phys = []

        # grafici: buffer
        MAXPTS = 12000
        self._chart_x = FloatRingBuffer(MAXPTS, dtype=np.float64)
        self._chart_history_points = MAXPTS
        self._chart_y_by_phys = {f"ai{i}": FloatRingBuffer(MAXPTS) for i in range(8)}
        self._instant_t = np.array([], dtype=float)
        self._instant_y_by_phys = {f"ai{i}": np.array([], dtype=float) for i in range(8)}
        self._chart_curves_by_phys = {}
        self._instant_curves_by_phys = {}
        self._chart_y_by_calc: Dict[str, FloatRingBuffer] = {}
        self._instant_y_by_calc: Dict[str, np.ndarray] = {}
        self._chart_curves_by_calc: Dict[str, Any] = {}
        self._instant_curves_by_calc: Dict[str, Any] = {}
        self._curve_pool_chart_phys: List[Any] = []
        self._curve_pool_instant_phys: List[Any] = []
        self._curve_pool_chart_calc: List[Any] = []
        self._curve_pool_instant_calc: List[Any] = []
        self._curve_pool_max = 48
        self._curve_pool_max_total = 96
        self._suspend_preview_when_background = True
        self._compact_instant_when_background = True
        self._calc_last_value_raw: Dict[str, float] = {}
        self._calc_zero_by_cc: Dict[str, Optional[float]] = {}
        self._calc_formula_by_cc: Dict[str, str] = {}
        self._calc_compile_errors: Dict[str, str] = {}
        self._calc_runtime_errors: Dict[str, str] = {}
        self._calc_engine = CalculatedChannelsEngine(max_channels=MAX_CALCULATED_CHANNELS)
        self._building_calc_table = False

        # TDMS saving
        self._save_dir = DEFAULT_SAVE_DIR
        self._base_filename = "SenzaNome.tdms"
        self._active_subdir = None
        self._recording_start_sample_index = 0
        self._merge_state_lock = threading.Lock()
        self._merge_state: Dict[str, Any] = {"state": "idle", "progress": 0.0, "message": "", "final_tdms": "", "error": "", "post_applied": False, "started_ns": 0, "updated_ns": 0}
        self._merge_worker_thread: Optional[threading.Thread] = None
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
        # Ordered shutdown guard/state.
        self._shutdown_in_progress = False
        self._shutdown_phase = "idle"

        # Path for the current sensor database. Default to SENSOR_DB_DEFAULT.
        self._sensor_db_path = SENSOR_DB_DEFAULT

        # Controllo remoto da chassis (attivo solo se lanciato dal root con env sync).
        self._sync_agent = None
        self._sync_remote_active = False
        self._sync_arm_requested = False
        self._pending_sync_start_cfg: Optional[Dict[str, Any]] = None

        # UI
        self._build_ui()
        self._connect_signals()
        self._populate_calc_table(reset=True)
        self._rebuild_calc_engine(update_core=True)

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

        # Tab Canali calcolati
        tabCalc = QtWidgets.QWidget()
        vcalc = QtWidgets.QVBoxLayout(tabCalc)
        self.calcTable = QtWidgets.QTableWidget(0, 8)
        self.calcTable.setHorizontalHeaderLabels([
            "Abilita", "Canale calcolato", "Formula", "Nome canale",
            "Valore istantaneo", "Azzeramento", "Valore azzerato", "Visualizza nel grafico"
        ])
        self.calcTable.horizontalHeader().setSectionResizeMode(QtWidgets.QHeaderView.Interactive)
        self.calcTable.horizontalHeader().setStretchLastSection(True)
        vcalc.addWidget(self.calcTable, 1)
        calcBtns = QtWidgets.QHBoxLayout()
        calcBtns.addStretch(1)
        self.btnAddCalcChannel = QtWidgets.QPushButton("Aggiungi canale di calcolo")
        self.btnResetCalc = QtWidgets.QPushButton("Reset calcoli")
        calcBtns.addWidget(self.btnAddCalcChannel)
        calcBtns.addWidget(self.btnResetCalc)
        vcalc.addLayout(calcBtns)
        self.tabs.addTab(tabCalc, "Canali Calcolati")

        # Tab Grafici: sotto-tab (chart + instant)
        tabPlots = QtWidgets.QTabWidget()

        self.tabChart = QtWidgets.QWidget()
        vchart = QtWidgets.QVBoxLayout(self.tabChart)
        self.pgChart = pg.PlotWidget(title="Chart concatenato (decimato)")
        try:
            self.pgChart.showGrid(x=True, y=True, alpha=0.12)
        except Exception:
            pass
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
        self.chkPhysViewEnable = QtWidgets.QPushButton("Abilita visualizzazione canali")
        self.chkPhysViewEnable.setCheckable(True)
        self.chkPhysViewEnable.setChecked(False)
        self.chkCalcViewEnable = QtWidgets.QPushButton("Abilita visualizzazione canali calcolati")
        self.chkCalcViewEnable.setCheckable(True)
        self.chkCalcViewEnable.setChecked(False)
        self.cmbChartPreset = QtWidgets.QComboBox()
        self.cmbChartPreset.addItems(["Operativo", "Diagnostica", "Prestazioni"])
        self.cmbChartMode = QtWidgets.QComboBox()
        self.cmbChartMode.addItem("Overlay", "overlay")
        self.cmbChartMode.addItem("Offset", "offset")
        self.cmbChartMode.addItem("Stacked", "stacked")
        self.chkChartRelativeTime = QtWidgets.QPushButton("Tempo relativo")
        self.chkChartRelativeTime.setCheckable(True)
        self.chkChartRelativeTime.setChecked(True)
        self.spinChartWindowSec = QtWidgets.QDoubleSpinBox()
        self.spinChartWindowSec.setDecimals(1)
        self.spinChartWindowSec.setRange(0.0, 86400.0)
        self.spinChartWindowSec.setSingleStep(5.0)
        self.spinChartWindowSec.setValue(60.0)
        self.spinChartWindowSec.setSuffix(" s")
        self.chkChartRobustY = QtWidgets.QCheckBox("Autoscale")
        self.chkChartRobustY.setChecked(True)
        self.chkChartLockY = QtWidgets.QCheckBox("Blocca Y")
        self.chkChartRobustY.setVisible(False)
        self.chkChartLockY.setVisible(False)
        self.cmbChartYScale = QtWidgets.QComboBox()
        self.cmbChartYScale.addItem("Autoscale", "autoscale")
        self.cmbChartYScale.addItem("Blocca Y", "lock")
        self.lblChartYMin = QtWidgets.QLabel("Y min:")
        self.spinChartYMin = QtWidgets.QDoubleSpinBox()
        self.spinChartYMin.setDecimals(1)
        self.spinChartYMin.setRange(-1.0e12, 1.0e12)
        self.spinChartYMin.setSingleStep(0.1)
        self.spinChartYMin.setFixedWidth(88)
        self.spinChartYMin.setValue(-1.0)
        self.lblChartYMax = QtWidgets.QLabel("Y max:")
        self.spinChartYMax = QtWidgets.QDoubleSpinBox()
        self.spinChartYMax.setDecimals(1)
        self.spinChartYMax.setRange(-1.0e12, 1.0e12)
        self.spinChartYMax.setSingleStep(0.1)
        self.spinChartYMax.setFixedWidth(88)
        self.spinChartYMax.setValue(1.0)
        self.lblChartYMin.setVisible(False)
        self.spinChartYMin.setVisible(False)
        self.lblChartYMax.setVisible(False)
        self.spinChartYMax.setVisible(False)
        self.cmbChartFocus = QtWidgets.QComboBox()
        self.cmbChartFocus.addItem("Tutti", "")
        self.chkChartCursors = QtWidgets.QCheckBox("Cursori A/B")
        self.chkChartCursors.setVisible(False)
        self.chkChartCursors.setChecked(False)
        self.btnChartFit = QtWidgets.QPushButton("Fit vista")
        self.btnChartFit.setVisible(False)
        self.btnChartResetView = QtWidgets.QPushButton("Reset vista")

        hctrl.addWidget(self.chkPhysViewEnable)
        hctrl.addWidget(self.chkCalcViewEnable)
        hctrl.addSpacing(8)
        self.cmbChartPreset.setVisible(False)
        self.cmbChartMode.setVisible(False)
        hctrl.addWidget(QtWidgets.QLabel("Focus:"))
        hctrl.addWidget(self.cmbChartFocus)
        hctrl.addWidget(self.chkChartRelativeTime)
        hctrl.addWidget(QtWidgets.QLabel("Finestra:"))
        hctrl.addWidget(self.spinChartWindowSec)
        hctrl.addWidget(QtWidgets.QLabel("Scala Y:"))
        hctrl.addWidget(self.cmbChartYScale)
        hctrl.addWidget(self.lblChartYMin)
        hctrl.addWidget(self.spinChartYMin)
        hctrl.addWidget(self.lblChartYMax)
        hctrl.addWidget(self.spinChartYMax)
        hctrl.addStretch(1)
        hctrl.addWidget(self.btnChartResetView)
        hctrl.addWidget(self.btnClearChart)
        vchart.addLayout(hctrl)
        self.lblChartCursorInfo = QtWidgets.QLabel("")
        self.lblChartCursorInfo.setWordWrap(True)
        self.lblChartCursorInfo.setVisible(False)
        vchart.addWidget(self.lblChartCursorInfo)
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
        self._plots_tab_widget = tabPlots
        self._plots_tab_index = self.tabs.indexOf(tabPlots)

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
        self.btnStart = QtWidgets.QPushButton("Salva dati")            # passa a "Salvo in (xx s)?"
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
        self._calc_curve_layout_dirty = True
        self._plot_render_max_points = 2500
        self._preview_points_per_block = 1200
        self._preview_minmax_enabled = True
        self._preview_queue_max_blocks = 24
        self._preview_queue = deque(maxlen=self._preview_queue_max_blocks)
        self._preview_queue_dropped = 0
        self._preview_apply_blocks_per_tick = 3
        self._preview_apply_blocks_per_tick_default = 3
        self._render_budget_curves = 8
        self._render_budget_curves_default = 8
        self._render_budget_curves_instant = 8
        self._render_budget_curves_instant_default = 8
        self._rr_cursor_chart = 0
        self._rr_cursor_instant = 0
        self._plot_render_max_points_default = int(self._plot_render_max_points)
        self._guardrail_active = False
        self._refresh_ewma_ms = 0.0
        self._guardrail_high_ms = 35.0
        self._guardrail_low_ms = 18.0
        self._guardrail_min_render_points = 700
        self._plot_sample_idx_cache: Dict[Tuple[int, int], np.ndarray] = {}
        self._plot_sample_idx_cache_limit = 32
        self._history_budget_points = 220000
        self._history_min_points = 1200
        self._history_max_points = 12000
        self._history_adjust_cooldown_s = 1.2
        self._last_history_adjust_ts = 0.0
        self._preview_idx_scratch = np.empty(max(256, int(self._preview_points_per_block) * 2 + 4), dtype=np.int64)
        self._table_value_min_interval_s = 0.12
        self._last_table_flush_ts = 0.0
        self._pending_table_updates: Dict[str, Any] = {}
        self._chart_last_preview_t = np.nan
        self._chart_gap_between_blocks = True
        self._chart_last_series_by_key: Dict[str, Tuple[np.ndarray, np.ndarray, str]] = {}
        self._chart_locked_ylim: Optional[Tuple[float, float]] = None
        self._chart_preset_active = ""
        self._chart_cursor_a = pg.InfiniteLine(angle=90, movable=True, pen=pg.mkPen((255, 255, 255, 140), width=1.0))
        self._chart_cursor_b = pg.InfiniteLine(angle=90, movable=True, pen=pg.mkPen((255, 200, 0, 140), width=1.0))
        try:
            self.pgChart.addItem(self._chart_cursor_a, ignoreBounds=True)
            self.pgChart.addItem(self._chart_cursor_b, ignoreBounds=True)
            self._chart_cursor_a.hide()
            self._chart_cursor_b.hide()
        except Exception:
            pass
        self._table_flush_timer = QtCore.QTimer(self)
        self._table_flush_timer.setInterval(100)
        self._table_flush_timer.timeout.connect(self._flush_table_value_updates)
        self._table_flush_timer.start()

        self._avg_ui_interval_s = 0.15
        self._last_avg_ui_update_ts = 0.0

        self._legend_signature_cache: Optional[Tuple[Any, ...]] = None
        self._chart_focus_signature_cache: Optional[Tuple[Any, ...]] = None

        self._guardrail_rss_high_mb = 900.0
        self._guardrail_rss_low_mb = 720.0

        self._ui_profile_background = False
        self._bg_gui_interval = max(250, int(self._default_gui_interval * 3))
        self._bg_render_budget_curves = 2
        self._bg_render_budget_curves_instant = 2
        self._bg_preview_apply_blocks = 1
        self._ui_profile_timer = QtCore.QTimer(self)
        self._ui_profile_timer.setInterval(1000)
        self._ui_profile_timer.timeout.connect(self._update_ui_render_profile)
        self._ui_profile_timer.start()

        profile_name = str(os.environ.get("CDAQ_UI_PROFILE", "balanced") or "balanced").strip().lower()
        if profile_name in ("high", "high_load", "low_memory"):
            self._plot_render_max_points_default = min(int(self._plot_render_max_points_default), 1800)
            self._plot_render_max_points = min(int(self._plot_render_max_points), 1800)
            self._render_budget_curves_default = min(int(self._render_budget_curves_default), 6)
            self._render_budget_curves = min(int(self._render_budget_curves), 6)
            self._render_budget_curves_instant_default = min(int(self._render_budget_curves_instant_default), 5)
            self._render_budget_curves_instant = min(int(self._render_budget_curves_instant), 5)
            self._preview_apply_blocks_per_tick_default = min(int(self._preview_apply_blocks_per_tick_default), 2)
            self._preview_apply_blocks_per_tick = min(int(self._preview_apply_blocks_per_tick), 2)
            self._bg_gui_interval = max(self._bg_gui_interval, 350)

        self._perf_metrics = deque(maxlen=720)
        self._perf_logging_enabled = True
        self._perf_log_path = os.path.join(os.path.dirname(__file__), "runtime_perf.csv")
        self._perf_timer = QtCore.QTimer(self)
        self._perf_timer.setInterval(2000)
        self._perf_timer.timeout.connect(self._sample_performance_metrics)
        self._perf_timer.start()


        # Relayout throttled per widget embedded nelle celle (bottoni/combo/spinbox).
        self._cell_widget_relayout_timer = QtCore.QTimer(self)
        self._cell_widget_relayout_timer.setSingleShot(True)
        self._cell_widget_relayout_timer.setInterval(0)
        self._cell_widget_relayout_timer.timeout.connect(self._realign_embedded_cell_widgets)

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
            with open(CONFIG_FILE, "r", encoding="utf-8-sig") as f:
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
        try:
            self.chkPhysViewEnable.setChecked(False)
        except Exception:
            pass
        try:
            self.chkCalcViewEnable.setChecked(False)
        except Exception:
            pass
        try:
            self.cmbChartPreset.setCurrentText(str(cfg.get("chart_preset", "Operativo") or "Operativo"))
            self.cmbChartMode.setCurrentText(str(cfg.get("chart_mode", "Overlay") or "Overlay"))
            self.chkChartRelativeTime.setChecked(True)
            self.spinChartWindowSec.setValue(float(cfg.get("chart_window_s", 60.0) or 0.0))
            self.chkChartRobustY.setChecked(bool(cfg.get("chart_robust_y", True)))
            self.chkChartLockY.setChecked(bool(cfg.get("chart_lock_y", False)))
            self.chkChartCursors.setChecked(bool(cfg.get("chart_cursors", False)))
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
            cfg["show_phys_plot"] = bool(self.chkPhysViewEnable.isChecked())
            cfg["show_calc_plot"] = bool(self.chkCalcViewEnable.isChecked())
            cfg["chart_preset"] = str(self.cmbChartPreset.currentText() or "Operativo")
            cfg["chart_mode"] = str(self.cmbChartMode.currentText() or "Overlay")
            cfg["chart_window_s"] = float(self.spinChartWindowSec.value())
            cfg["chart_robust_y"] = bool(self.chkChartRobustY.isChecked())
            cfg["chart_lock_y"] = bool(self.chkChartLockY.isChecked())
            cfg["chart_cursors"] = bool(self.chkChartCursors.isChecked())
        except Exception:
            pass
        try:
            txt = self.rateEdit.text().strip()
            if txt:
                cfg["fs"] = float(txt)
        except Exception:
            pass
        try:
            with open(CONFIG_FILE, "w", encoding="utf-8-sig") as f:
                json.dump(cfg, f, indent=2)
        except Exception:
            pass

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
        self.btnAddCalcChannel.clicked.connect(self._on_add_calc_channel)
        self.btnResetCalc.clicked.connect(self._on_reset_calculated_channels)
        self.chkCalcViewEnable.toggled.connect(self._on_calc_view_toggled)
        self.chkPhysViewEnable.toggled.connect(self._on_phys_view_toggled)
        try:
            self.cmbChartFocus.currentIndexChanged.connect(self._on_chart_focus_changed)
            self.chkChartRelativeTime.toggled.connect(self._on_chart_view_option_changed)
            self.chkChartRelativeTime.toggled.connect(self._update_chart_relative_button_style)
            self.spinChartWindowSec.valueChanged.connect(self._on_chart_view_option_changed)
            self.cmbChartYScale.currentIndexChanged.connect(self._on_chart_y_scale_changed)
            self.spinChartYMin.valueChanged.connect(self._on_chart_y_limits_changed)
            self.spinChartYMax.valueChanged.connect(self._on_chart_y_limits_changed)
            self.btnChartResetView.clicked.connect(self._on_chart_reset_view_clicked)
        except Exception:
            pass
        self._apply_chart_preset("Operativo", force=True)
        self._update_chart_relative_button_style()
        self._update_chart_view_buttons_style()
        self._on_chart_y_scale_changed(show_popup=False)

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
        try:
            self.calcTable.itemChanged.disconnect()
        except Exception:
            pass
        self.calcTable.itemChanged.connect(self._on_calc_item_changed)
        self.calcTable.cellDoubleClicked.connect(self._on_calc_cell_double_clicked)

        self.cmbDevice.currentIndexChanged.connect(self._on_device_changed)

        # Aggiorna la frequenza di campionamento quando l'utente conferma il valore
        try:
            self.rateEdit.editingFinished.connect(self._on_rate_edit_finished)
        except Exception:
            pass

        # callback dal core (rimappati in segnali Qt)
        self.channelValueUpdated.connect(self._queue_table_value_update)
        self.sigInstantBlock.connect(self._slot_instant_block)
        self.sigChartPoints.connect(self._slot_chart_points)

        self.acq.on_channel_value = lambda name, val: self.channelValueUpdated.emit(name, val)
        self.acq.on_new_instant_block = lambda t, ys, names: self.sigInstantBlock.emit(t, ys, names)
        self.acq.on_new_chart_points = lambda t_pts, ys_pts, names: self.sigChartPoints.emit(t_pts, ys_pts, names)
        self._connect_embedded_widget_relayout()
        self._schedule_embedded_widget_relayout()

    def _connect_embedded_widget_relayout(self) -> None:
        header_pairs = [
            (self.table.horizontalHeader(), "sectionResized"),
            (self.table.verticalHeader(), "sectionResized"),
            (self.calcTable.horizontalHeader(), "sectionResized"),
            (self.calcTable.verticalHeader(), "sectionResized"),
        ]
        for obj, sig_name in header_pairs:
            try:
                getattr(obj, sig_name).connect(lambda *_: self._schedule_embedded_widget_relayout())
            except Exception:
                pass
        for bar in (
            self.table.horizontalScrollBar(),
            self.table.verticalScrollBar(),
            self.calcTable.horizontalScrollBar(),
            self.calcTable.verticalScrollBar(),
        ):
            try:
                bar.valueChanged.connect(lambda *_: self._schedule_embedded_widget_relayout())
            except Exception:
                pass

    def _schedule_embedded_widget_relayout(self) -> None:
        try:
            self._cell_widget_relayout_timer.start()
        except Exception:
            pass

    def _realign_embedded_widgets_for_table(self, table: QtWidgets.QTableWidget, columns: List[int]) -> None:
        model = table.model()
        if model is None:
            return
        for row in range(table.rowCount()):
            for col in columns:
                widget = table.cellWidget(row, col)
                if widget is None:
                    continue
                idx = model.index(row, col)
                rect = table.visualRect(idx)
                if rect.isValid() and rect.width() > 0 and rect.height() > 0:
                    widget.setGeometry(rect)

    def _realign_embedded_cell_widgets(self) -> None:
        try:
            self._realign_embedded_widgets_for_table(self.table, [COL_TYPE, COL_ZERO_BTN])
        except Exception:
            pass
        try:
            self._realign_embedded_widgets_for_table(self.calcTable, [CCOL_ZERO_BTN])
        except Exception:
            pass

    # ----------------------------- Canali calcolati -----------------------------
    def _calc_channel_id_for_row(self, row: int) -> str:
        item = self.calcTable.item(row, CCOL_ID)
        return str(item.text().strip() if item else f"cc{row}")

    def _find_calc_row_by_cc(self, channel_id: str) -> int:
        for r in range(self.calcTable.rowCount()):
            if self._calc_channel_id_for_row(r) == channel_id:
                return r
        return -1

    def _existing_channel_names_lower(self, exclude_phys_row: Optional[int] = None, exclude_calc_row: Optional[int] = None) -> List[str]:
        out: List[str] = []
        for r in range(self.table.rowCount()):
            if exclude_phys_row is not None and r == exclude_phys_row:
                continue
            it = self.table.item(r, COL_LABEL)
            if it:
                txt = (it.text() or "").strip()
                if txt:
                    out.append(txt.lower())
        for r in range(self.calcTable.rowCount()):
            if exclude_calc_row is not None and r == exclude_calc_row:
                continue
            it = self.calcTable.item(r, CCOL_LABEL)
            if it:
                txt = (it.text() or "").strip()
                if txt:
                    out.append(txt.lower())
        return out

    def _dedupe_channel_name(self, base_name: str, existing_lower: List[str]) -> str:
        base = str(base_name or "").strip()
        if not base:
            base = "channel"
        candidate = base
        suffix = 2
        existing = set(existing_lower or [])
        while candidate.lower() in existing:
            candidate = f"{base}_{suffix}"
            suffix += 1
        return candidate

    def _populate_calc_table(self, reset: bool = False) -> None:
        self._building_calc_table = True
        try:
            if reset:
                self.calcTable.setRowCount(0)
                self._calc_formula_by_cc.clear()
                self._calc_zero_by_cc.clear()
                self._calc_last_value_raw.clear()
                try:
                    self._calc_engine.reset_all_state()
                except Exception:
                    pass
                for idx in range(DEFAULT_CALCULATED_ROWS):
                    self._append_calc_row(idx)
            elif self.calcTable.rowCount() <= 0:
                for idx in range(DEFAULT_CALCULATED_ROWS):
                    self._append_calc_row(idx)
        finally:
            self._building_calc_table = False
        self._rebuild_calc_engine(update_core=True)
        self._schedule_embedded_widget_relayout()

    def _append_calc_row(self, idx: int) -> None:
        if self.calcTable.rowCount() >= MAX_CALCULATED_CHANNELS:
            return
        row = self.calcTable.rowCount()
        self.calcTable.insertRow(row)
        cc_id = f"cc{int(idx)}"

        it_enable = QtWidgets.QTableWidgetItem()
        it_enable.setFlags(QtCore.Qt.ItemIsSelectable | QtCore.Qt.ItemIsEnabled)
        it_enable.setCheckState(QtCore.Qt.Unchecked)
        self.calcTable.setItem(row, CCOL_ENABLE, it_enable)

        it_id = QtWidgets.QTableWidgetItem(cc_id)
        it_id.setFlags(QtCore.Qt.ItemIsSelectable | QtCore.Qt.ItemIsEnabled)
        self.calcTable.setItem(row, CCOL_ID, it_id)

        it_formula = QtWidgets.QTableWidgetItem("")
        it_formula.setFlags(QtCore.Qt.ItemIsSelectable | QtCore.Qt.ItemIsEnabled)
        it_formula.setToolTip("")
        self.calcTable.setItem(row, CCOL_FORMULA, it_formula)
        self._calc_formula_by_cc.setdefault(cc_id, "")

        default_name = cc_id
        dedup_name = self._dedupe_channel_name(default_name, self._existing_channel_names_lower(exclude_calc_row=row))
        it_label = QtWidgets.QTableWidgetItem(dedup_name)
        it_label.setFlags(QtCore.Qt.ItemIsSelectable | QtCore.Qt.ItemIsEnabled | QtCore.Qt.ItemIsEditable)
        self.calcTable.setItem(row, CCOL_LABEL, it_label)

        it_val = QtWidgets.QTableWidgetItem("-")
        it_val.setFlags(QtCore.Qt.ItemIsSelectable | QtCore.Qt.ItemIsEnabled)
        self.calcTable.setItem(row, CCOL_VALUE, it_val)

        btn_zero = QtWidgets.QPushButton("Azzeramento")
        btn_zero.clicked.connect(lambda _=False, cc=cc_id: self._on_zero_calc_button_clicked(cc))
        self.calcTable.setCellWidget(row, CCOL_ZERO_BTN, btn_zero)

        it_zero = QtWidgets.QTableWidgetItem("0.0")
        it_zero.setFlags(QtCore.Qt.ItemIsSelectable | QtCore.Qt.ItemIsEnabled)
        self.calcTable.setItem(row, CCOL_ZERO_VAL, it_zero)

        it_plot = QtWidgets.QTableWidgetItem()
        it_plot.setFlags(QtCore.Qt.ItemIsSelectable | QtCore.Qt.ItemIsEnabled | QtCore.Qt.ItemIsUserCheckable)
        it_plot.setCheckState(QtCore.Qt.Unchecked)
        self.calcTable.setItem(row, CCOL_PLOT, it_plot)

        self._calc_zero_by_cc.setdefault(cc_id, None)
        self._schedule_embedded_widget_relayout()

    def _on_add_calc_channel(self) -> None:
        if self.calcTable.rowCount() >= MAX_CALCULATED_CHANNELS:
            QtWidgets.QMessageBox.warning(self, "Limite raggiunto", f"Numero massimo canali calcolati: {MAX_CALCULATED_CHANNELS}.")
            return
        self._building_calc_table = True
        try:
            self._append_calc_row(self.calcTable.rowCount())
        finally:
            self._building_calc_table = False
        self._rebuild_calc_engine(update_core=True)
        self._sync_calc_plot_curves()

    def _on_reset_calculated_channels(self) -> None:
        self._populate_calc_table(reset=True)
        self._sync_calc_plot_curves()

    def _preview_formula_text(self, text: str) -> str:
        s = str(text or "").replace("\r\n", " ").replace("\n", " ").strip()
        if len(s) <= 48:
            return s
        return s[:45] + "..."

    def _collect_calc_formula_map(self) -> Dict[str, str]:
        out: Dict[str, str] = {}
        for r in range(self.calcTable.rowCount()):
            cc = self._calc_channel_id_for_row(r)
            out[cc] = str(self._calc_formula_by_cc.get(cc, "") or "").strip()
        return out

    def _refresh_calc_engine_enabled(self) -> None:
        enabled_ids: List[str] = []
        for r in range(self.calcTable.rowCount()):
            cc = self._calc_channel_id_for_row(r)
            formula = str(self._calc_formula_by_cc.get(cc, "") or "").strip()
            if cc in self._calc_compile_errors:
                continue
            it = self.calcTable.item(r, CCOL_ENABLE)
            if it is not None and it.checkState() == QtCore.Qt.Checked and formula:
                enabled_ids.append(cc)
        try:
            self._calc_engine.set_enabled_channels(enabled_ids)
        except Exception:
            pass

    def _dummy_formula_inputs(self) -> Dict[str, np.ndarray]:
        n = 64
        t = np.linspace(0.0, 1.0, n, dtype=np.float64)
        out: Dict[str, np.ndarray] = {}
        for i in range(8):
            out[f"ai{i}"] = np.sin((i + 1) * 2.0 * np.pi * t)
        return out

    def _set_calc_row_error(self, row: int, message: str) -> None:
        msg = str(message or "Formula non valida.")
        red = QtGui.QColor("#ffd9d9")
        for col in (CCOL_FORMULA, CCOL_LABEL, CCOL_VALUE):
            it = self.calcTable.item(row, col)
            if it is not None:
                it.setBackground(red)
                it.setToolTip(msg if col == CCOL_FORMULA else "")

    def _clear_calc_row_error(self, row: int) -> None:
        white = QtGui.QColor("#ffffff")
        for col in (CCOL_FORMULA, CCOL_LABEL, CCOL_VALUE):
            it = self.calcTable.item(row, col)
            if it is not None:
                it.setBackground(white)
                if col == CCOL_FORMULA:
                    it.setToolTip(str(self._calc_formula_by_cc.get(self._calc_channel_id_for_row(row), "") or ""))

    def _apply_calc_row_flags(self, row: int) -> None:
        cc = self._calc_channel_id_for_row(row)
        formula = str(self._calc_formula_by_cc.get(cc, "") or "").strip()
        err = str(self._calc_compile_errors.get(cc, "") or "")
        enable_item = self.calcTable.item(row, CCOL_ENABLE)
        if enable_item is None:
            return
        if formula and not err:
            enable_item.setFlags(QtCore.Qt.ItemIsSelectable | QtCore.Qt.ItemIsEnabled | QtCore.Qt.ItemIsUserCheckable)
        else:
            enable_item.setCheckState(QtCore.Qt.Unchecked)
            enable_item.setFlags(QtCore.Qt.ItemIsSelectable | QtCore.Qt.ItemIsEnabled)
        if err:
            self._set_calc_row_error(row, err)
        else:
            self._clear_calc_row_error(row)

    def _rebuild_calc_engine(self, update_core: bool = False, test_runtime: bool = False) -> bool:
        formula_map = self._collect_calc_formula_map()
        compile_errors = self._calc_engine.configure(formula_map)
        self._calc_compile_errors = dict(compile_errors)
        runtime_errors: Dict[str, str] = {}
        if test_runtime:
            try:
                probe = CalculatedChannelsEngine(max_channels=MAX_CALCULATED_CHANNELS)
                probe.configure(formula_map)
                probe.set_enabled_channels(list(formula_map.keys()), reset_disabled=False)
                _, runtime_errors = probe.evaluate(
                    self._dummy_formula_inputs(),
                    float(getattr(self.acq, "current_rate_hz", 0.0) or 1.0),
                    fill_value=0.0,
                )
            except Exception:
                runtime_errors = {}
        for cc, err in runtime_errors.items():
            if cc.startswith("cc") and formula_map.get(cc, "").strip():
                self._calc_compile_errors[cc] = err

        self._building_calc_table = True
        try:
            for r in range(self.calcTable.rowCount()):
                self._apply_calc_row_flags(r)
        finally:
            self._building_calc_table = False
        self._refresh_calc_engine_enabled()

        if update_core:
            self._push_calculated_channels_to_core()

        self._rebuild_legends()
        self._sync_calc_plot_curves()
        return len(self._calc_compile_errors) == 0

    def _on_calc_cell_double_clicked(self, row: int, col: int) -> None:
        if col != CCOL_FORMULA:
            return
        self._open_calc_formula_editor(row)

    def _open_calc_formula_editor(self, row: int) -> None:
        cc = self._calc_channel_id_for_row(row)
        current = str(self._calc_formula_by_cc.get(cc, "") or "")
        dlg = FormulaEditorDialog(channel_id=cc, formula_text=current, parent=self)
        while True:
            dlg.clear_error()
            if dlg.exec_() != QtWidgets.QDialog.Accepted:
                return
            formula = str(dlg.formula_text() or "")
            self._calc_formula_by_cc[cc] = formula
            preview = self._preview_formula_text(formula)
            it = self.calcTable.item(row, CCOL_FORMULA)
            if it is None:
                it = QtWidgets.QTableWidgetItem("")
                self.calcTable.setItem(row, CCOL_FORMULA, it)
            it.setText(preview)
            it.setToolTip(formula)
            ok = self._rebuild_calc_engine(update_core=True, test_runtime=True)
            err = str(self._calc_compile_errors.get(cc, "") or "")
            if err:
                QtWidgets.QMessageBox.warning(self, "Formula non valida", err)
                dlg.show_error(err)
                continue
            if not ok:
                dlg.show_error("Formula non valida.")
                continue
            return

    def _on_calc_item_changed(self, item: QtWidgets.QTableWidgetItem) -> None:
        if item is None:
            return
        if self._building_calc_table or self._auto_change:
            return

        row = item.row()
        col = item.column()
        cc = self._calc_channel_id_for_row(row)

        if col == CCOL_ENABLE:
            formula = str(self._calc_formula_by_cc.get(cc, "") or "").strip()
            err = str(self._calc_compile_errors.get(cc, "") or "")
            if not formula or err:
                self._auto_change = True
                item.setCheckState(QtCore.Qt.Unchecked)
                self._auto_change = False
                if err:
                    QtWidgets.QMessageBox.warning(self, "Formula non valida", err)
            enabled = bool(item.checkState() == QtCore.Qt.Checked)
            if not enabled:
                # Disabilitazione: reset immediato del canale calcolato a zero.
                self._calc_last_value_raw[cc] = 0.0
                self._calc_zero_by_cc[cc] = None
                try:
                    it_val = self.calcTable.item(row, CCOL_VALUE)
                    if it_val is not None:
                        it_val.setText("0.0")
                    it_zero = self.calcTable.item(row, CCOL_ZERO_VAL)
                    if it_zero is not None:
                        it_zero.setText("0.0")
                except Exception:
                    pass
            self._refresh_calc_engine_enabled()
            self._push_calculated_channels_to_core()
            self._sync_calc_plot_curves()
            return

        if col == CCOL_LABEL:
            entered = (item.text() or "").strip() or cc
            dedup = self._dedupe_channel_name(entered, self._existing_channel_names_lower(exclude_calc_row=row))
            if dedup != entered:
                self._auto_change = True
                item.setText(dedup)
                self._auto_change = False
            self._push_calculated_channels_to_core()
            self._rebuild_legends()
            self._sync_calc_plot_curves()
            return

        if col == CCOL_PLOT:
            self._sync_calc_plot_curves()
            return

    def _on_zero_calc_button_clicked(self, channel_id: str) -> None:
        cc = str(channel_id or "").strip()
        if not cc:
            return
        last = self._calc_last_value_raw.get(cc, None)
        row = self._find_calc_row_by_cc(cc)
        if row < 0:
            return
        if last is None:
            self._calc_zero_by_cc[cc] = 0.0
            try:
                self.calcTable.item(row, CCOL_ZERO_VAL).setText("0.0")
            except Exception:
                pass
            return
        self._calc_zero_by_cc[cc] = float(last)
        try:
            self.calcTable.item(row, CCOL_ZERO_VAL).setText(f"{float(last):.6g}")
        except Exception:
            pass

    def _calc_rows_payload(self) -> List[Dict[str, Any]]:
        rows: List[Dict[str, Any]] = []
        for r in range(self.calcTable.rowCount()):
            cc = self._calc_channel_id_for_row(r)
            it_enable = self.calcTable.item(r, CCOL_ENABLE)
            it_plot = self.calcTable.item(r, CCOL_PLOT)
            it_label = self.calcTable.item(r, CCOL_LABEL)
            rows.append(
                {
                    "channel_id": cc,
                    "formula": str(self._calc_formula_by_cc.get(cc, "") or ""),
                    "enabled": bool(it_enable and it_enable.checkState() == QtCore.Qt.Checked),
                    "plot_enabled": bool(it_plot and it_plot.checkState() == QtCore.Qt.Checked),
                    "name": str((it_label.text() if it_label else cc) or cc).strip() or cc,
                    "zero": self._calc_zero_by_cc.get(cc, None),
                }
            )
        return rows

    def _push_calculated_channels_to_core(self) -> None:
        try:
            if hasattr(self.acq, "set_calculated_channels"):
                self.acq.set_calculated_channels(self._calc_rows_payload())
        except Exception:
            pass

    def _on_calc_view_toggled(self, _checked: bool) -> None:
        self._update_chart_view_buttons_style()
        self._calc_curve_layout_dirty = True
        self._sync_calc_plot_curves()
        self._trim_plot_history_buffers()

    def _on_phys_view_toggled(self, _checked: bool) -> None:
        self._update_chart_view_buttons_style()
        self._calc_curve_layout_dirty = True
        self._ensure_phys_plot_curves(
            show_phys=bool(self.chkPhysViewEnable.isChecked()),
            instant_enabled=bool(getattr(self, '_instant_plot_enabled', True)),
        )
        self._trim_plot_history_buffers()


    def _on_instant_view_toggled(self, checked: bool) -> None:
        self._instant_plot_enabled = bool(checked)
        self._calc_curve_layout_dirty = True
        self._ensure_phys_plot_curves(
            show_phys=bool(self.chkPhysViewEnable.isChecked()),
            instant_enabled=bool(self._instant_plot_enabled),
        )
        self._sync_calc_plot_curves()
        if not self._instant_plot_enabled:
            for curve in list(getattr(self, '_instant_curves_by_phys', {}).values()):
                try:
                    curve.clear()
                except Exception:
                    pass
            for curve in list(getattr(self, '_instant_curves_by_calc', {}).values()):
                try:
                    curve.clear()
                except Exception:
                    pass
        self._trim_plot_history_buffers()

    def _trim_plot_history_buffers(self) -> None:
        show_phys = bool(self.chkPhysViewEnable.isChecked())
        show_calc = bool(self.chkCalcViewEnable.isChecked())

        if not show_phys:
            for phys in list(self._chart_curves_by_phys.keys()):
                self._release_curve_to_pool('_curve_pool_chart_phys', self.pgChart, self._chart_curves_by_phys.get(phys))
                self._chart_curves_by_phys.pop(phys, None)
            for phys in list(self._instant_curves_by_phys.keys()):
                self._release_curve_to_pool('_curve_pool_instant_phys', self.pgInstant, self._instant_curves_by_phys.get(phys))
                self._instant_curves_by_phys.pop(phys, None)

        if not show_calc:
            for cc in list(self._chart_curves_by_calc.keys()):
                self._release_curve_to_pool('_curve_pool_chart_calc', self.pgChart, self._chart_curves_by_calc.get(cc))
                self._chart_curves_by_calc.pop(cc, None)
            for cc in list(self._instant_curves_by_calc.keys()):
                self._release_curve_to_pool('_curve_pool_instant_calc', self.pgInstant, self._instant_curves_by_calc.get(cc))
                self._instant_curves_by_calc.pop(cc, None)

        # Keep x/y history aligned when plot visibility changes.
        try:
            self._chart_x.clear()
        except Exception:
            pass
        try:
            self._preview_queue.clear()
        except Exception:
            pass
        for dq in self._chart_y_by_phys.values():
            try:
                dq.clear()
            except Exception:
                pass
        for dq in self._chart_y_by_calc.values():
            try:
                dq.clear()
            except Exception:
                pass
        self._rebuild_legends()

    def _build_preview_indices(self, t_arr: np.ndarray, ref_blocks: List[np.ndarray]) -> np.ndarray:
        try:
            n = int(np.asarray(t_arr).size)
        except Exception:
            n = 0
        if n <= 0:
            return np.zeros((0,), dtype=np.int64)

        target = int(getattr(self, "_preview_points_per_block", 1200) or 1200)
        if target < 64:
            target = 64

        if n <= target or not bool(getattr(self, "_preview_minmax_enabled", True)):
            return np.arange(n, dtype=np.int64)

        ref = None
        for arr in ref_blocks or []:
            try:
                a = np.asarray(arr, dtype=np.float32).reshape(-1)
            except Exception:
                continue
            if int(a.size) == n:
                ref = a
                break

        if ref is None:
            return np.linspace(0, n - 1, num=min(n, target), dtype=np.int64)

        bins = max(1, target // 2)

        edges = np.empty(bins + 1, dtype=np.int64)
        edges[:] = np.linspace(0, n, bins + 1, dtype=np.int64, endpoint=True)

        need = bins * 2 + 4
        scratch = getattr(self, "_preview_idx_scratch", None)
        if not isinstance(scratch, np.ndarray) or scratch.dtype != np.int64 or scratch.size < need:
            scratch = np.empty(need, dtype=np.int64)
            self._preview_idx_scratch = scratch

        k = 0
        for i in range(bins):
            a = int(edges[i])
            b = int(edges[i + 1])
            if b <= a:
                continue
            seg = ref[a:b]
            if seg.size <= 0:
                continue
            try:
                lo = a + int(np.nanargmin(seg))
            except Exception:
                lo = a
            try:
                hi = a + int(np.nanargmax(seg))
            except Exception:
                hi = b - 1
            if lo <= hi:
                scratch[k] = lo
                scratch[k + 1] = hi
            else:
                scratch[k] = hi
                scratch[k + 1] = lo
            k += 2

        if k <= 0:
            return np.linspace(0, n - 1, num=min(n, target), dtype=np.int64)

        idx = np.asarray(scratch[:k], dtype=np.int64)
        idx = idx[(idx >= 0) & (idx < n)]
        if idx.size <= 0:
            return np.linspace(0, n - 1, num=min(n, target), dtype=np.int64)

        idx = np.unique(idx)
        if idx[0] != 0:
            idx = np.insert(idx, 0, 0)
        if idx[-1] != (n - 1):
            idx = np.append(idx, n - 1)

        if idx.size > target:
            step = max(1, int(np.ceil(float(idx.size) / float(target))))
            idx = idx[::step]
            if idx[-1] != (n - 1):
                idx = np.append(idx, n - 1)

        return idx

    def _buffer_to_numpy(self, buf: Any, dtype=np.float32) -> np.ndarray:
        if buf is None:
            return np.array([], dtype=dtype)
        try:
            if hasattr(buf, "to_numpy"):
                return np.asarray(buf.to_numpy(dtype=dtype), dtype=dtype)
        except Exception:
            pass
        try:
            n = int(len(buf))
            if n <= 0:
                return np.array([], dtype=dtype)
            return np.fromiter(buf, dtype=dtype, count=n)
        except Exception:
            return np.array([], dtype=dtype)

    def _get_subsample_indices(self, n: int, step: int) -> np.ndarray:
        n = int(n)
        step = max(1, int(step))
        if n <= 0:
            return np.zeros((0,), dtype=np.int64)
        if step <= 1:
            return np.arange(n, dtype=np.int64)
        cache = getattr(self, "_plot_sample_idx_cache", None)
        if not isinstance(cache, dict):
            cache = {}
            self._plot_sample_idx_cache = cache
        key = (n, step)
        idx = cache.get(key)
        if isinstance(idx, np.ndarray) and idx.size > 0:
            return idx
        idx = np.arange(0, n, step, dtype=np.int64)
        if idx.size <= 0 or idx[-1] != (n - 1):
            idx = np.append(idx, n - 1)
        cache[key] = idx
        max_entries = int(getattr(self, "_plot_sample_idx_cache_limit", 32) or 32)
        if len(cache) > max_entries:
            # discard oldest insertion (dict preserves order in py3.7+)
            try:
                first_key = next(iter(cache.keys()))
                cache.pop(first_key, None)
            except Exception:
                pass
        return idx

    def _sample_for_plot(self, arr: np.ndarray, step: int) -> np.ndarray:
        if not isinstance(arr, np.ndarray):
            arr = np.asarray(arr, dtype=np.float32)
        if arr.size <= 1:
            return arr
        step = max(1, int(step))
        if step <= 1:
            return arr
        idx = self._get_subsample_indices(int(arr.size), step)
        if idx.size <= 0:
            return arr
        try:
            return arr[idx]
        except Exception:
            return arr[::step]

    def _is_plots_tab_active(self) -> bool:
        try:
            if not hasattr(self, "tabs"):
                return True
            if hasattr(self, "_plots_tab_index"):
                return int(self.tabs.currentIndex()) == int(getattr(self, "_plots_tab_index", -1))
            idx = int(self.tabs.currentIndex())
            txt = str(self.tabs.tabText(idx) if idx >= 0 else "").strip().lower()
            return txt.startswith("graf")
        except Exception:
            return True

    def _recompute_history_capacity(self, force: bool = False) -> None:
        now = time.monotonic()
        cooldown = float(getattr(self, "_history_adjust_cooldown_s", 1.2) or 1.2)
        if (not force) and ((now - float(getattr(self, "_last_history_adjust_ts", 0.0) or 0.0)) < cooldown):
            return

        try:
            active_phys = max(1, int(len(getattr(self, "_current_phys_order", []) or [])))
        except Exception:
            active_phys = 1
        try:
            active_calc = max(0, int(len(getattr(self, "_chart_curves_by_calc", {}) or {})))
        except Exception:
            active_calc = 0
        active_total = max(1, active_phys + active_calc)

        plot_w = 1400
        try:
            plot_w = max(320, int(self.pgChart.width()))
        except Exception:
            pass

        min_pts = int(getattr(self, "_history_min_points", 1200) or 1200)
        max_pts = int(getattr(self, "_history_max_points", 12000) or 12000)
        budget_pts = int(getattr(self, "_history_budget_points", 220000) or 220000)

        width_target = max(min_pts, min(max_pts, int(plot_w * 4)))
        budget_target = max(min_pts, min(max_pts, int(budget_pts / max(1, active_total))))
        if active_total <= 2:
            target = max(width_target, budget_target)
        else:
            target = min(width_target, budget_target)
        target = max(min_pts, min(max_pts, int(target)))

        current = int(getattr(self, "_chart_history_points", target) or target)
        if (not force) and abs(target - current) < 256:
            return

        self._chart_history_points = int(target)
        try:
            self._chart_x.resize(int(target))
        except Exception:
            pass
        for buf in list(getattr(self, "_chart_y_by_phys", {}).values()):
            try:
                buf.resize(int(target))
            except Exception:
                pass
        for buf in list(getattr(self, "_chart_y_by_calc", {}).values()):
            try:
                buf.resize(int(target))
            except Exception:
                pass
        try:
            cache = getattr(self, "_plot_sample_idx_cache", None)
            if isinstance(cache, dict):
                cache.clear()
        except Exception:
            pass
        self._last_history_adjust_ts = now


    def _chart_series_key(self, kind: str, key: str) -> str:
        return f"{kind}:{key}"

    def _chart_mode(self) -> str:
        return "overlay"

    def _chart_focus(self) -> str:
        try:
            return str(self.cmbChartFocus.currentData(QtCore.Qt.UserRole) or "")
        except Exception:
            return ""

    def _chart_relative_enabled(self) -> bool:
        try:
            return bool(self.chkChartRelativeTime.isChecked())
        except Exception:
            return True

    def _chart_robust_enabled(self) -> bool:
        try:
            return bool(self.chkChartRobustY.isChecked())
        except Exception:
            return True

    def _chart_lock_y_enabled(self) -> bool:
        try:
            return bool(self.chkChartLockY.isChecked())
        except Exception:
            return False

    def _chart_window_seconds(self) -> float:
        try:
            return max(0.0, float(self.spinChartWindowSec.value()))
        except Exception:
            return 0.0

    def _refresh_chart_focus_combo(self) -> None:
        if not hasattr(self, "cmbChartFocus"):
            return
        try:
            current = self._chart_focus()
            items = [("Tutti", "")]
            for phys in list(getattr(self, "_current_phys_order", []) or []):
                label = self._label_by_phys.get(phys, phys)
                items.append((f"{label}", self._chart_series_key("phys", phys)))
            for cc in list(getattr(self, "_chart_curves_by_calc", {}).keys()):
                label = cc
                r = self._find_calc_row_by_cc(cc)
                if r >= 0:
                    it = self.calcTable.item(r, CCOL_LABEL)
                    label = str((it.text() if it else cc) or cc).strip() or cc
                items.append((f"{label} [calc]", self._chart_series_key("calc", cc)))

            signature = tuple(items)
            if signature == getattr(self, "_chart_focus_signature_cache", None):
                return

            self._chart_focus_signature_cache = signature
            self.cmbChartFocus.blockSignals(True)
            self.cmbChartFocus.clear()
            for txt_item, key in items:
                self.cmbChartFocus.addItem(txt_item, key)
            idx = 0
            if current:
                for i in range(self.cmbChartFocus.count()):
                    if str(self.cmbChartFocus.itemData(i, QtCore.Qt.UserRole) or "") == current:
                        idx = i
                        break
            self.cmbChartFocus.setCurrentIndex(idx)
        except Exception:
            pass
        finally:
            try:
                self.cmbChartFocus.blockSignals(False)
            except Exception:
                pass

    def _on_chart_view_option_changed(self, *_args):
        self._legend_signature_cache = None
        self._update_chart_relative_button_style()

    def _on_chart_mode_changed(self, *_args):
        self._on_chart_view_option_changed()

    def _on_chart_focus_changed(self, *_args):
        self._on_chart_view_option_changed()
    def _update_chart_relative_button_style(self) -> None:
        try:
            btn = getattr(self, "chkChartRelativeTime", None)
            if not isinstance(btn, QtWidgets.QPushButton):
                return
            if bool(btn.isChecked()):
                btn.setStyleSheet(
                    "QPushButton {background:#22c55e; color:#ffffff; border:1px solid #16a34a; font-weight:700;}"
                    " QPushButton:hover {background:#16a34a;}"
                )
            else:
                btn.setStyleSheet(
                    "QPushButton {background:#9ca3af; color:#111827; border:1px solid #6b7280; font-weight:600;}"
                    " QPushButton:hover {background:#6b7280; color:#ffffff;}"
                )
        except Exception:
            pass

    
    def _update_chart_view_buttons_style(self) -> None:
        try:
            for btn in (self.chkPhysViewEnable, self.chkCalcViewEnable):
                if not isinstance(btn, QtWidgets.QPushButton):
                    continue
                if bool(btn.isChecked()):
                    btn.setStyleSheet(
                        "QPushButton {background:#22c55e; color:#ffffff; border:1px solid #16a34a; font-weight:700;}"
                        " QPushButton:hover {background:#16a34a;}"
                    )
                else:
                    btn.setStyleSheet(
                        "QPushButton {background:#9ca3af; color:#111827; border:1px solid #6b7280; font-weight:600;}"
                        " QPushButton:hover {background:#6b7280; color:#ffffff;}"
                    )
        except Exception:
            pass
    def _on_chart_y_limits_changed(self, *_args):
        try:
            mode = str(self.cmbChartYScale.currentData(QtCore.Qt.UserRole) or "autoscale").strip().lower()
            if mode == "lock":
                self._on_chart_y_scale_changed(show_popup=True)
        except Exception:
            pass

    def _on_chart_y_scale_changed(self, *_args, show_popup: bool = True):
        try:
            mode = str(self.cmbChartYScale.currentData(QtCore.Qt.UserRole) or "autoscale").strip().lower()
            lock = (mode == "lock")
            for w in (self.lblChartYMin, self.spinChartYMin, self.lblChartYMax, self.spinChartYMax):
                w.setVisible(lock)

            if lock:
                y_min = float(self.spinChartYMin.value())
                y_max = float(self.spinChartYMax.value())
                if y_min >= y_max:
                    self.spinChartYMin.setValue(-1.0)
                    self.spinChartYMax.setValue(1.0)
                    if show_popup:
                        QtWidgets.QMessageBox.warning(self, "Scala Y", "Y min >= Y max valori ignorati")
                    try:
                        self.cmbChartYScale.blockSignals(True)
                        self.cmbChartYScale.setCurrentIndex(0)
                    finally:
                        self.cmbChartYScale.blockSignals(False)
                    lock = False
                else:
                    self._chart_locked_ylim = (y_min, y_max)

            self.chkChartLockY.setChecked(lock)
            self.chkChartRobustY.setChecked(not lock)
            if not lock:
                self._chart_locked_ylim = None
                for w in (self.lblChartYMin, self.spinChartYMin, self.lblChartYMax, self.spinChartYMax):
                    w.setVisible(False)
            self._on_chart_view_option_changed()
        except Exception:
            pass

    def _on_chart_preset_changed(self, *_args):
        try:
            name = str(self.cmbChartPreset.currentText() or "").strip() or "Operativo"
            self._apply_chart_preset(name)
        except Exception:
            pass

    def _on_chart_cursor_moved(self, *_args):
        self._update_chart_cursor_info()

    def _apply_chart_preset(self, name: str, force: bool = False) -> None:
        preset = str(name or "").strip().lower()
        if preset not in ("operativo", "diagnostica", "prestazioni"):
            preset = "operativo"
        if (not force) and str(getattr(self, "_chart_preset_active", "")).strip().lower() == preset:
            return
        self._chart_preset_active = preset
        try:
            if preset == "diagnostica":
                self.cmbChartMode.setCurrentText("Stacked")
                self.chkChartRelativeTime.setChecked(True)
                self.spinChartWindowSec.setValue(0.0)
                self.chkChartRobustY.setChecked(False)
                self.chkChartLockY.setChecked(False)
                self.chkChartCursors.setChecked(True)
            elif preset == "prestazioni":
                self.cmbChartMode.setCurrentText("Overlay")
                self.chkChartRelativeTime.setChecked(True)
                self.spinChartWindowSec.setValue(20.0)
                self.chkChartRobustY.setChecked(True)
                self.chkChartLockY.setChecked(False)
                self.chkChartCursors.setChecked(False)
                self._plot_render_max_points = min(int(getattr(self, "_plot_render_max_points", 2500) or 2500), 1800)
            else:
                self.cmbChartMode.setCurrentText("Overlay")
                self.chkChartRelativeTime.setChecked(True)
                self.spinChartWindowSec.setValue(60.0)
                self.chkChartRobustY.setChecked(True)
                self.chkChartLockY.setChecked(False)
                self.chkChartCursors.setChecked(False)
        except Exception:
            pass

    def _on_chart_fit_clicked(self):
        try:
            self._chart_locked_ylim = None
            if hasattr(self, "chkChartLockY"):
                self.chkChartLockY.setChecked(False)
            self.pgChart.getPlotItem().enableAutoRange(x=True, y=True)
            self.pgChart.getPlotItem().autoRange()
        except Exception:
            pass

    def _on_chart_reset_view_clicked(self):
        try:
            self.spinChartWindowSec.setValue(0.0)
            self.chkChartRelativeTime.setChecked(True)
            if hasattr(self, "cmbChartYScale"):
                self.cmbChartYScale.setCurrentIndex(0)
                self._on_chart_y_scale_changed(show_popup=False)
            if hasattr(self, "cmbChartFocus"):
                self.cmbChartFocus.setCurrentIndex(0)
            self._chart_locked_ylim = None
        except Exception:
            pass

    def _update_chart_cursor_info(self):
        try:
            enabled = bool(getattr(self, "chkChartCursors", None) and self.chkChartCursors.isChecked())
            if not enabled:
                self._chart_cursor_a.hide(); self._chart_cursor_b.hide()
                if hasattr(self, "lblChartCursorInfo"):
                    self.lblChartCursorInfo.setText("")
                return
            series_map = dict(getattr(self, "_chart_last_series_by_key", {}) or {})
            if not series_map:
                if hasattr(self, "lblChartCursorInfo"):
                    self.lblChartCursorInfo.setText("Cursori: nessun dato disponibile")
                return
            self._chart_cursor_a.show(); self._chart_cursor_b.show()
            focus = self._chart_focus()
            if focus not in series_map:
                focus = next(iter(series_map.keys()))
            x_arr, y_arr, label = series_map.get(focus, (None, None, focus))
            if not isinstance(x_arr, np.ndarray) or not isinstance(y_arr, np.ndarray):
                return
            m = np.isfinite(x_arr) & np.isfinite(y_arr)
            if int(np.count_nonzero(m)) < 2:
                return
            xf = x_arr[m]; yf = y_arr[m]
            xmin = float(xf[0]); xmax = float(xf[-1])
            if xmax <= xmin:
                xmax = xmin + 1.0
            xa = float(self._chart_cursor_a.value()); xb = float(self._chart_cursor_b.value())
            if (not np.isfinite(xa)) or xa < xmin or xa > xmax:
                xa = xmin + 0.25 * (xmax - xmin); self._chart_cursor_a.setValue(xa)
            if (not np.isfinite(xb)) or xb < xmin or xb > xmax or abs(xb - xa) < 1e-12:
                xb = xmin + 0.75 * (xmax - xmin); self._chart_cursor_b.setValue(xb)
            ia = int(np.clip(np.searchsorted(xf, xa, side='left'), 0, len(xf) - 1))
            ib = int(np.clip(np.searchsorted(xf, xb, side='left'), 0, len(xf) - 1))
            ya = float(yf[ia]); yb = float(yf[ib])
            if hasattr(self, "lblChartCursorInfo"):
                self.lblChartCursorInfo.setText(f"Cursori [{label}]  A: x={xa:.3f}, y={ya:.6g}  |  B: x={xb:.3f}, y={yb:.6g}  |  dT={xb-xa:.3f}, dY={yb-ya:.6g}")
        except Exception:
            pass


    def _drain_preview_queue(self, show_phys: bool, show_calc: bool) -> None:
        q = getattr(self, "_preview_queue", None)
        if q is None:
            return
        budget = int(getattr(self, "_preview_apply_blocks_per_tick", 3) or 3)
        if budget < 1:
            budget = 1
        loops = min(int(len(q)), budget)
        for _ in range(loops):
            try:
                blk = q.popleft()
            except Exception:
                break
            if not isinstance(blk, dict):
                continue
            t_prev = np.asarray(blk.get("t", []), dtype=np.float64).reshape(-1)
            if t_prev.size <= 0:
                continue
            try:
                last_t = float(getattr(self, "_chart_last_preview_t", np.nan))
            except Exception:
                last_t = np.nan
            t0 = float(t_prev[0]) if t_prev.size > 0 else np.nan
            if bool(getattr(self, "_chart_gap_between_blocks", True)) and np.isfinite(last_t) and np.isfinite(t0) and (t0 > last_t):
                self._chart_x.append(np.float64(np.nan))
                for buf in list(getattr(self, "_chart_y_by_phys", {}).values()):
                    try:
                        buf.append(np.float32(np.nan))
                    except Exception:
                        pass
                for buf in list(getattr(self, "_chart_y_by_calc", {}).values()):
                    try:
                        buf.append(np.float32(np.nan))
                    except Exception:
                        pass
            self._chart_x.extend(t_prev)
            if show_phys:
                for phys, y in dict(blk.get("phys", {}) or {}).items():
                    buf = self._chart_y_by_phys.get(phys)
                    if buf is None:
                        continue
                    try:
                        buf.extend(np.asarray(y, dtype=np.float32).reshape(-1))
                    except Exception:
                        pass
            if show_calc:
                for cc, y in dict(blk.get("calc", {}) or {}).items():
                    buf = self._chart_y_by_calc.get(cc)
                    if buf is None:
                        buf = FloatRingBuffer(int(getattr(self, "_chart_history_points", 12000) or 12000))
                        self._chart_y_by_calc[cc] = buf
                    try:
                        buf.extend(np.asarray(y, dtype=np.float32).reshape(-1))
                    except Exception:
                        pass
            try:
                finite = t_prev[np.isfinite(t_prev)]
                if finite.size > 0:
                    self._chart_last_preview_t = float(finite[-1])
            except Exception:
                pass

    def _rr_select(self, items: List[Any], cursor_attr: str, budget: int) -> List[Any]:
        if not items:
            return []
        n = len(items)
        if budget <= 0 or n <= budget:
            setattr(self, cursor_attr, 0)
            return items
        start = int(getattr(self, cursor_attr, 0) or 0) % n
        out = [items[(start + i) % n] for i in range(budget)]
        setattr(self, cursor_attr, (start + budget) % n)
        return out

    def _update_render_guardrail(self, frame_ms: float) -> None:
        try:
            alpha = 0.2
            prev = float(getattr(self, "_refresh_ewma_ms", 0.0) or 0.0)
            if prev <= 0.0:
                prev = float(frame_ms)
            ewma = (1.0 - alpha) * prev + alpha * float(frame_ms)
            self._refresh_ewma_ms = ewma

            q = getattr(self, "_preview_queue", None)
            q_len = int(len(q)) if q is not None else 0
            q_cap = int(getattr(q, "maxlen", 0) or 0)
            q_ratio = (float(q_len) / float(q_cap)) if q_cap > 0 else 0.0

            high_ms = float(getattr(self, "_guardrail_high_ms", 35.0) or 35.0)
            low_ms = float(getattr(self, "_guardrail_low_ms", 18.0) or 18.0)
            rss_mb = float(self._get_process_rss_mb())
            rss_hi = float(getattr(self, "_guardrail_rss_high_mb", 900.0) or 900.0)
            rss_lo = float(getattr(self, "_guardrail_rss_low_mb", 720.0) or 720.0)

            high = (ewma >= high_ms) or (q_ratio >= 0.8) or (rss_mb > 0.0 and rss_mb >= rss_hi)
            low = (ewma <= low_ms) and (q_ratio <= 0.2) and ((rss_mb <= 0.0) or (rss_mb <= rss_lo))

            if high:
                self._guardrail_active = True
                self._plot_render_max_points = max(
                    int(getattr(self, "_guardrail_min_render_points", 700) or 700),
                    int(float(self._plot_render_max_points) * 0.9),
                )
                self._render_budget_curves = max(2, int(float(self._render_budget_curves) * 0.9))
                self._render_budget_curves_instant = max(2, int(float(self._render_budget_curves_instant) * 0.9))
                self._preview_apply_blocks_per_tick = max(1, int(float(self._preview_apply_blocks_per_tick) * 0.9))
                return

            if not low:
                return

            default_points = int(getattr(self, "_plot_render_max_points_default", 2500) or 2500)
            default_chart_budget = int(getattr(self, "_render_budget_curves_default", 8) or 8)
            default_instant_budget = int(getattr(self, "_render_budget_curves_instant_default", 8) or 8)
            default_preview_budget = int(getattr(self, "_preview_apply_blocks_per_tick_default", 3) or 3)

            self._plot_render_max_points = min(default_points, int(self._plot_render_max_points + 120))
            self._render_budget_curves = min(default_chart_budget, int(self._render_budget_curves + 1))
            self._render_budget_curves_instant = min(default_instant_budget, int(self._render_budget_curves_instant + 1))
            self._preview_apply_blocks_per_tick = min(default_preview_budget, int(self._preview_apply_blocks_per_tick + 1))

            if (
                self._plot_render_max_points >= default_points
                and self._render_budget_curves >= default_chart_budget
                and self._render_budget_curves_instant >= default_instant_budget
                and self._preview_apply_blocks_per_tick >= default_preview_budget
            ):
                self._guardrail_active = False
        except Exception:
            pass
    def _get_process_rss_mb(self) -> float:
        try:
            import psutil  # type: ignore
            return float(psutil.Process(os.getpid()).memory_info().rss) / (1024.0 * 1024.0)
        except Exception:
            return 0.0

    def _window_is_background(self) -> bool:
        try:
            if not self.isVisible():
                return True
            w = self.window() if hasattr(self, "window") else self
            if w is not None and bool(w.isMinimized()):
                return True
            app = QtWidgets.QApplication.instance()
            aw = app.activeWindow() if app is not None else None
            if aw is None:
                return False
            return (aw is not self) and (w is None or aw is not w)
        except Exception:
            return False

    def _update_ui_render_profile(self) -> None:
        try:
            bg = bool(self._window_is_background())
            if bg == bool(getattr(self, "_ui_profile_background", False)):
                return
            self._ui_profile_background = bg

            if bg:
                try:
                    if hasattr(self, "guiTimer") and self.guiTimer is not None:
                        self.guiTimer.setInterval(int(getattr(self, "_bg_gui_interval", 300) or 300))
                except Exception:
                    pass
                self._render_budget_curves = max(1, int(getattr(self, "_bg_render_budget_curves", 2) or 2))
                self._render_budget_curves_instant = max(1, int(getattr(self, "_bg_render_budget_curves_instant", 2) or 2))
                self._preview_apply_blocks_per_tick = max(1, int(getattr(self, "_bg_preview_apply_blocks", 1) or 1))
            else:
                try:
                    if hasattr(self, "guiTimer") and self.guiTimer is not None:
                        self.guiTimer.setInterval(int(getattr(self, "_default_gui_interval", 120) or 120))
                except Exception:
                    pass
                self._render_budget_curves = max(1, int(getattr(self, "_render_budget_curves_default", 8) or 8))
                self._render_budget_curves_instant = max(1, int(getattr(self, "_render_budget_curves_instant_default", 8) or 8))
                self._preview_apply_blocks_per_tick = max(1, int(getattr(self, "_preview_apply_blocks_per_tick_default", 3) or 3))
        except Exception:
            pass

    def _sample_performance_metrics(self) -> None:
        try:
            rss_mb = float(self._get_process_rss_mb())
            q = getattr(self, "_preview_queue", None)
            q_len = int(len(q)) if q is not None else 0
            q_cap = int(getattr(q, "maxlen", 0) or 0)
            row = {
                "ts": float(time.time()),
                "rss_mb": rss_mb,
                "frame_ms_ewma": float(getattr(self, "_refresh_ewma_ms", 0.0) or 0.0),
                "queue_len": q_len,
                "queue_cap": q_cap,
                "queue_dropped": int(getattr(self, "_preview_queue_dropped", 0) or 0),
                "budget_chart": int(getattr(self, "_render_budget_curves", 0) or 0),
                "budget_instant": int(getattr(self, "_render_budget_curves_instant", 0) or 0),
                "budget_preview": int(getattr(self, "_preview_apply_blocks_per_tick", 0) or 0),
                "gui_interval_ms": int(self.guiTimer.interval()) if hasattr(self, "guiTimer") else 0,
                "guardrail": int(bool(getattr(self, "_guardrail_active", False))),
                "background": int(bool(getattr(self, "_ui_profile_background", False))),
            }
            perf = getattr(self, "_perf_metrics", None)
            if isinstance(perf, deque):
                perf.append(row)

            if not bool(getattr(self, "_perf_logging_enabled", False)):
                return
            log_path = str(getattr(self, "_perf_log_path", "") or "").strip()
            if not log_path:
                return
            need_header = not os.path.isfile(log_path)
            with open(log_path, "a", encoding="utf-8-sig") as f:
                if need_header:
                    f.write("ts,rss_mb,frame_ms_ewma,queue_len,queue_cap,queue_dropped,budget_chart,budget_instant,budget_preview,gui_interval_ms,guardrail,background\n")
                f.write(
                    f"{row['ts']:.6f},{row['rss_mb']:.3f},{row['frame_ms_ewma']:.3f},{row['queue_len']},{row['queue_cap']},{row['queue_dropped']},"
                    f"{row['budget_chart']},{row['budget_instant']},{row['budget_preview']},{row['gui_interval_ms']},{row['guardrail']},{row['background']}\n"
                )
        except Exception:
            pass

    def _build_legend_signature(self) -> Tuple[Any, ...]:
        try:
            phys = tuple((str(p), str(getattr(self, "_start_label_by_phys", {}).get(p, getattr(self, "_label_by_phys", {}).get(p, p)))) for p in list(getattr(self, "_current_phys_order", []) or []))
        except Exception:
            phys = tuple()
        try:
            calc = tuple(sorted(str(k) for k in dict(getattr(self, "_chart_curves_by_calc", {}) or {}).keys()))
        except Exception:
            calc = tuple()
        try:
            show_phys = bool(self.chkPhysViewEnable.isChecked())
        except Exception:
            show_phys = False
        try:
            show_calc = bool(self.chkCalcViewEnable.isChecked())
        except Exception:
            show_calc = False
        return (phys, calc, show_phys, show_calc)

    def _acquire_curve_from_pool(self, pool_attr: str, plot_widget: Any, label: str, color: Any, width: float = 1.5):
        curve = None
        pool = getattr(self, pool_attr, None)
        if isinstance(pool, list) and pool:
            try:
                curve = pool.pop()
            except Exception:
                curve = None
        if curve is None:
            curve = pg.PlotDataItem()
        try:
            curve.clear()
        except Exception:
            pass
        try:
            curve.setPen(pg.mkPen(color=color, width=width))
        except Exception:
            pass
        try:
            curve.setName(label)
        except Exception:
            pass
        try:
            curve.setClipToView(True)
            curve.setDownsampling(auto=True, mode='peak')
        except Exception:
            pass
        try:
            plot_widget.addItem(curve)
        except Exception:
            pass
        return curve

    def _release_curve_to_pool(self, pool_attr: str, plot_widget: Any, curve: Any) -> None:
        if curve is None:
            return
        try:
            plot_widget.removeItem(curve)
        except Exception:
            pass
        try:
            curve.clear()
        except Exception:
            pass
        pool = getattr(self, pool_attr, None)
        if not isinstance(pool, list):
            return
        max_pool = int(getattr(self, '_curve_pool_max', 48) or 48)
        if len(pool) >= max_pool:
            return
        total_limit = int(getattr(self, '_curve_pool_max_total', max_pool * 2) or (max_pool * 2))
        total = 0
        for attr in ('_curve_pool_chart_phys', '_curve_pool_instant_phys', '_curve_pool_chart_calc', '_curve_pool_instant_calc'):
            arr = getattr(self, attr, None)
            if isinstance(arr, list):
                total += len(arr)
        if total >= total_limit:
            return
        pool.append(curve)

    def _ensure_phys_plot_curves(self, show_phys: bool, instant_enabled: bool) -> None:
        expected = set(self._current_phys_order) if show_phys else set()
        changed = False

        for phys in list(self._chart_curves_by_phys.keys()):
            if phys in expected:
                continue
            self._release_curve_to_pool('_curve_pool_chart_phys', self.pgChart, self._chart_curves_by_phys.get(phys))
            self._chart_curves_by_phys.pop(phys, None)
            changed = True

        for phys in list(self._instant_curves_by_phys.keys()):
            if phys in expected and instant_enabled:
                continue
            self._release_curve_to_pool('_curve_pool_instant_phys', self.pgInstant, self._instant_curves_by_phys.get(phys))
            self._instant_curves_by_phys.pop(phys, None)
            changed = True

        if not show_phys:
            if changed:
                self._rebuild_legends()
            return

        num_ch = max(1, len(self._current_phys_order))
        for idx, phys in enumerate(self._current_phys_order):
            base_label = self._label_by_phys.get(phys, phys)
            unit = ''
            if hasattr(self, '_calib_by_phys'):
                try:
                    unit = str(self._calib_by_phys.get(phys, {}).get('unit', '') or '')
                except Exception:
                    unit = ''
            label = f"{base_label} [{unit}]" if unit else base_label
            try:
                color = pg.intColor(idx, hues=max(8, num_ch))
            except Exception:
                color = (255, 0, 0)

            chart_curve = self._chart_curves_by_phys.get(phys)
            if chart_curve is None:
                self._chart_curves_by_phys[phys] = self._acquire_curve_from_pool(
                    '_curve_pool_chart_phys', self.pgChart, label, color, width=1.5
                )
                changed = True
            else:
                try:
                    chart_curve.setName(label)
                    chart_curve.setPen(pg.mkPen(color=color, width=1.5))
                except Exception:
                    pass

            if not instant_enabled:
                continue

            instant_curve = self._instant_curves_by_phys.get(phys)
            if instant_curve is None:
                self._instant_curves_by_phys[phys] = self._acquire_curve_from_pool(
                    '_curve_pool_instant_phys', self.pgInstant, label, color, width=1.5
                )
                changed = True
            else:
                try:
                    instant_curve.setName(label)
                    instant_curve.setPen(pg.mkPen(color=color, width=1.5))
                except Exception:
                    pass

        if changed:
            self._rebuild_legends()

    def _calc_visible_ids(self) -> List[str]:
        if not bool(self.chkCalcViewEnable.isChecked()):
            return []
        out: List[str] = []
        for r in range(self.calcTable.rowCount()):
            cc = self._calc_channel_id_for_row(r)
            formula = str(self._calc_formula_by_cc.get(cc, "") or "").strip()
            if not formula:
                continue
            if cc in self._calc_compile_errors:
                continue
            it_enable = self.calcTable.item(r, CCOL_ENABLE)
            it_plot = self.calcTable.item(r, CCOL_PLOT)
            if not it_enable or it_enable.checkState() != QtCore.Qt.Checked:
                continue
            if not it_plot or it_plot.checkState() != QtCore.Qt.Checked:
                continue
            out.append(cc)
        return out

    def _sync_calc_plot_curves(self) -> None:
        show_calc = bool(self.chkCalcViewEnable.isChecked())
        instant_enabled = bool(getattr(self, '_instant_plot_enabled', True))
        visible = set(self._calc_visible_ids()) if show_calc else set()

        for cc in list(self._chart_curves_by_calc.keys()):
            if cc in visible and show_calc:
                continue
            self._release_curve_to_pool('_curve_pool_chart_calc', self.pgChart, self._chart_curves_by_calc.get(cc))
            self._chart_curves_by_calc.pop(cc, None)

        for cc in list(self._instant_curves_by_calc.keys()):
            if cc in visible and show_calc and instant_enabled:
                continue
            self._release_curve_to_pool('_curve_pool_instant_calc', self.pgInstant, self._instant_curves_by_calc.get(cc))
            self._instant_curves_by_calc.pop(cc, None)

        phys_count = max(1, len(self._current_phys_order))
        for idx, cc in enumerate(sorted(visible, key=lambda x: int(x[2:]) if x[2:].isdigit() else 0)):
            if cc not in self._chart_y_by_calc:
                self._chart_y_by_calc[cc] = FloatRingBuffer(int(getattr(self, '_chart_history_points', 12000) or 12000))
            if cc not in self._instant_y_by_calc:
                self._instant_y_by_calc[cc] = np.array([], dtype=float)

            row = self._find_calc_row_by_cc(cc)
            label_item = self.calcTable.item(row, CCOL_LABEL) if row >= 0 else None
            label = str(label_item.text().strip() if label_item else cc) or cc
            color = pg.intColor(phys_count + idx, hues=max(16, phys_count + len(visible)))

            if show_calc:
                if cc not in self._chart_curves_by_calc:
                    self._chart_curves_by_calc[cc] = self._acquire_curve_from_pool(
                        '_curve_pool_chart_calc', self.pgChart, label, color, width=1.3
                    )
                else:
                    try:
                        self._chart_curves_by_calc[cc].setName(label)
                        self._chart_curves_by_calc[cc].setPen(pg.mkPen(color=color, width=1.3))
                    except Exception:
                        pass

            if show_calc and instant_enabled:
                if cc not in self._instant_curves_by_calc:
                    self._instant_curves_by_calc[cc] = self._acquire_curve_from_pool(
                        '_curve_pool_instant_calc', self.pgInstant, label, color, width=1.3
                    )
                else:
                    try:
                        self._instant_curves_by_calc[cc].setName(label)
                        self._instant_curves_by_calc[cc].setPen(pg.mkPen(color=color, width=1.3))
                    except Exception:
                        pass

        self._rebuild_legends()
        self._calc_curve_layout_dirty = False

    def _evaluate_calculated_block(self, phys_eng: Dict[str, np.ndarray]) -> Dict[str, np.ndarray]:
        fs = float(getattr(self.acq, "current_rate_hz", 0.0) or 0.0)
        enabled_phys, _ = self._enabled_phys_and_labels()
        inputs = {k: v for k, v in phys_eng.items() if k in set(enabled_phys)}
        outputs, errors = self._calc_engine.evaluate(inputs, fs, fill_value=0.0)
        self._calc_runtime_errors = {k: v for k, v in errors.items() if str(k).startswith("cc")}

        out_shifted: Dict[str, np.ndarray] = {}
        for cc, arr in outputs.items():
            a = np.asarray(arr, dtype=np.float64)
            if a.ndim == 0:
                a = np.asarray([float(a)], dtype=np.float64)
            baseline = self._calc_zero_by_cc.get(cc, None)
            raw_last = float(a[-1]) if a.size > 0 else 0.0
            self._calc_last_value_raw[cc] = raw_last
            if baseline is not None:
                a = a - float(baseline)
            out_shifted[cc] = np.ascontiguousarray(a, dtype=np.float64)
        return out_shifted

    def _update_calc_table_values(self, calc_data: Dict[str, np.ndarray]) -> None:
        self._building_calc_table = True
        try:
            for r in range(self.calcTable.rowCount()):
                cc = self._calc_channel_id_for_row(r)
                it_enable = self.calcTable.item(r, CCOL_ENABLE)
                enabled = bool(it_enable is not None and it_enable.checkState() == QtCore.Qt.Checked)
                arr = calc_data.get(cc)
                val = float(arr[-1]) if (enabled and isinstance(arr, np.ndarray) and arr.size > 0) else 0.0
                it_val = self.calcTable.item(r, CCOL_VALUE)
                if it_val is not None:
                    it_val.setText(f"{val:.6g}")
                err = str(self._calc_compile_errors.get(cc, "") or self._calc_runtime_errors.get(cc, "") or "")
                if err:
                    self._set_calc_row_error(r, err)
                else:
                    self._clear_calc_row_error(r)
        finally:
            self._building_calc_table = False

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
        self._sync_agent.register_handler("STATUS_SNAPSHOT", self._sync_cmd_status_snapshot)
        self._sync_agent.register_handler("PREPARE_SAVE", self._sync_cmd_prepare_save)
        self._sync_agent.register_handler("CONFIGURE_SYNC", self._sync_cmd_configure_sync)
        self._sync_agent.register_handler("ARM_ACQUISITION", self._sync_cmd_arm_acquisition)
        self._sync_agent.register_handler("START_SYNC", self._sync_cmd_start_sync)
        self._sync_agent.register_handler("START_SAVE", self._sync_cmd_start_save)
        self._sync_agent.register_handler("SET_SYNC_WRITE_CUTOFF", self._sync_cmd_set_sync_write_cutoff)
        self._sync_agent.register_handler("STOP_SAFE", self._sync_cmd_stop_safe)
        self._sync_agent.register_handler("START_MERGE_ASYNC", self._sync_cmd_start_merge_async)
        self._sync_agent.register_handler("MERGE_STATUS", self._sync_cmd_merge_status)
        self._sync_agent.register_handler("STOP_AND_MERGE", self._sync_cmd_stop_and_merge)
        self._sync_agent.register_handler("UNLOCK_UI", self._sync_cmd_unlock_ui)
        self._sync_agent.register_handler("ABORT_PREPARED", self._sync_cmd_abort_prepared)
        self._sync_agent.register_handler("SAVE_WORKSPACE_TO_PATH", self._sync_cmd_save_workspace_to_path)
        self._sync_agent.register_handler("LOAD_WORKSPACE_FROM_PATH", self._sync_cmd_load_workspace_from_path)
        self._sync_agent.register_handler("SHUTDOWN", self._sync_cmd_shutdown)
        self._sync_agent.start(
            {
                "board": "NI9201",
                "pid": int(os.getpid()),
                "device_name": str(self._forced_device_name_from_env() or ""),
            }
        )
        QtCore.QTimer.singleShot(0, self._sync_emit_status_update)

    def _sync_status_snapshot(self) -> Dict[str, Any]:
        device_name = str((self.cmbDevice.currentData() or self.cmbDevice.currentText() or "").strip())
        phys, _labels = self._enabled_phys_and_labels()
        active_channels = int(len(phys))
        fs_max_hz = 0.0
        if device_name and active_channels > 0:
            try:
                fs_max_hz = float(self.acq._compute_per_channel_rate(device_name, active_channels))
            except Exception:
                try:
                    fs_max_hz = float(self.acq.current_rate_hz or 0.0)
                except Exception:
                    fs_max_hz = 0.0
        return {
            "module_id": str(self._sync_agent.module_id() if self._sync_agent is not None else ""),
            "board_number": "9201",
            "device_name": device_name,
            "group_name": str(getattr(self.acq, "_tdms_group_name", lambda: "Acquisition")() or "Acquisition"),
            "active_channels": active_channels,
            "fs_max_hz": float(fs_max_hz if fs_max_hz > 0 else 0.0),
            "current_rate_hz": float(getattr(self.acq, "current_rate_hz", 0.0) or 0.0),
            "is_simulated": self._is_current_device_simulated(),
            "running": bool(getattr(self.acq, "_running", False)),
            "recording": bool(getattr(self.acq, "recording_enabled", False)),
            "samples_acquired": int(getattr(self.acq, "_global_samples", 0) or 0),
            "recording_start_index": int(getattr(self, "_recording_start_sample_index", 0) or 0),
            "samples_recording": int(max(0, int(getattr(self.acq, "_global_samples", 0) or 0) - int(getattr(self, "_recording_start_sample_index", 0) or 0))),
        }

    def _sync_emit_status_update(self):
        if self._sync_agent is None:
            return
        try:
            self._sync_agent.send_event("STATUS_UPDATE", self._sync_status_snapshot())
        except Exception:
            pass

    def _sync_cmd_status_snapshot(self, _payload: Dict[str, Any]) -> Dict[str, Any]:
        return self._sync_status_snapshot()

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
            self._set_stop_button_enabled_for_recording()

    def _update_window_close_button_state(self, recording: Optional[bool] = None) -> None:
        try:
            rec = bool(self.acq.recording_enabled) if recording is None else bool(recording)
        except Exception:
            rec = bool(recording) if recording is not None else False
        allow_close = not bool(rec)
        try:
            flags = self.windowFlags()
            target_flags = flags | QtCore.Qt.WindowCloseButtonHint if allow_close else flags & ~QtCore.Qt.WindowCloseButtonHint
            if target_flags != flags:
                was_visible = self.isVisible()
                self.setWindowFlag(QtCore.Qt.WindowCloseButtonHint, allow_close)
                if was_visible:
                    self.show()
        except Exception:
            pass

    def _set_stop_button_enabled_for_recording(self, recording: Optional[bool] = None) -> None:
        try:
            rec = bool(self.acq.recording_enabled) if recording is None else bool(recording)
        except Exception:
            rec = bool(recording) if recording is not None else False
        allow_local_stop = bool(rec) and (not bool(getattr(self, "_sync_remote_active", False)))
        try:
            self.btnStop.setEnabled(allow_local_stop)
        except Exception:
            pass
        self._update_window_close_button_state(rec)

    def _confirm_user_close_request(self) -> bool:
        box = QtWidgets.QMessageBox(self)
        box.setIcon(QtWidgets.QMessageBox.Question)
        box.setWindowTitle("Conferma chiusura modulo")
        if self._sync_agent is not None:
            box.setText("Chiudere questo modulo?")
            box.setInformativeText("Il modulo verra escluso dallo chassis e dalla sincronizzazione corrente.")
        else:
            box.setText("Chiudere questo modulo?")
            box.setInformativeText("Il modulo verra chiuso completamente.")
        box.setStandardButtons(QtWidgets.QMessageBox.Yes | QtWidgets.QMessageBox.No)
        box.setDefaultButton(QtWidgets.QMessageBox.No)
        return box.exec_() == QtWidgets.QMessageBox.Yes

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
        try:
            self.rateEdit.setToolTip("frequenza di acquisizione del dataset sincronizzato finale")
        except Exception:
            pass

        snap = self._sync_status_snapshot()
        self._sync_emit_status_update()
        return snap

    def _sync_cmd_prepare_save(self, _payload: Dict[str, Any]) -> Dict[str, Any]:
        if not self._device_ready:
            raise RuntimeError("Dispositivo non pronto.")
        phys, _labels = self._enabled_phys_and_labels()
        if not phys:
            snap = self._sync_status_snapshot()
            snap["eligible"] = False
            self._sync_emit_status_update()
            return snap
        if not bool(getattr(self.acq, "_running", False)):
            self._run_without_message_boxes(self._update_acquisition_from_table)
        if not bool(getattr(self.acq, "_running", False)):
            raise RuntimeError("Acquisizione non avviata.")
        snap = self._sync_status_snapshot()
        snap["eligible"] = True
        self._sync_emit_status_update()
        return snap

    def _sync_cmd_configure_sync(self, payload: Dict[str, Any]) -> Dict[str, Any]:
        fs_hz = float(payload.get("fs_hz", 0.0) or 0.0)
        if fs_hz > 0:
            self.rateEdit.setText(str(int(round(fs_hz))))
            self._run_without_message_boxes(self._on_rate_edit_finished)
        snap = self._sync_status_snapshot()
        snap["hardware_supported"] = bool(not self._is_current_device_simulated())
        self._sync_emit_status_update()
        return snap

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
        snap = self._sync_status_snapshot()
        snap["armed"] = True
        self._sync_emit_status_update()
        return snap

    def _sync_cmd_start_sync(self, payload: Dict[str, Any]) -> Dict[str, Any]:
        if not self._sync_arm_requested:
            raise RuntimeError("Modulo non armato.")
        self._set_table_lock(True)
        start_save_on_sync = bool(payload.get("start_save_on_sync", False))
        sync_anchor_epoch_ns = int(payload.get("sync_anchor_epoch_ns", 0) or 0)
        if sync_anchor_epoch_ns > 0:
            try:
                self.acq.set_sync_anchor_epoch_s(float(sync_anchor_epoch_ns) / 1e9)
            except Exception:
                pass
        mode = str(payload.get("mode", "software") or "software").strip().lower()
        sync_role = str(payload.get("sync_role", "") or "").strip().lower()
        trig_src = str(payload.get("start_trigger_source", "") or "").strip()
        sample_clk_mode = str(payload.get("sample_clock_mode", "") or "").strip().lower()
        sample_clk_src = str(payload.get("sample_clock_source", "") or "").strip()
        sample_clk_edge = str(payload.get("sample_clock_edge", "rising") or "rising").strip().lower()
        master_timebase_src = str(payload.get("master_timebase_source", "") or "").strip()
        try:
            master_timebase_rate = float(payload.get("master_timebase_rate_hz", 0.0) or 0.0)
        except Exception:
            master_timebase_rate = 0.0
        sync_pulse_src = str(payload.get("sync_pulse_source", "") or "").strip()
        try:
            sample_clk_rate = float(payload.get("sample_clock_rate_hz", 0.0) or 0.0)
        except Exception:
            sample_clk_rate = 0.0
        if mode == "hardware":
            self._pending_sync_start_cfg = {
                "sync_mode": "hardware",
                "sync_role": sync_role,
                "start_trigger_source": trig_src,
                "sample_clock_mode": sample_clk_mode,
                "sample_clock_source": sample_clk_src,
                "sample_clock_edge": sample_clk_edge,
                "sample_clock_rate_hz": sample_clk_rate,
                "master_timebase_source": master_timebase_src,
                "master_timebase_rate_hz": master_timebase_rate,
                "sync_pulse_source": sync_pulse_src,
            }
        else:
            self._pending_sync_start_cfg = None
        start_epoch_ns = int(payload.get("start_epoch_ns", 0) or 0)
        if start_epoch_ns > 0 and (mode != "hardware" or sync_role == "master"):
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
        try:
            self._run_without_message_boxes(self._update_acquisition_from_table)
        finally:
            self._pending_sync_start_cfg = None
        if not bool(getattr(self.acq, "_running", False)):
            raise RuntimeError("Start sincronizzato fallito.")
        if start_save_on_sync:
            self._sync_remote_active = True
            self._set_remote_control_lock(True)
            # Hold writer until root computes common N0 and commits cutoff.
            try:
                self.acq.set_sync_write_start_index(10**12)
            except Exception:
                pass
            self._run_without_message_boxes(self._on_start_saving)
            if not bool(self.acq.recording_enabled):
                self._sync_remote_active = False
                self._set_remote_control_lock(False)
                raise RuntimeError("Salvataggio sync non avviato.")
        self._sync_arm_requested = False
        snap = self._sync_status_snapshot()
        snap["running"] = True
        snap["start_ns"] = time.time_ns()
        if start_save_on_sync:
            snap["recording"] = bool(self.acq.recording_enabled)
        self._sync_emit_status_update()
        return snap

    def _sync_cmd_set_sync_write_cutoff(self, payload: Dict[str, Any]) -> Dict[str, Any]:
        try:
            cutoff = int(payload.get("cutoff_index", 0) or 0)
        except Exception:
            cutoff = 0
        try:
            self.acq.set_sync_write_start_index(cutoff)
        except Exception:
            pass
        snap = self._sync_status_snapshot()
        snap["sync_cutoff_index"] = int(cutoff)
        self._sync_emit_status_update()
        return snap

    def _sync_cmd_start_save(self, _payload: Dict[str, Any]) -> Dict[str, Any]:
        start_epoch_ns = int(_payload.get("start_epoch_ns", 0) or 0)
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
        self._sync_remote_active = True
        self._set_remote_control_lock(True)
        self._run_without_message_boxes(self._on_start_saving)
        if not bool(self.acq.recording_enabled):
            self._sync_remote_active = False
            self._set_remote_control_lock(False)
            raise RuntimeError("Salvataggio non avviato.")
        snap = self._sync_status_snapshot()
        snap["recording"] = True
        if start_epoch_ns > 0:
            snap["requested_start_ns"] = int(start_epoch_ns)
        snap["recording_start_ns"] = int(time.time_ns())
        self._sync_emit_status_update()
        return snap

    def _sync_set_merge_state(self, **kwargs) -> None:
        now_ns = int(time.time_ns())
        with self._merge_state_lock:
            state = dict(self._merge_state)
            state.update(kwargs)
            state["updated_ns"] = now_ns
            self._merge_state = state

    def _sync_get_merge_state(self) -> Dict[str, Any]:
        with self._merge_state_lock:
            return dict(self._merge_state)

    def _sync_stop_save_only(self) -> None:
        try:
            self.acq.stop_graceful()
        except Exception:
            pass
        try:
            self.acq.stop()
        except Exception:
            pass
        try:
            self.acq.set_recording(False)
        except Exception:
            pass

        try:
            if hasattr(self, "_auto_fft_change") and hasattr(self, "chkFftEnable"):
                self._auto_fft_change = True
                self.chkFftEnable.setChecked(False)
        except Exception:
            pass
        finally:
            if hasattr(self, "_auto_fft_change"):
                self._auto_fft_change = False
        try:
            if hasattr(self, "_fft_enabled"):
                self._fft_enabled = False
            if hasattr(self, "_clear_fft_plot_visuals"):
                self._clear_fft_plot_visuals(clear_cached=False)
        except Exception:
            pass
        try:
            if hasattr(self, "sigFftWorkerReset"):
                self.sigFftWorkerReset.emit(True, True)
        except Exception:
            pass

        try:
            if self._count_timer.isActive():
                self._count_timer.stop()
        except Exception:
            pass
        try:
            self.btnStart.setText("Salva dati")
            self.btnStart.setEnabled(True)
            self.btnStop.setEnabled(False)
        except Exception:
            pass
        try:
            self.guiTimer.stop()
        except Exception:
            pass

    def _sync_build_final_tdms_path(self) -> str:
        final_path = os.path.join(self._save_dir, self._base_filename)
        try:
            if os.path.exists(final_path):
                base_name, ext = os.path.splitext(self._base_filename)
                dt_str = datetime.datetime.now().strftime("%d_%m_%y_%H_%M_%S")
                new_name = f"{base_name}_{dt_str}{ext or '.tdms'}"
                final_path = os.path.join(self._save_dir, new_name)
        except Exception:
            pass
        return final_path

    def _sync_collect_optional_fft_data(self) -> Optional[Dict[str, Any]]:
        try:
            freq = getattr(self, "_last_fft_freq", None)
            mags = getattr(self, "_last_fft_mag_by_phys", None)
            fresh_fft = (
                int(getattr(self, "_fft_result_counter", 0))
                > int(getattr(self, "_fft_result_counter_at_record_start", 0))
            )
            if not fresh_fft or not isinstance(freq, np.ndarray) or freq.size <= 0:
                return None
            if not isinstance(mags, dict) or not mags:
                return None
            ch_map: Dict[str, np.ndarray] = {}
            units_map: Dict[str, str] = {}
            for phys, arr in mags.items():
                try:
                    if not (isinstance(arr, np.ndarray) and arr.size == freq.size):
                        continue
                except Exception:
                    continue
                label = self._start_label_by_phys.get(phys, self._label_by_phys.get(phys, phys))
                fft_label = f"FFT_{label}"
                ch_map[fft_label] = arr.astype(np.float64)
                unit = self._calib_by_phys.get(phys, {}).get("unit", "")
                units_map[fft_label] = str(unit or "")
            if not ch_map:
                return None
            return {
                "freq": freq.astype(np.float64),
                "channels": ch_map,
                "units": units_map,
                "duration": float(getattr(self, "_fft_duration_seconds", 0.0) or 0.0),
            }
        except Exception:
            return None

    def _sync_merge_worker(self, tmp_subdir: str, final_path: str, fft_data: Optional[Dict[str, Any]]) -> None:
        try:
            from tdms_merge import TdmsMerger

            merger = TdmsMerger()
            try:
                anchor = getattr(self.acq, "_sync_anchor_epoch_s", None)
                cutoff = int(getattr(self.acq, "_sync_write_start_index", 0) or 0)
                fs = float(getattr(self.acq, "current_rate_hz", 0.0) or 0.0)
                if anchor is not None:
                    forced = float(anchor)
                    if cutoff > 0 and fs > 0:
                        forced += float(cutoff) / float(fs)
                    merger.forced_wf_start_time = datetime.datetime.fromtimestamp(forced)
            except Exception:
                pass

            if fft_data and hasattr(merger, "fft_data"):
                try:
                    merger.fft_data = fft_data
                except Exception:
                    pass

            self._sync_set_merge_state(
                state="running",
                progress=0.0,
                message="Finalizzazione in corso...",
                final_tdms="",
                error="",
            )

            def _merge_progress(curr: int, total: int) -> None:
                total_i = max(1, int(total))
                curr_i = max(0, min(int(curr), total_i))
                self._sync_set_merge_state(
                    state="running",
                    progress=float(curr_i) / float(total_i),
                    message=f"Finalizzazione in corso... ({curr_i}/{total_i})",
                )

            merger.merge_temp_tdms(tmp_subdir, final_path, progress_cb=_merge_progress)
            try:
                if tmp_subdir and os.path.isdir(tmp_subdir):
                    shutil.rmtree(tmp_subdir, ignore_errors=True)
            except Exception:
                pass

            self._sync_set_merge_state(
                state="done",
                progress=1.0,
                message="Finalizzazione completata.",
                final_tdms=final_path,
                error="",
            )
        except Exception as exc:
            self._sync_set_merge_state(
                state="failed",
                progress=0.0,
                message="Finalizzazione fallita.",
                final_tdms="",
                error=f"{exc.__class__.__name__}: {exc}",
            )

    def _sync_cmd_stop_safe(self, _payload: Dict[str, Any]) -> Dict[str, Any]:
        before = self._find_latest_tdms()
        self._sync_stop_save_only()
        self._sync_remote_active = False
        self._sync_arm_requested = False
        tmp_subdir = str(self._active_subdir or "").strip()
        merge_pending = bool(str(self._active_subdir or "").strip())
        if merge_pending:
            self._sync_set_merge_state(
                state="pending",
                progress=0.0,
                message="In attesa finalizzazione...",
                final_tdms="",
                error="",
                post_applied=False,
                started_ns=int(time.time_ns()),
            )
        else:
            self._sync_set_merge_state(
                state="done",
                progress=1.0,
                message="Nessuna finalizzazione necessaria.",
                final_tdms=str(before or ""),
                error="",
                post_applied=False,
                started_ns=int(time.time_ns()),
            )
        snap = self._sync_status_snapshot()
        snap["recording"] = bool(self.acq.recording_enabled)
        snap["merge_pending"] = bool(merge_pending)
        snap["final_tdms"] = str(before or "")
        snap["spool_dir"] = tmp_subdir
        snap["save_dir"] = str(self._save_dir or "")
        snap["base_filename"] = str(self._base_filename or "")
        snap["group_name"] = str(getattr(self.acq, "_tdms_group_name", lambda: "Acquisition")() or "Acquisition")
        snap["board_number"] = "9201"
        state = self._sync_get_merge_state()
        snap["merge_state"] = str(state.get("state", "idle") or "idle")
        snap["merge_progress"] = float(state.get("progress", 0.0) or 0.0)
        snap["merge_message"] = str(state.get("message", "") or "")
        self._sync_emit_status_update()
        return snap

    def _sync_cmd_start_merge_async(self, _payload: Dict[str, Any]) -> Dict[str, Any]:
        worker = getattr(self, "_merge_worker_thread", None)
        if worker is not None and worker.is_alive():
            state = self._sync_get_merge_state()
            snap = self._sync_status_snapshot()
            snap["merge_state"] = str(state.get("state", "running") or "running")
            snap["merge_progress"] = float(state.get("progress", 0.0) or 0.0)
            snap["merge_message"] = str(state.get("message", "") or "")
            snap["merge_started"] = True
            self._sync_emit_status_update()
            return snap

        tmp_subdir = str(self._active_subdir or "").strip()
        if not tmp_subdir or not os.path.isdir(tmp_subdir):
            latest = self._find_latest_tdms()
            self._sync_set_merge_state(
                state="done",
                progress=1.0,
                message="Nessuna finalizzazione necessaria.",
                final_tdms=str(latest or ""),
                error="",
                post_applied=False,
            )
            snap = self._sync_status_snapshot()
            snap["merge_state"] = "done"
            snap["merge_progress"] = 1.0
            snap["merge_message"] = "Nessuna finalizzazione necessaria."
            snap["final_tdms"] = str(latest or "")
            snap["merge_started"] = False
            self._sync_emit_status_update()
            return snap

        final_path = self._sync_build_final_tdms_path()
        fft_data = self._sync_collect_optional_fft_data()
        self._sync_set_merge_state(
            state="running",
            progress=0.0,
            message="Finalizzazione in corso...",
            final_tdms="",
            error="",
            post_applied=False,
            started_ns=int(time.time_ns()),
        )
        th = threading.Thread(
            target=self._sync_merge_worker,
            args=(tmp_subdir, final_path, fft_data),
            name=f"merge-{self.__class__.__name__}",
            daemon=True,
        )
        self._merge_worker_thread = th
        th.start()

        snap = self._sync_status_snapshot()
        snap["merge_state"] = "running"
        snap["merge_progress"] = 0.0
        snap["merge_message"] = "Finalizzazione in corso..."
        snap["merge_started"] = True
        self._sync_emit_status_update()
        return snap

    def _sync_cmd_merge_status(self, _payload: Dict[str, Any]) -> Dict[str, Any]:
        state = self._sync_get_merge_state()
        merge_state = str(state.get("state", "idle") or "idle").lower()

        if merge_state in ("done", "failed") and not bool(state.get("post_applied", False)):
            self._active_subdir = None
            try:
                self.acq.set_sync_write_start_index(0)
                self.acq.set_sync_anchor_epoch_s(None)
            except Exception:
                pass
            try:
                self._set_table_lock(False)
            except Exception:
                pass
            try:
                self._uncheck_all_enabled()
            except Exception:
                pass
            self._sync_set_merge_state(post_applied=True)
            state = self._sync_get_merge_state()
            merge_state = str(state.get("state", merge_state) or merge_state).lower()

        if merge_state == "failed":
            err = str(state.get("error", "Ricomposizione TDMS fallita.") or "Ricomposizione TDMS fallita.")
            raise RuntimeError(err)

        snap = self._sync_status_snapshot()
        snap["merge_state"] = merge_state
        snap["merge_progress"] = float(state.get("progress", 0.0) or 0.0)
        snap["merge_message"] = str(state.get("message", "") or "")
        snap["final_tdms"] = str(state.get("final_tdms", "") or "")
        snap["merge_done"] = bool(merge_state == "done")
        self._sync_emit_status_update()
        return snap

    def _sync_cmd_stop_and_merge(self, _payload: Dict[str, Any]) -> Dict[str, Any]:
        self._sync_cmd_stop_safe(_payload)
        self._sync_cmd_start_merge_async({})
        deadline = time.monotonic() + 7200.0
        while time.monotonic() < deadline:
            state = self._sync_get_merge_state()
            merge_state = str(state.get("state", "idle") or "idle").lower()
            if merge_state == "done":
                break
            if merge_state == "failed":
                err = str(state.get("error", "Ricomposizione TDMS fallita.") or "Ricomposizione TDMS fallita.")
                raise RuntimeError(err)
            time.sleep(0.05)

        if time.monotonic() >= deadline:
            raise RuntimeError("Timeout finalizzazione TDMS.")

        snap = self._sync_cmd_merge_status({})
        snap["recording"] = bool(self.acq.recording_enabled)
        return snap

    def _sync_cmd_unlock_ui(self, _payload: Dict[str, Any]) -> Dict[str, Any]:
        self._sync_remote_active = False
        self._sync_arm_requested = False
        self._set_remote_control_lock(False)
        snap = self._sync_status_snapshot()
        snap["unlocked"] = True
        self._sync_emit_status_update()
        return snap

    def _sync_cmd_abort_prepared(self, _payload: Dict[str, Any]) -> Dict[str, Any]:
        try:
            self.acq.set_recording(False)
        except Exception:
            pass
        try:
            self.acq.set_sync_write_start_index(0)
            self.acq.set_sync_anchor_epoch_s(None)
        except Exception:
            pass
        try:
            self.acq.stop()
        except Exception:
            pass
        self._sync_remote_active = False
        self._sync_arm_requested = False
        self._set_remote_control_lock(False)
        snap = self._sync_status_snapshot()
        snap["aborted"] = True
        self._sync_emit_status_update()
        return snap

    def _perform_remote_shutdown(self) -> None:
        if bool(getattr(self, "_shutdown_in_progress", False)):
            return
        self._shutdown_in_progress = True
        self._allow_close_after_shutdown = True
        try:
            self._close_sync_agent_for_shutdown()
        except Exception:
            pass
        try:
            app = QtWidgets.QApplication.instance()
            if app is not None:
                app.quit()
            else:
                self.close()
        except Exception:
            try:
                self.close()
            except Exception:
                pass

    def _sync_cmd_shutdown(self, _payload: Dict[str, Any]) -> Dict[str, Any]:
        try:
            QtCore.QTimer.singleShot(0, self._perform_remote_shutdown)
        except Exception:
            try:
                self._perform_remote_shutdown()
            except Exception:
                pass
        return {"shutdown": True}

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
                    f'Il dispositivo assegnato "{forced_device_name}" non ? disponibile.',
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
        self._sync_emit_status_update()

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
        self._schedule_embedded_widget_relayout()

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

            # Deduplica il nuovo nome rispetto agli altri canali.  Se esiste giaun
            # altro canale con la stessa etichetta (ignorando la differenza
            # maiuscole/minuscole), appende un suffisso _2, _3, ... fino a trovare
            # un nome non in uso.  Questa logica evita ambiguit? quando i nomi
            # duplicati vengono usati per instradare i dati dal core alla UI.
            try:
                base = new_label
                if base:
                    # Raccogli tutte le etichette degli altri canali (fisici + calcolati, case-insensitive)
                    existing = self._existing_channel_names_lower(exclude_phys_row=row)
                    # Se il nuovo nome ? giapresente, trova un suffisso libero
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
            self._sync_emit_status_update()
            return

        # PRENDE SEMPRE IL "NAME" PULITO dal userData della combo
        device = (self.cmbDevice.currentData() or self.cmbDevice.currentText()).strip()
        phys, labels = self._enabled_phys_and_labels()

        if not phys:
            self._stop_acquisition_ui_only()
            self.lblRateInfo.setText("-")
            self._sync_emit_status_update()
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

        sync_cfg = dict(self._pending_sync_start_cfg or {})
        ok = self.acq.start(
            device_name=device,
            ai_channels=phys,
            channel_names=labels,
            sync_start_cfg=sync_cfg if sync_cfg else None,
        )
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
            self._set_stop_button_enabled_for_recording()
        except Exception:
            # Fallback: disable the button if we cannot read the recording state
            self.btnStop.setEnabled(False)
        if not self.guiTimer.isActive():
            self.guiTimer.start()

        self._update_rate_label(phys)
        self._push_sensor_map_to_core()
        self._push_calculated_channels_to_core()
        self._sync_emit_status_update()

    def _update_rate_label(self, phys_list):
        try:
            labels = [self._label_by_phys.get(p, p) for p in phys_list]
            cur_per = (self.acq.current_rate_hz or 0) / 1e3
            cur_agg = (self.acq.current_agg_rate_hz or 0) / 1e3
            lim_single = (self.acq.max_single_rate_hz or 0) / 1e3
            lim_multi  = (self.acq.max_multi_rate_hz  or 0) / 1e3
            sync_txt = ""
            if self._sync_agent is not None and self._sync_agent.is_active():
                sync_txt = f"  |  Fs dataset sincronizzato {str(self.rateEdit.text() or '').strip() or 'Max'} Hz"
            self.lblRateInfo.setText(
                f"Canali: {', '.join(labels)}  |  "
                f"Rate per-canale {cur_per:.1f} kS/s  (agg: {cur_agg:.1f} kS/s)  |  "
                f"Limiti modulo -> single {lim_single:.1f} kS/s, aggregato {lim_multi:.1f} kS/s"
                f"{sync_txt}"
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
                            self._set_stop_button_enabled_for_recording()
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
                        try:
                            self._push_calculated_channels_to_core()
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
        self._push_calculated_channels_to_core()
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
        try:
            self._recording_start_sample_index = int(getattr(self.acq, "_global_samples", 0) or 0)
        except Exception:
            self._recording_start_sample_index = 0
        # enable recording so the writer will start accumulating blocks in RAM
        self.acq.set_recording(True)

        # Now that recording is active, the Stop/Recompose button can be used to
        # stop and merge the temporary TDMS files.  Enable it explicitly.
        try:
            self._set_stop_button_enabled_for_recording(True)
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
            try:
                anchor = getattr(self.acq, "_sync_anchor_epoch_s", None)
                cutoff = int(getattr(self.acq, "_sync_write_start_index", 0) or 0)
                fs = float(getattr(self.acq, "current_rate_hz", 0.0) or 0.0)
                if anchor is not None:
                    forced = float(anchor)
                    if cutoff > 0 and fs > 0:
                        forced += float(cutoff) / float(fs)
                    merger.forced_wf_start_time = datetime.datetime.fromtimestamp(forced)
            except Exception:
                pass
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
            try:
                self.acq.set_sync_write_start_index(0)
                self.acq.set_sync_anchor_epoch_s(None)
            except Exception:
                pass

        self._set_table_lock(False)
        self._uncheck_all_enabled()

    # ----------------------------- Grafici -----------------------------
    def _reset_plots(self):
        self._chart_x.clear()
        self._pending_table_updates.clear()
        self._legend_signature_cache = None
        try:
            self._preview_queue.clear()
        except Exception:
            pass
        for dq in self._chart_y_by_phys.values(): dq.clear()
        for dq in self._chart_y_by_calc.values(): dq.clear()
        self._instant_t = np.array([], dtype=float)
        self._instant_y_by_phys = {k: np.array([], dtype=float) for k in self._instant_y_by_phys}
        self._instant_y_by_calc = {k: np.array([], dtype=float) for k in self._instant_y_by_calc}

        for c in list(self._chart_curves_by_phys.values()):
            self._release_curve_to_pool('_curve_pool_chart_phys', self.pgChart, c)
        for c in list(self._chart_curves_by_calc.values()):
            self._release_curve_to_pool('_curve_pool_chart_calc', self.pgChart, c)
        for c in list(self._instant_curves_by_phys.values()):
            self._release_curve_to_pool('_curve_pool_instant_phys', self.pgInstant, c)
        for c in list(self._instant_curves_by_calc.values()):
            self._release_curve_to_pool('_curve_pool_instant_calc', self.pgInstant, c)
        self._chart_curves_by_phys.clear()
        self._instant_curves_by_phys.clear()
        self._chart_curves_by_calc.clear()
        self._instant_curves_by_calc.clear()
        self._chart_legend.clear()
        self._instant_legend.clear()
        self._legend_signature_cache = None

        # Cancella la stringa delle medie quando si resettano i grafici
        try:
            if hasattr(self, 'lblAvgChart'):
                self.lblAvgChart.setText("")
        except Exception:
            pass

    def _reset_plots_curves(self):
        self._reset_plots()
        self._ensure_phys_plot_curves(
            show_phys=bool(self.chkPhysViewEnable.isChecked()),
            instant_enabled=bool(getattr(self, '_instant_plot_enabled', True)),
        )
        self._sync_calc_plot_curves()

    def _rebuild_legends(self, force: bool = False):
        signature = self._build_legend_signature()
        if (not force) and signature == getattr(self, "_legend_signature_cache", None):
            return
        self._legend_signature_cache = signature
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
        for cc, curve in self._chart_curves_by_calc.items():
            r = self._find_calc_row_by_cc(cc)
            label = cc
            if r >= 0:
                it = self.calcTable.item(r, CCOL_LABEL)
                label = str((it.text() if it else cc) or cc).strip() or cc
            try:
                curve.setName(label)
            except Exception:
                pass
            self._chart_legend.addItem(curve, label)
        for cc, curve in self._instant_curves_by_calc.items():
            r = self._find_calc_row_by_cc(cc)
            label = cc
            if r >= 0:
                it = self.calcTable.item(r, CCOL_LABEL)
                label = str((it.text() if it else cc) or cc).strip() or cc
            try:
                curve.setName(label)
            except Exception:
                pass
            self._instant_legend.addItem(curve, label)

    def _clear_chart(self):
        self._chart_x.clear()
        self._pending_table_updates.clear()
        self._legend_signature_cache = None
        self._chart_last_preview_t = np.nan
        self._chart_last_series_by_key = {}
        self._chart_locked_ylim = None
        try:
            self._preview_queue.clear()
        except Exception:
            pass
        for phys, curve in self._chart_curves_by_phys.items():
            self._chart_y_by_phys[phys].clear()
            curve.clear()
        for cc, curve in self._chart_curves_by_calc.items():
            dq = self._chart_y_by_calc.get(cc)
            if dq is not None:
                dq.clear()
            curve.clear()
        try:
            self._chart_cursor_a.hide(); self._chart_cursor_b.hide()
        except Exception:
            pass
        try:
            self.lblChartCursorInfo.setText("")
        except Exception:
            pass

    def _slot_instant_block(self, t: np.ndarray, ys: list, names: list):
        try:
            self._instant_t = np.asarray(t, dtype=float)
            _bg_compact = bool(
                getattr(self, '_compact_instant_when_background', True)
                and self._window_is_background()
                and (not bool(getattr(self, '_instant_plot_enabled', True)))
            )
            if _bg_compact and self._instant_t.size > 1:
                self._instant_t = self._instant_t[-1:]
            # mappa nome di start -> phys
            start_to_phys = {name: phys for phys, name in self._start_label_by_phys.items()}
            phys_map: Dict[str, np.ndarray] = {}
            for name, y in zip(names, ys):
                phys = start_to_phys.get(name)
                if not phys: continue
                cal = self._calib_by_phys.get(phys, {"a":1.0,"b":0.0})
                a = float(cal.get("a",1.0)); b = float(cal.get("b",0.0))
                y_src = np.asarray(y, dtype=float)
                if _bg_compact and y_src.size > 1:
                    y_src = y_src[-1:]
                y_eng = a * y_src + b
                self._instant_y_by_phys[phys] = y_eng
                phys_map[phys] = y_eng
            calc_data = self._evaluate_calculated_block(phys_map)
            for cc, arr in calc_data.items():
                self._instant_y_by_calc[cc] = arr
            self._update_calc_table_values(calc_data)
            self._sync_calc_plot_curves()
        except RuntimeError:
            pass

    def _slot_chart_points(self, t_pts: np.ndarray, ys_pts: list, names: list):
        try:
            show_phys = bool(self.chkPhysViewEnable.isChecked())
            show_calc = bool(self.chkCalcViewEnable.isChecked())
            if not (show_phys or show_calc):
                return
            if not self._is_plots_tab_active():
                return
            if bool(getattr(self, '_suspend_preview_when_background', True)) and self._window_is_background():
                try:
                    self._preview_queue.clear()
                except Exception:
                    pass
                return

            t_pts = np.asarray(t_pts, dtype=np.float64).reshape(-1)
            if t_pts.size <= 0:
                return

            start_to_phys = {name: phys for phys, name in self._start_label_by_phys.items()}
            phys_full = {}
            ref_blocks = []

            for name, ypts in zip(names, ys_pts):
                phys = start_to_phys.get(name)
                if not phys:
                    continue
                y_raw = np.asarray(ypts, dtype=np.float32).reshape(-1)
                if y_raw.size != t_pts.size:
                    continue
                if hasattr(self, "_calib_by_phys"):
                    cal = self._calib_by_phys.get(phys, {"a": 1.0, "b": 0.0})
                    a = np.float32(float(cal.get("a", 1.0)))
                    b = np.float32(float(cal.get("b", 0.0)))
                    y_eng = a * y_raw + b
                else:
                    y_eng = y_raw
                if show_phys:
                    phys_full[phys] = y_eng
                ref_blocks.append(y_eng)

            if not ref_blocks:
                ref_blocks = [np.asarray(ys_pts[0], dtype=np.float32).reshape(-1)] if ys_pts else []

            idx = self._build_preview_indices(t_pts, ref_blocks)
            if idx.size <= 0:
                return

            t_prev = np.asarray(t_pts[idx], dtype=np.float64)
            payload_phys = {}
            if show_phys:
                for phys, arr in phys_full.items():
                    if arr.size == t_pts.size:
                        payload_phys[phys] = np.asarray(arr[idx], dtype=np.float32)

            payload_calc = {}
            if show_calc:
                try:
                    dec_step = int(getattr(self.acq, "chart_decimation", 1) or 1)
                except Exception:
                    dec_step = 1
                if dec_step <= 0:
                    dec_step = 1
                expected = int(t_pts.size)
                for cc, arr in dict(self._instant_y_by_calc or {}).items():
                    a = np.asarray(arr, dtype=np.float32).reshape(-1)
                    y_dec = a[::dec_step] if dec_step > 1 else a
                    if expected > 0:
                        if y_dec.size > expected:
                            y_dec = y_dec[:expected]
                        elif y_dec.size < expected and y_dec.size > 0:
                            y_dec = np.pad(y_dec, (0, expected - y_dec.size), mode="edge")
                    if y_dec.size == expected and expected > 0:
                        payload_calc[cc] = np.asarray(y_dec[idx], dtype=np.float32)

            if not payload_phys and not payload_calc:
                return

            max_blocks = int(getattr(self, "_preview_queue_max_blocks", 24) or 24)
            if max_blocks < 4:
                max_blocks = 4
            if not hasattr(self, "_preview_queue"):
                self._preview_queue = deque(maxlen=max_blocks)
            if int(getattr(self._preview_queue, "maxlen", 0) or 0) != max_blocks:
                self._preview_queue = deque(self._preview_queue, maxlen=max_blocks)

            if len(self._preview_queue) >= max_blocks:
                self._preview_queue_dropped = int(getattr(self, "_preview_queue_dropped", 0) or 0) + 1

            self._preview_queue.append({"t": t_prev, "phys": payload_phys, "calc": payload_calc})
        except RuntimeError:
            pass

    def _refresh_plots(self):
        frame_t0 = time.perf_counter()

        if bool(getattr(self, "_calc_curve_layout_dirty", True)):
            self._sync_calc_plot_curves()

        show_phys = bool(self.chkPhysViewEnable.isChecked())
        show_calc = bool(self.chkCalcViewEnable.isChecked())
        chart_visible = bool(self.pgChart.isVisible())

        if not self._is_plots_tab_active():
            self._update_render_guardrail((time.perf_counter() - frame_t0) * 1000.0)
            return

        if bool(getattr(self, '_suspend_preview_when_background', True)) and self._window_is_background():
            try:
                self._preview_queue.clear()
            except Exception:
                pass
            self._update_render_guardrail((time.perf_counter() - frame_t0) * 1000.0)
            return

        self._update_ui_render_profile()
        self._recompute_history_capacity()
        self._ensure_phys_plot_curves(
            show_phys=show_phys,
            instant_enabled=bool(getattr(self, '_instant_plot_enabled', True)),
        )
        self._drain_preview_queue(show_phys=show_phys, show_calc=show_calc)
        self._refresh_chart_focus_combo()

        self._chart_last_series_by_key = {}
        n = len(self._chart_x)
        mode = self._chart_mode()
        focus_key = self._chart_focus()
        relative_time = self._chart_relative_enabled()
        robust_y = self._chart_robust_enabled()
        lock_y = self._chart_lock_y_enabled()
        window_s = self._chart_window_seconds()

        if chart_visible and n > 1 and (show_phys or show_calc):
            x = self._buffer_to_numpy(self._chart_x, dtype=np.float64)
            if x.size > 1:
                valid_x = np.isfinite(x)
                if int(np.count_nonzero(valid_x)) > 1:
                    x_view = np.array(x, dtype=np.float64, copy=True)
                    if relative_time:
                        try:
                            x0 = float(x_view[valid_x][0])
                            x_view[valid_x] = x_view[valid_x] - np.float64(x0)
                        except Exception:
                            pass
                    x_f = x_view[valid_x]
                    x_min = float(np.min(x_f)); x_max = float(np.max(x_f))
                    if window_s > 0.0 and np.isfinite(x_max):
                        x_min = max(x_min, x_max - float(window_s))

                    target = int(getattr(self, "_plot_render_max_points", 2500) or 2500)
                    if target < 300:
                        target = 300
                    step = max(1, int(np.ceil(float(x_view.size) / float(target))))
                    x_plot = self._sample_for_plot(x_view, step)
                    x_mask = np.isfinite(x_plot)
                    if window_s > 0.0:
                        x_mask = x_mask & (x_plot >= np.float64(x_min))
                    if int(np.count_nonzero(x_mask)) <= 1:
                        x_mask = np.isfinite(x_plot)

                    jobs = []
                    if show_phys:
                        for phys, curve in self._chart_curves_by_phys.items():
                            jobs.append(("phys", phys, curve))
                    if show_calc:
                        for cc, curve in self._chart_curves_by_calc.items():
                            jobs.append(("calc", cc, curve))

                    if focus_key:
                        for kind, key, curve in jobs:
                            if self._chart_series_key(kind, key) != focus_key:
                                try: curve.setData([], [])
                                except Exception: pass
                        jobs = [job for job in jobs if self._chart_series_key(job[0], job[1]) == focus_key]

                    key_order = [self._chart_series_key(kind, key) for kind, key, _ in jobs]
                    index_map = {k: i for i, k in enumerate(key_order)}

                    spans = []
                    for kind, key, _curve in jobs[:32]:
                        y = self._buffer_to_numpy(self._chart_y_by_phys.get(key)) if kind == "phys" else self._buffer_to_numpy(self._chart_y_by_calc.get(key))
                        if y.size != x_view.size or y.size <= 1:
                            continue
                        ys = self._sample_for_plot(y, step)
                        ys = ys[np.isfinite(ys)]
                        if ys.size > 8:
                            try:
                                lo = float(np.percentile(ys, 1.0)); hi = float(np.percentile(ys, 99.0)); span = hi - lo
                                if np.isfinite(span) and span > 0.0: spans.append(span)
                            except Exception:
                                pass
                    global_span = float(np.median(np.asarray(spans, dtype=np.float64))) if spans else 1.0
                    if (not np.isfinite(global_span)) or global_span <= 1e-12:
                        global_span = 1.0

                    budget = int(getattr(self, "_render_budget_curves", 8) or 8)
                    if budget < 1: budget = 1
                    selected = self._rr_select(jobs, "_rr_cursor_chart", budget)

                    y_chunks = []
                    for kind, key, curve in selected:
                        y = self._buffer_to_numpy(self._chart_y_by_phys.get(key)) if kind == "phys" else self._buffer_to_numpy(self._chart_y_by_calc.get(key))
                        if y.size != x_view.size or y.size <= 1:
                            continue
                        y_plot = self._sample_for_plot(y, step)
                        if y_plot.size != x_plot.size:
                            continue
                        skey = self._chart_series_key(kind, key)
                        idx = int(index_map.get(skey, 0))
                        if mode == "offset":
                            y_draw = y_plot + np.float32(idx * global_span * 0.8)
                        elif mode == "stacked":
                            y_draw = y_plot + np.float32(idx * global_span * 1.8)
                        else:
                            y_draw = y_plot
                        xd = x_plot[x_mask] if int(np.count_nonzero(x_mask)) > 1 else x_plot
                        yd = y_draw[x_mask] if int(np.count_nonzero(x_mask)) > 1 else y_draw
                        if xd.size <= 1 or yd.size <= 1:
                            continue
                        try:
                            curve.setData(xd, yd)
                            self._chart_last_series_by_key[skey] = (np.asarray(xd, dtype=np.float64), np.asarray(yd, dtype=np.float32), str(key))
                        except Exception:
                            continue
                        yv = yd[np.isfinite(yd)]
                        if yv.size > 0:
                            y_chunks.append(yv)

                    if np.isfinite(x_min) and np.isfinite(x_max):
                        if x_max <= x_min: x_max = x_min + 1.0
                        try: self.pgChart.setXRange(float(x_min), float(x_max), padding=0.01)
                        except Exception: pass

                    if lock_y and isinstance(getattr(self, "_chart_locked_ylim", None), tuple):
                        try:
                            yl = self._chart_locked_ylim
                            self.pgChart.setYRange(float(yl[0]), float(yl[1]), padding=0.0)
                        except Exception:
                            pass
                    elif y_chunks:
                        try:
                            y_all = np.concatenate(y_chunks)
                            if y_all.size > 8 and robust_y:
                                y_lo = float(np.percentile(y_all, 1.0)); y_hi = float(np.percentile(y_all, 99.0))
                            else:
                                y_lo = float(np.min(y_all)); y_hi = float(np.max(y_all))
                            if np.isfinite(y_lo) and np.isfinite(y_hi):
                                if y_hi <= y_lo:
                                    d = 1.0 if abs(y_lo) < 1e-9 else abs(y_lo) * 0.1
                                    y_lo -= d; y_hi += d
                                pad = max(1e-9, (y_hi - y_lo) * 0.08)
                                yl = (float(y_lo - pad), float(y_hi + pad))
                                self._chart_locked_ylim = yl
                                self.pgChart.setYRange(yl[0], yl[1], padding=0.0)
                        except Exception:
                            pass

        instant_enabled = bool(getattr(self, "_instant_plot_enabled", True))
        if instant_enabled and isinstance(self._instant_t, np.ndarray) and self._instant_t.size > 1:
            jobs_inst = []
            if show_phys:
                for phys, curve in self._instant_curves_by_phys.items():
                    jobs_inst.append(("phys", phys, curve))
            if show_calc:
                for cc, curve in self._instant_curves_by_calc.items():
                    jobs_inst.append(("calc", cc, curve))
            if focus_key:
                jobs_inst = [job for job in jobs_inst if self._chart_series_key(job[0], job[1]) == focus_key]
            ibudget = int(getattr(self, "_render_budget_curves_instant", 8) or 8)
            if ibudget < 1: ibudget = 1
            for kind, key, curve in self._rr_select(jobs_inst, "_rr_cursor_instant", ibudget):
                y = self._instant_y_by_phys.get(key) if kind == "phys" else self._instant_y_by_calc.get(key)
                if isinstance(y, np.ndarray) and y.size == self._instant_t.size and y.size > 1:
                    try: curve.setData(self._instant_t, y)
                    except Exception: pass

        self._update_chart_cursor_info()
        self._update_render_guardrail((time.perf_counter() - frame_t0) * 1000.0)
        try:
            if hasattr(self, 'lblAvgChart'):
                avg_strings = []
                for phys in self._current_phys_order:
                    y = self._instant_y_by_phys.get(phys)
                    if isinstance(y, np.ndarray) and y.size > 0:
                        try:
                            avg_val = float(np.mean(y)); label = self._start_label_by_phys.get(phys, self._label_by_phys.get(phys, phys)); unit = self._calib_by_phys.get(phys, {}).get('unit', '')
                            avg_strings.append(f"{label}: {avg_val:.6g}" + (f" {unit}" if unit else ""))
                        except Exception:
                            pass
                for r in range(self.calcTable.rowCount()):
                    try:
                        it_en = self.calcTable.item(r, CCOL_ENABLE)
                        if it_en is None or it_en.checkState() != QtCore.Qt.Checked: continue
                        cc = self._calc_channel_id_for_row(r); formula = str(self._calc_formula_by_cc.get(cc, "") or "").strip()
                        if (not formula) or (cc in self._calc_compile_errors): continue
                        y = self._instant_y_by_calc.get(cc)
                        if not isinstance(y, np.ndarray) or y.size <= 0: continue
                        avg_val = float(np.mean(y)); it_label = self.calcTable.item(r, CCOL_LABEL); label = str((it_label.text() if it_label else cc) or cc).strip() or cc
                        avg_strings.append(f"{label}: {avg_val:.6g}")
                    except Exception:
                        continue
                self.lblAvgChart.setText(" | ".join(avg_strings))
        except Exception:
            pass

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
        while (f"{candidate}.general" in cfg) or (f"{candidate}.channels" in cfg) or (f"{candidate}.calculated_channels" in cfg):
            candidate = f"{base}_{idx}"
            idx += 1
        return candidate

    def _run_workspace_via_existing_ui(self, mode: str, path: str) -> Dict[str, Any]:
        target_path = str(path or "").strip()
        if not target_path:
            raise RuntimeError("Percorso workspace non valido.")
        captured = {"error": "", "warning": "", "info": []}
        QFileDialog = QtWidgets.QFileDialog
        QMessageBox = QtWidgets.QMessageBox
        old_exec = getattr(QFileDialog, "exec_", None)
        old_selected = getattr(QFileDialog, "selectedFiles", None)
        old_open = getattr(QFileDialog, "getOpenFileName", None)
        old_info = getattr(QMessageBox, "information", None)
        old_warn = getattr(QMessageBox, "warning", None)
        old_crit = getattr(QMessageBox, "critical", None)
        old_question = getattr(QMessageBox, "question", None)
        had_notice = hasattr(self, "_show_themed_notice")
        had_confirm = hasattr(self, "_ask_themed_confirmation")
        old_notice = getattr(self, "_show_themed_notice", None)
        old_confirm = getattr(self, "_ask_themed_confirmation", None)
        def _capture_message(args):
            parts = []
            for a in args[2:]:
                try:
                    txt = str(a or "").strip()
                except Exception:
                    txt = ""
                if txt:
                    parts.append(txt)
            return "\n".join(parts).strip()
        def _fake_info(*args, **kwargs):
            msg = _capture_message(args)
            if msg:
                captured["info"].append(msg)
            return QMessageBox.Ok
        def _fake_warn(*args, **kwargs):
            captured["warning"] = _capture_message(args)
            return QMessageBox.Ok
        def _fake_crit(*args, **kwargs):
            captured["error"] = _capture_message(args)
            return QMessageBox.Ok
        def _fake_question(*args, **kwargs):
            return QMessageBox.Yes
        def _fake_exec(dlg):
            return QtWidgets.QDialog.Accepted
        def _fake_selected(_dlg):
            return [target_path]
        def _fake_open(*args, **kwargs):
            return (target_path, "INI (*.ini)")
        def _fake_notice(title, text, details="", kind="info"):
            msg = "\n".join([str(text or "").strip(), str(details or "").strip()]).strip()
            k = str(kind or "info").strip().lower()
            if k == "error":
                captured["error"] = msg
            elif k == "warning":
                captured["warning"] = msg
            elif msg:
                captured["info"].append(msg)
        try:
            if old_exec is not None:
                QFileDialog.exec_ = _fake_exec
            if old_selected is not None:
                QFileDialog.selectedFiles = _fake_selected
            if old_open is not None:
                QFileDialog.getOpenFileName = staticmethod(_fake_open)
            if old_info is not None:
                QMessageBox.information = staticmethod(_fake_info)
            if old_warn is not None:
                QMessageBox.warning = staticmethod(_fake_warn)
            if old_crit is not None:
                QMessageBox.critical = staticmethod(_fake_crit)
            if old_question is not None:
                QMessageBox.question = staticmethod(_fake_question)
            if had_notice:
                self._show_themed_notice = _fake_notice
            if had_confirm:
                self._ask_themed_confirmation = lambda *a, **k: True
            if str(mode or "").strip().lower() == "save":
                self._save_workspace()
            else:
                self._load_workspace()
        finally:
            if old_exec is not None:
                QFileDialog.exec_ = old_exec
            if old_selected is not None:
                QFileDialog.selectedFiles = old_selected
            if old_open is not None:
                QFileDialog.getOpenFileName = old_open
            if old_info is not None:
                QMessageBox.information = old_info
            if old_warn is not None:
                QMessageBox.warning = old_warn
            if old_crit is not None:
                QMessageBox.critical = old_crit
            if old_question is not None:
                QMessageBox.question = old_question
            if had_notice:
                self._show_themed_notice = old_notice
            if had_confirm:
                self._ask_themed_confirmation = old_confirm
        if captured["error"]:
            raise RuntimeError(captured["error"])
        if captured["warning"]:
            raise RuntimeError(captured["warning"])
        return {
            "path": target_path,
            "supporteddaq": self._workspace_supported_daq(),
            "device_name": self._workspace_current_device_name(),
            "messages": list(captured.get("info") or []),
        }

    def _sync_cmd_save_workspace_to_path(self, payload: dict) -> dict:
        target_path = str(dict(payload or {}).get("path", "") or "").strip()
        result = self._run_workspace_via_existing_ui("save", target_path)
        return {"ok": True, "payload": result}

    def _sync_cmd_load_workspace_from_path(self, payload: dict) -> dict:
        target_path = str(dict(payload or {}).get("path", "") or "").strip()
        result = self._run_workspace_via_existing_ui("load", target_path)
        return {"ok": True, "payload": result}

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
                cfg.read(path, encoding="utf-8-sig")
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
                "Scheda gi? presente, vuoi sovrascriverla?",
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
        sec_calc = f"{entry_base}.calculated_channels"
        cfg[sec_general] = {}
        cfg[sec_channels] = {}
        cfg[sec_calc] = {}

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
        gen["show_phys_plot"] = "1" if bool(self.chkPhysViewEnable.isChecked()) else "0"
        gen["show_calc_plot"] = "1" if bool(self.chkCalcViewEnable.isChecked()) else "0"
        gen["chart_preset"] = str(self.cmbChartPreset.currentText() or "Operativo")
        gen["chart_mode"] = str(self.cmbChartMode.currentText() or "Overlay")
        gen["chart_window_s"] = str(float(self.spinChartWindowSec.value()))
        gen["chart_robust_y"] = "1" if bool(self.chkChartRobustY.isChecked()) else "0"
        gen["chart_lock_y"] = "1" if bool(self.chkChartLockY.isChecked()) else "0"
        gen["chart_cursors"] = "1" if bool(self.chkChartCursors.isChecked()) else "0"

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

        calcsec = cfg[sec_calc]
        calcsec["rows_json"] = json.dumps(self._calc_rows_payload())

        try:
            with open(path, "w", encoding="utf-8-sig") as f:
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
            cfg.read(fname, encoding="utf-8-sig")
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
        sec_calc = f"{entry_base}.calculated_channels"
        if sec_general not in cfg or sec_channels not in cfg:
            QtWidgets.QMessageBox.warning(self, "Attenzione", "Nessun workspace per la scheda corrente")
            return

        gen = cfg[sec_general]
        chsec = cfg[sec_channels]
        calcsec = cfg[sec_calc] if sec_calc in cfg else None

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
        try:
            self.chkPhysViewEnable.setChecked(str(gen.get("show_phys_plot", "0")).strip().lower() in ("1", "true", "yes", "on"))
        except Exception:
            pass
        try:
            self.chkCalcViewEnable.setChecked(str(gen.get("show_calc_plot", "0")).strip().lower() in ("1", "true", "yes", "on"))
        except Exception:
            pass
        try:
            self.cmbChartPreset.setCurrentText(str(gen.get("chart_preset", "Operativo") or "Operativo"))
            self.cmbChartMode.setCurrentText(str(gen.get("chart_mode", "Overlay") or "Overlay"))
            self.chkChartRelativeTime.setChecked(True)
            self.spinChartWindowSec.setValue(float(str(gen.get("chart_window_s", "60")).strip() or "0"))
            self.chkChartRobustY.setChecked(str(gen.get("chart_robust_y", "1")).strip().lower() in ("1", "true", "yes", "on"))
            self.chkChartLockY.setChecked(str(gen.get("chart_lock_y", "0")).strip().lower() in ("1", "true", "yes", "on"))
            self.chkChartCursors.setChecked(str(gen.get("chart_cursors", "0")).strip().lower() in ("1", "true", "yes", "on"))
        except Exception:
            pass
        self._sync_emit_status_update()

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
        # calculated channels (retrocompatibile: sezione opzionale)
        try:
            if calcsec is not None:
                rows_json = str(calcsec.get("rows_json", "") or "").strip()
                rows = json.loads(rows_json) if rows_json else []
                if isinstance(rows, list):
                    self._building_calc_table = True
                    try:
                        self.calcTable.setRowCount(0)
                        self._calc_formula_by_cc.clear()
                        self._calc_zero_by_cc.clear()
                        for idx, row_data in enumerate(rows[:MAX_CALCULATED_CHANNELS]):
                            self._append_calc_row(idx)
                            r = self.calcTable.rowCount() - 1
                            cc = self._calc_channel_id_for_row(r)
                            try:
                                rid = str(row_data.get("channel_id", cc) or cc).strip()
                            except Exception:
                                rid = cc
                            if rid != cc:
                                self.calcTable.item(r, CCOL_ID).setText(rid)
                                cc = rid
                            formula = str(row_data.get("formula", "") or "")
                            self._calc_formula_by_cc[cc] = formula
                            self.calcTable.item(r, CCOL_FORMULA).setText(self._preview_formula_text(formula))
                            self.calcTable.item(r, CCOL_FORMULA).setToolTip(formula)
                            name = str(row_data.get("name", cc) or cc).strip() or cc
                            self.calcTable.item(r, CCOL_LABEL).setText(name)
                            en = bool(row_data.get("enabled", False))
                            pv = bool(row_data.get("plot_enabled", False))
                            self.calcTable.item(r, CCOL_ENABLE).setCheckState(QtCore.Qt.Checked if en else QtCore.Qt.Unchecked)
                            self.calcTable.item(r, CCOL_PLOT).setCheckState(QtCore.Qt.Checked if pv else QtCore.Qt.Unchecked)
                            z = row_data.get("zero", None)
                            self._calc_zero_by_cc[cc] = float(z) if z is not None else None
                            if z is not None:
                                self.calcTable.item(r, CCOL_ZERO_VAL).setText(f"{float(z):.6g}")
                    finally:
                        self._building_calc_table = False
        except Exception:
            pass
        if self.calcTable.rowCount() <= 0:
            self._populate_calc_table(reset=True)
        self._rebuild_calc_engine(update_core=True, test_runtime=True)
        self._sync_calc_plot_curves()
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
    def _queue_table_value_update(self, start_label_name, raw_value):
        try:
            key = str(start_label_name or "")
        except Exception:
            key = ""
        if not key:
            return
        pending = getattr(self, "_pending_table_updates", None)
        if not isinstance(pending, dict):
            pending = {}
            self._pending_table_updates = pending
        pending[key] = raw_value
        min_interval = float(getattr(self, "_table_value_min_interval_s", 0.12) or 0.12)
        now = time.monotonic()
        last = float(getattr(self, "_last_table_flush_ts", 0.0) or 0.0)
        if (now - last) >= min_interval:
            self._flush_table_value_updates()

    def _flush_table_value_updates(self):
        pending = getattr(self, "_pending_table_updates", None)
        if not isinstance(pending, dict) or not pending:
            return
        self._pending_table_updates = {}
        self._last_table_flush_ts = time.monotonic()
        for start_label_name, raw_value in pending.items():
            try:
                self._update_table_value(start_label_name, raw_value)
            except RuntimeError:
                pass
            except Exception:
                pass

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
    def _deactivate_all_channels_for_shutdown(self) -> None:
        old_auto = bool(getattr(self, "_auto_change", False))
        old_block = False
        try:
            old_block = bool(self.table.blockSignals(True))
        except Exception:
            old_block = False
        self._auto_change = True
        try:
            for r in range(self.table.rowCount()):
                it_en = self.table.item(r, COL_ENABLE)
                if it_en and it_en.checkState() == QtCore.Qt.Checked:
                    it_en.setCheckState(QtCore.Qt.Unchecked)
                it_val = self.table.item(r, COL_VALUE)
                if it_val is None:
                    it_val = QtWidgets.QTableWidgetItem("-")
                    self.table.setItem(r, COL_VALUE, it_val)
                it_val.setText("-")
            self._last_enabled_phys = []
            self._current_phys_order = []
            self._start_label_by_phys = {}
        finally:
            self._auto_change = old_auto
            try:
                self.table.blockSignals(old_block)
            except Exception:
                pass

    def _detach_acquisition_callbacks(self) -> None:
        try:
            self.acq.on_channel_value = None
        except Exception:
            pass
        try:
            self.acq.on_new_instant_block = None
        except Exception:
            pass
        try:
            self.acq.on_new_chart_points = None
        except Exception:
            pass

    def _stop_periodic_timers_for_shutdown(self) -> None:
        for tname in ("guiTimer", "_count_timer", "_backlog_timer", "_perf_timer", "_table_flush_timer", "_ui_profile_timer"):
            try:
                t = getattr(self, tname, None)
                if t is not None and t.isActive():
                    t.stop()
            except Exception:
                pass

    def _close_sync_agent_for_shutdown(self) -> None:
        try:
            agent = self._sync_agent
            self._sync_agent = None
            if agent is None:
                return
            try:
                agent._stop_event.set()
            except Exception:
                pass
            try:
                agent._close_socket()
            except Exception:
                pass
            try:
                QtCore.QTimer.singleShot(0, agent.close)
            except Exception:
                pass
        except BaseException:
            pass

    def _shutdown_core_for_close(self) -> None:
        try:
            self.acq.set_recording(False)
        except BaseException:
            pass
        try:
            self.acq.stop_graceful()
        except BaseException:
            pass
        try:
            self.acq.stop()
        except BaseException:
            pass

    def _disconnect_ui_signals_for_shutdown(self) -> None:
        try:
            self.sigInstantBlock.disconnect()
        except BaseException:
            pass
        try:
            self.sigChartPoints.disconnect()
        except BaseException:
            pass
        try:
            self.channelValueUpdated.disconnect()
        except BaseException:
            pass

    def _run_shutdown_state_machine(self) -> None:
        if bool(getattr(self, "_shutdown_in_progress", False)):
            return
        self._shutdown_in_progress = True
        phases = [
            ("deactivate_channels", self._deactivate_all_channels_for_shutdown),
            ("detach_callbacks", self._detach_acquisition_callbacks),
            ("stop_timers", self._stop_periodic_timers_for_shutdown),
            ("save_config", self._save_config),
            ("stop_core", self._shutdown_core_for_close),
            ("disconnect_signals", self._disconnect_ui_signals_for_shutdown),
        ]
        for name, fn in phases:
            self._shutdown_phase = name
            try:
                fn()
            except BaseException:
                pass
        self._shutdown_phase = "done"

    def _shutdown_phase_steps(self):
        phases = [
            ("deactivate_channels", self._deactivate_all_channels_for_shutdown),
            ("detach_callbacks", self._detach_acquisition_callbacks),
            ("stop_timers", self._stop_periodic_timers_for_shutdown),
            ("save_config", self._save_config),
            ("stop_core", self._shutdown_core_for_close),
        ]
        if hasattr(self, "_shutdown_fft_for_close"):
            try:
                phases.append(("stop_fft", self._shutdown_fft_for_close))
            except Exception:
                pass
        phases.append(("disconnect_signals", self._disconnect_ui_signals_for_shutdown))
        return phases

    def _phase_label_for_user_close(self, phase_name: str) -> str:
        mapping = {
            "deactivate_channels": "Disattivazione canali...",
            "detach_callbacks": "Distacco callback...",
            "stop_timers": "Arresto timer...",
            "save_config": "Salvataggio configurazione...",
            "stop_core": "Arresto core acquisizione...",
            "stop_fft": "Arresto worker FFT...",
            "disconnect_signals": "Disconnessione segnali UI...",
        }
        return mapping.get(str(phase_name or ""), "Chiusura modulo in corso...")

    def _append_guided_close_detail(self, text: str) -> None:
        msg = str(text or "").strip()
        if not msg:
            return
        box = getattr(self, "_guided_close_details", None)
        if box is None:
            return
        try:
            box.appendPlainText(msg)
            cursor = box.textCursor()
            cursor.movePosition(QtGui.QTextCursor.End)
            box.setTextCursor(cursor)
        except Exception:
            pass

    def _close_guided_progress_dialog(self) -> None:
        dlg = getattr(self, "_guided_close_dialog", None)
        if dlg is not None:
            try:
                dlg.close()
                dlg.deleteLater()
            except Exception:
                pass
        self._guided_close_dialog = None
        self._guided_close_label = None
        self._guided_close_progress = None
        self._guided_close_details = None

    def _fail_guided_close(self, details: str) -> None:
        self._close_request_running = False
        self._allow_close_after_shutdown = False
        self._shutdown_in_progress = False
        self._shutdown_phase = "error"
        try:
            if bool(getattr(self, "_module_closing_notified", False)) and self._sync_agent is not None:
                self._sync_agent.send_event(
                    "MODULE_CLOSE_FAILED",
                    {"error": "Chiusura modulo non completata.", "traceback": str(details or "")},
                )
        except Exception:
            pass
        self._module_closing_notified = False
        self._append_guided_close_detail("ERRORE durante la chiusura guidata.")
        if details:
            self._append_guided_close_detail(details)
        box = QtWidgets.QMessageBox(self)
        box.setIcon(QtWidgets.QMessageBox.Critical)
        box.setWindowTitle("Chiusura modulo fallita")
        box.setText("La chiusura del modulo non ? stata completata.")
        box.setInformativeText("Il modulo resta aperto per evitare uno stato incoerente.")
        if details:
            box.setDetailedText(details)
        box.exec_()
        self._close_guided_progress_dialog()

    def _run_next_guided_close_phase(self) -> None:
        if not bool(getattr(self, "_close_request_running", False)):
            return
        phases = list(getattr(self, "_guided_close_phases", []) or [])
        idx = int(getattr(self, "_guided_close_phase_index", 0) or 0)
        label = getattr(self, "_guided_close_label", None)
        progress = getattr(self, "_guided_close_progress", None)
        if idx >= len(phases):
            self._shutdown_phase = "done"
            self._close_request_running = False
            self._allow_close_after_shutdown = True
            self._append_guided_close_detail("Fasi completate. Chiusura finestra...")
            try:
                if progress is not None:
                    progress.setValue(len(phases))
            except Exception:
                pass
            self._close_guided_progress_dialog()
            QtCore.QTimer.singleShot(0, self._finalize_guided_close_exit)
            return

        phase_name, fn = phases[idx]
        phase_label = self._phase_label_for_user_close(phase_name)
        self._shutdown_phase = str(phase_name)
        self._shutdown_in_progress = True
        self._append_guided_close_detail(f"[{idx + 1}/{len(phases)}] START {phase_name}")
        try:
            if label is not None:
                label.setText(phase_label)
            if progress is not None:
                progress.setValue(idx)
        except Exception:
            pass
        QtWidgets.QApplication.processEvents()
        try:
            fn()
            self._append_guided_close_detail(f"[{idx + 1}/{len(phases)}] OK {phase_name}")
        except BaseException:
            self._fail_guided_close(traceback.format_exc())
            return

        self._guided_close_phase_index = idx + 1
        try:
            if progress is not None:
                progress.setValue(self._guided_close_phase_index)
        except Exception:
            pass
        QtCore.QTimer.singleShot(0, self._run_next_guided_close_phase)

    def _start_guided_close(self, require_confirmation: bool = True, allow_recording_close: bool = False, show_dialog: bool = True) -> None:
        if bool(getattr(self, "_close_request_running", False)):
            return
        try:
            recording = bool(self.acq.recording_enabled)
        except Exception:
            recording = False
        if recording and not bool(allow_recording_close):
            box = QtWidgets.QMessageBox(self)
            box.setIcon(QtWidgets.QMessageBox.Information)
            box.setWindowTitle("Chiusura non consentita")
            box.setText("Il modulo sta acquisendo.")
            if self._sync_agent is not None:
                box.setInformativeText("Arresta la sessione con 'Stop e ricomponi' dello chassis prima di chiudere il modulo.")
            else:
                box.setInformativeText("Arresta prima il modulo con 'Stop e ricomponi'.")
            box.exec_()
            return
        if require_confirmation and (not self._confirm_user_close_request()):
            return
        try:
            if self._sync_agent is not None and not bool(getattr(self, "_module_closing_notified", False)):
                self._sync_agent.send_event("MODULE_CLOSING", {"reason": "user_close"})
                self._module_closing_notified = True
        except Exception:
            pass

        phases = list(self._shutdown_phase_steps())
        self._guided_close_phases = phases
        self._guided_close_phase_index = 0
        self._close_request_running = True
        self._allow_close_after_shutdown = False
        self._shutdown_in_progress = True

        self._guided_close_dialog = None
        self._guided_close_label = None
        self._guided_close_progress = None
        self._guided_close_details = None
        if show_dialog:
            dlg = QtWidgets.QDialog(self)
            dlg.setWindowTitle("Chiusura modulo")
            dlg.setWindowModality(QtCore.Qt.ApplicationModal)
            try:
                dlg.setWindowFlag(QtCore.Qt.WindowStaysOnTopHint, True)
            except Exception:
                pass
            dlg.setMinimumWidth(560)
            layout = QtWidgets.QVBoxLayout(dlg)
            layout.setContentsMargins(12, 12, 12, 12)
            layout.setSpacing(8)
            label = QtWidgets.QLabel("Chiusura modulo in corso...")
            label.setWordWrap(True)
            progress = QtWidgets.QProgressBar()
            progress.setRange(0, max(1, len(phases)))
            progress.setValue(0)
            details = QtWidgets.QPlainTextEdit()
            details.setReadOnly(True)
            details.setMinimumHeight(140)
            layout.addWidget(label)
            layout.addWidget(progress)
            layout.addWidget(details)
            self._guided_close_dialog = dlg
            self._guided_close_label = label
            self._guided_close_progress = progress
            self._guided_close_details = details
            try:
                dlg.show()
                dlg.raise_()
                dlg.activateWindow()
            except Exception:
                pass
        self._append_guided_close_detail("Richiesta chiusura modulo ricevuta.")
        self._append_guided_close_detail(f"Totale fasi: {len(phases)}")
        QtCore.QTimer.singleShot(0, self._run_next_guided_close_phase)

    def _finalize_guided_close_exit(self) -> None:
        try:
            self.close()
        except Exception:
            pass
        try:
            app = QtWidgets.QApplication.instance()
            if app is not None:
                QtCore.QTimer.singleShot(0, app.quit)
        except Exception:
            pass

    def closeEvent(self, event: QtGui.QCloseEvent):
        if bool(getattr(self, "_allow_close_after_shutdown", False)):
            self._allow_close_after_shutdown = False
            event.accept()
            super().closeEvent(event)
            try:
                app = QtWidgets.QApplication.instance()
                if app is not None:
                    QtCore.QTimer.singleShot(0, app.quit)
            except Exception:
                pass
            return
        event.ignore()
        self._start_guided_close(require_confirmation=True, allow_recording_close=False)

    def _on_zero_button_clicked(self, phys: str):
        """
        Azzeramento canale:
        - Legge il valore istantaneo ATTUALE (in unitaingegneristiche)
        - Lo mostra in colonna 'Valore azzerato'
        - Fissa lo zero nel core come valore RAW (Volt) dell'istante
        """
        # riga del canale
        r = self._find_row_by_phys(phys)
        if r < 0:
            return

        # 1) valore istantaneo in unitaingegneristiche (quello che vedi in UI)
        try:
            val_eng = self.acq.get_last_engineered(phys)
        except Exception:
            val_eng = None

        # unitaper visualizzazione
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
        self._set_calc_table_lock(lock)

    def _set_calc_table_lock(self, lock: bool) -> None:
        gray = QtGui.QColor("#e9ecef")
        white = QtGui.QColor("#ffffff")
        self.btnAddCalcChannel.setEnabled(not lock)
        self.btnResetCalc.setEnabled(not lock)
        self.chkCalcViewEnable.setEnabled(not lock)
        self.chkPhysViewEnable.setEnabled(not lock)
        nrows = self.calcTable.rowCount()
        for r in range(nrows):
            for col in (CCOL_ENABLE, CCOL_ID, CCOL_FORMULA, CCOL_LABEL, CCOL_VALUE, CCOL_ZERO_VAL, CCOL_PLOT):
                it = self.calcTable.item(r, col)
                if it is not None:
                    it.setBackground(gray if lock else white)
            it_en = self.calcTable.item(r, CCOL_ENABLE)
            if it_en is not None:
                if lock:
                    it_en.setFlags(QtCore.Qt.ItemIsSelectable | QtCore.Qt.ItemIsEnabled)
                else:
                    self._apply_calc_row_flags(r)
            it_label = self.calcTable.item(r, CCOL_LABEL)
            if it_label is not None:
                if lock:
                    it_label.setFlags(QtCore.Qt.ItemIsSelectable | QtCore.Qt.ItemIsEnabled)
                else:
                    it_label.setFlags(QtCore.Qt.ItemIsSelectable | QtCore.Qt.ItemIsEnabled | QtCore.Qt.ItemIsEditable)
            it_plot = self.calcTable.item(r, CCOL_PLOT)
            if it_plot is not None:
                if lock:
                    it_plot.setFlags(QtCore.Qt.ItemIsSelectable | QtCore.Qt.ItemIsEnabled)
                else:
                    it_plot.setFlags(QtCore.Qt.ItemIsSelectable | QtCore.Qt.ItemIsEnabled | QtCore.Qt.ItemIsUserCheckable)
            btn_zero = self.calcTable.cellWidget(r, CCOL_ZERO_BTN)
            if isinstance(btn_zero, QtWidgets.QPushButton):
                btn_zero.setEnabled(not lock)

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






