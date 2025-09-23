# ui.py
from PyQt5 import QtCore, QtWidgets, QtGui
import pyqtgraph as pg
from collections import deque
import numpy as np
import os
import xml.etree.ElementTree as ET
import datetime

pg.setConfigOptions(useOpenGL=True, antialias=False)

# Colonne tabella
COL_ENABLE   = 0
COL_PHYS     = 1
COL_TYPE     = 2   # Tipo risorsa (Voltage o sensori dal DB)
COL_LABEL    = 3   # Nome canale (etichetta utente)
COL_VALUE    = 4   # Valore istantaneo (con unità se selezionata)
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

        self.setWindowTitle("NI 9201 Acquisition — Demo Architettura")
        self.resize(1200, 740)

        # stati UI/logica
        self._building_table = False
        self._auto_change = False
        self._device_ready = False

        # mappature canali
        self._current_phys_order = []                    # ordine fisico corrente avviato
        self._label_by_phys = {f"ai{i}": f"ai{i}" for i in range(8)}   # label utente “Nome canale”
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

        # UI
        self._build_ui()
        self._connect_signals()

        # inizializzazione
        self.refresh_devices()

    # ----------------------------- Build UI -----------------------------
    def _build_ui(self):
        central = QtWidgets.QWidget()
        self.setCentralWidget(central)
        main = QtWidgets.QVBoxLayout(central)

        # Riga superiore: rileva + device + definisci risorse
        top = QtWidgets.QHBoxLayout()
        self.btnRefresh = QtWidgets.QPushButton("Rileva schede")
        self.cmbDevice = QtWidgets.QComboBox()
        self.btnDefineTypes = QtWidgets.QPushButton("Definisci Tipo Risorsa")
        top.addWidget(self.btnRefresh)
        top.addWidget(QtWidgets.QLabel("Dispositivo:"))
        top.addWidget(self.cmbDevice, 1)
        top.addWidget(self.btnDefineTypes)
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
        self.btnBrowseDir = QtWidgets.QPushButton("Sfoglia cartella…")
        self.txtBaseName = QtWidgets.QLineEdit(self._base_filename)
        self.btnStart = QtWidgets.QPushButton("Salva dati")            # passa a “Salvo in (xx s)…”
        self.btnStop = QtWidgets.QPushButton("Stop e ricomponi…")
        self.btnStop.setEnabled(False)

        bottom.addWidget(QtWidgets.QLabel("Percorso salvataggio:"))
        bottom.addWidget(self.txtSaveDir, 1)
        bottom.addWidget(self.btnBrowseDir)
        bottom.addSpacing(12)
        bottom.addWidget(QtWidgets.QLabel("Nome file:"))
        bottom.addWidget(self.txtBaseName)
        bottom.addStretch(1)
        bottom.addWidget(self.btnStart)
        bottom.addWidget(self.btnStop)
        main.addLayout(bottom)

        # Timer aggiornamento grafici
        self.guiTimer = QtCore.QTimer(self)
        self.guiTimer.setInterval(50)
        self.guiTimer.timeout.connect(self._refresh_plots)

        # Status bar + etichetta sempre visibile con rate
        self.statusBar = QtWidgets.QStatusBar()
        self.setStatusBar(self.statusBar)
        self.lblRateInfo = QtWidgets.QLabel("—")
        self.statusBar.addPermanentWidget(self.lblRateInfo)

    def _connect_signals(self):
        # pulsanti
        self.btnRefresh.clicked.connect(self.refresh_devices)
        self.btnBrowseDir.clicked.connect(self._choose_folder)
        self.btnStart.clicked.connect(self._on_start_saving)
        self.btnStop.clicked.connect(self._on_stop)
        self.btnClearChart.clicked.connect(self._clear_chart)
        self.btnDefineTypes.clicked.connect(self._open_resource_manager)

        # tabella
        self.table.itemChanged.connect(self._on_table_item_changed)
        self.cmbDevice.currentIndexChanged.connect(self._on_device_changed)

        # callback dal core (rimappati in segnali Qt)
        self.channelValueUpdated.connect(self._update_table_value)
        self.sigInstantBlock.connect(self._slot_instant_block)
        self.sigChartPoints.connect(self._slot_chart_points)

        self.acq.on_channel_value = lambda name, val: self.channelValueUpdated.emit(name, val)
        self.acq.on_new_instant_block = lambda t, ys, names: self.sigInstantBlock.emit(t, ys, names)
        self.acq.on_new_chart_points = lambda t_pts, ys_pts, names: self.sigChartPoints.emit(t_pts, ys_pts, names)

    # ----------------------------- Devices -----------------------------
    def refresh_devices(self):
        """
        Popola la combo dispositivi includendo anche i moduli simulati.
        Se sono presenti più NI-9201, apre un dialog per scegliere:
        mostra 'nome modulo', 'chassis' e tag '[SIMULATED]'.
        """
        # usa i metadati completi dal core
        try:
            metas = self.acq.list_ni9201_devices_meta()
        except AttributeError:
            # retrocompat: se la versione del core non ha il metodo, fallback
            names = self.acq.list_ni9201_devices()
            metas = [{"name": n, "product_type": "NI 9201", "is_simulated": False,
                      "chassis": n.split("Mod")[0] if "Mod" in n else ""} for n in names]
        except Exception:
            metas = []

        # Aggiorna combo: testo "cDAQ1Mod1 — NI 9201 — (cDAQ1) [SIMULATED]" ma userData=nome pulito
        self.cmbDevice.blockSignals(True)
        self.cmbDevice.clear()
        for m in metas:
            name = m.get("name", "?")
            pt = m.get("product_type", "")
            ch = m.get("chassis", "")
            sim = " [SIMULATED]" if m.get("is_simulated") else ""
            label = f"{name} — {pt} — ({ch}){sim}" if ch else f"{name} — {pt}{sim}"
            self.cmbDevice.addItem(label, userData=name)
        self.cmbDevice.blockSignals(False)

        self._device_ready = bool(metas)

        # scelta automatica / dialog se più device
        if not metas:
            QtWidgets.QMessageBox.information(self, "Nessun dispositivo",
                                              "Nessun NI-9201 trovato. Verifica in NI-MAX (anche simulati).")
        elif len(metas) == 1:
            self.cmbDevice.setCurrentIndex(0)
        else:
            chosen = self._prompt_device_choice(metas)
            if chosen:
                # seleziona item con quel name in userData
                for i in range(self.cmbDevice.count()):
                    if self.cmbDevice.itemData(i) == chosen:
                        self.cmbDevice.setCurrentIndex(i)
                        break

        # come prima: ricostruzione tabella/definizioni/scale
        self._populate_table()
        self._populate_type_column()
        self._recompute_all_calibrations()
        self.lblRateInfo.setText("—")

    def _prompt_device_choice(self, metas):
        items = []
        for m in metas:
            name = m.get("name", "?")
            pt = m.get("product_type", "")
            ch = m.get("chassis", "")
            sim = " [SIMULATED]" if m.get("is_simulated") else ""
            label = f"{name} — {pt} — ({ch}){sim}" if ch else f"{name} — {pt}{sim}"
            items.append(label)
        item, ok = QtWidgets.QInputDialog.getItem(
            self, "Seleziona dispositivo",
            "Sono presenti più moduli NI-9201.\nScegli quello da usare:",
            items, 0, False
        )
        if not ok or not item:
            return None
        # estrai il name prima della prima " — "
        return item.split(" — ", 1)[0]

    def _on_device_changed(self, _):
        self._stop_acquisition_ui_only()
        self._reset_plots()
        self.lblRateInfo.setText("—")

    # ----------------------------- Sensor defs -----------------------------
    def _read_sensor_defs(self) -> dict:
        """
        Legge il file XML (multi-punti o 2-punti) e ritorna dict:
            name -> {unit, a, b}
        """
        defs = {}
        p = SENSOR_DB_DEFAULT
        if not os.path.isfile(p):
            return defs
        try:
            tree = ET.parse(p)
            root = tree.getroot()
            for s in root.findall(XML_ITEM):
                name = (s.findtext(XML_NAME, default="") or "").strip()
                if not name:
                    continue
                unit = (s.findtext(XML_UNIT, default="") or "").strip()

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
        names = []
        try:
            from gestione_risorse import get_sensor_names
            names = get_sensor_names(SENSOR_DB_DEFAULT)
        except Exception:
            pass
        for r in range(self.table.rowCount()):
            cmb: QtWidgets.QComboBox = self.table.cellWidget(r, COL_TYPE)
            if not isinstance(cmb, QtWidgets.QComboBox):
                continue
            cur = cmb.currentText()
            cmb.blockSignals(True)
            cmb.clear()
            cmb.setEditable(True)
            cmb.addItem("Voltage")
            for n in names:
                cmb.addItem(n)
            if cur and cur != "Voltage":
                idx = cmb.findText(cur)
                if idx >= 0:
                    cmb.setCurrentIndex(idx)
                else:
                    cmb.setEditText(cur)
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

            # Tipo risorsa
            cmbType = QtWidgets.QComboBox()
            cmbType.setEditable(True)
            cmbType.addItem("Voltage")
            cmbType.currentTextChanged.connect(lambda _t, row=i: self._type_changed_for_row(row))
            self.table.setCellWidget(i, COL_TYPE, cmbType)

            # Nome canale (label utente)
            labelItem = QtWidgets.QTableWidgetItem(self._label_by_phys.get(phys, phys))
            self.table.setItem(i, COL_LABEL, labelItem)

            # Valore istantaneo (solo display)
            valItem = QtWidgets.QTableWidgetItem("—")
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

    def _on_table_item_changed(self, item: QtWidgets.QTableWidgetItem):
        if self._building_table or self._auto_change:
            return
        r, c = item.row(), item.column()
        if c == COL_ENABLE:
            self._update_acquisition_from_table()
        elif c == COL_LABEL:
            phys = self.table.item(r, COL_PHYS).text().strip()
            self._label_by_phys[phys] = item.text().strip() or phys
            self._rebuild_legends()
            self._push_sensor_map_to_core()
            if self.btnStop.isEnabled():
                self._update_rate_label(self._current_phys_order)

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
            self.lblRateInfo.setText("—")
            return

        if phys == self._last_enabled_phys and self.btnStop.isEnabled():
            self._update_rate_label(phys)
            return

        # se già attiva, ferma e riavvia con nuova lista
        if self.btnStop.isEnabled():
            self.acq.stop()

        ok = self.acq.start(device_name=device, ai_channels=phys, channel_names=labels)
        if not ok:
            QtWidgets.QMessageBox.critical(self, "Errore", "Impossibile avviare l'acquisizione.")
            return

        self._current_phys_order = phys[:]
        self._start_label_by_phys = dict(zip(phys, labels))
        self._last_enabled_phys = phys[:]

        # grafici
        self._reset_plots_curves()
        self.btnStop.setEnabled(True)
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
                f"Limiti modulo → single {lim_single:.1f} kS/s, aggregato {lim_multi:.1f} kS/s"
            )
        except Exception:
            self.lblRateInfo.setText("—")

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
        self.lblRateInfo.setText("—")

    # ----------------------------- TDMS: folder/name, start/stop, countdown -----------------------------
    def _choose_folder(self):
        folder = QtWidgets.QFileDialog.getExistingDirectory(
            self, "Seleziona cartella di salvataggio", self.txtSaveDir.text() or DEFAULT_SAVE_DIR
        )
        if folder:
            self.txtSaveDir.setText(folder)

    def _on_start_saving(self):
        # deve essere attiva un’acquisizione
        if not self.btnStop.isEnabled():
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

        self.acq.set_output_directory(subdir)
        self.acq.set_recording(True)

        self._active_subdir = subdir
        self._save_dir = base_dir
        self._base_filename = base_name

        self._set_table_lock(True)
        # countdown
        self._countdown = 60
        self._update_start_button_text()
        if not self._count_timer.isActive():
            self._count_timer.start()

        # blocca i campi
        self.txtSaveDir.setEnabled(False)
        self.btnBrowseDir.setEnabled(False)
        self.txtBaseName.setEnabled(False)
        self.btnStart.setEnabled(False)
        
        

    def _tick_countdown(self):
        if not self.acq.recording_enabled:
            self._count_timer.stop()
            self.btnStart.setText("Salva dati")
            self.btnStart.setEnabled(True)
            return
        self._countdown -= 1
        if self._countdown <= 0:
            self._countdown = 60
        self._update_start_button_text()

    def _update_start_button_text(self):
        self.btnStart.setText(f"Salvo in ({self._countdown:02d} s) …")

    def _on_stop(self):
        # ferma core
        try:
            #self.acq.set_recording(False)
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

        final_path = os.path.join(self._save_dir, self._base_filename)
        try:
            from tdms_merge import TdmsMerger
            TdmsMerger().merge_temp_tdms(self._active_subdir, final_path)
            QtWidgets.QMessageBox.information(self, "Completato", f"TDMS finale creato:\n{final_path}")
        except Exception as e:
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

    def _reset_plots_curves(self):
        self._reset_plots()
        for phys in self._current_phys_order:
            unit = self._calib_by_phys.get(phys, {}).get("unit", "")
            base_label = self._label_by_phys.get(phys, phys)
            label = f"{base_label} [{unit}]" if unit else base_label

            c = self.pgChart.plot(name=label)
            try:
                c.setClipToView(True)
                c.setDownsampling(auto=True, mode='peak')
            except Exception:
                pass
            self._chart_curves_by_phys[phys] = c
            self._chart_legend.addItem(c, label)

            ic = self.pgInstant.plot(name=label)
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

    # ----------------------------- Definisci Tipo Risorsa -----------------------------
    def _open_resource_manager(self):
        try:
            from gestione_risorse import ResourceManagerDialog
        except Exception as e:
            QtWidgets.QMessageBox.critical(self, "Errore", f"Impossibile importare gestione_risorse:\n{e}")
            return
        dlg = ResourceManagerDialog(self.acq, xml_path=SENSOR_DB_DEFAULT, parent=self)
        dlg.exec_()
        # refresh liste e scale
        self._populate_type_column()
        self._recompute_all_calibrations()

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
        - Legge il valore istantaneo ATTUALE (in unità ingegneristiche)
        - Lo mostra in colonna 'Valore azzerato'
        - Fissa lo zero nel core come valore RAW (Volt) dell'istante
        """
        # riga del canale
        r = self._find_row_by_phys(phys)
        if r < 0:
            return

        # 1) valore istantaneo in unità ingegneristiche (quello che vedi in UI)
        try:
            val_eng = self.acq.get_last_engineered(phys)
        except Exception:
            val_eng = None

        # unità per visualizzazione
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
                    # rimuovo la possibilità di spuntare
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
        # applica lo stato all’acquisizione
        self._update_acquisition_from_table()