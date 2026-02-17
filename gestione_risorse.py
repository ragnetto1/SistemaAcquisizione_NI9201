import os
import xml.etree.ElementTree as ET
from typing import List, Optional, Tuple
import numpy as np
from PyQt5 import QtCore, QtWidgets
import pyqtgraph as pg

SENSOR_DB_DEFAULT = r"C:\UG-WORK\SistemaAcquisizione_NI9201\Sensor database.xml"

# XML tags
XML_ROOT = "Sensors"
XML_ITEM = "Sensor"
XML_NAME = "NomeRisorsa"
XML_UNIT = "GrandezzaFisica"
# vecchio schema (retro-compatibilità in lettura)
XML_V1V = "Valore1Volt"
XML_V1  = "Valore1"
XML_V2V = "Valore2Volt"
XML_V2  = "Valore2"
# nuovo schema (multi-punti)
XML_CAL = "CalibrationPoints"
XML_POINT = "Point"   # attr: volt, value

# New tag to specify which DAQ devices a sensor supports.
XML_SUPPORTED_DAQ = "supportedDAQ"


# -------- utility di base --------
def _ensure_db_exists(xml_path: str):
    if os.path.isfile(xml_path):
        return
    root = ET.Element(XML_ROOT)
    tree = ET.ElementTree(root)
    os.makedirs(os.path.dirname(xml_path) or ".", exist_ok=True)
    tree.write(xml_path, encoding="utf-8", xml_declaration=True)

def get_sensor_names(xml_path: str) -> List[str]:
    names: List[str] = []
    try:
        if not os.path.isfile(xml_path):
            return names
        tree = ET.parse(xml_path)
        root = tree.getroot()
        for s in root.findall(XML_ITEM):
            n = (s.findtext(XML_NAME, default="") or "").strip()
            if n:
                names.append(n)
    except Exception:
        pass
    return names


# -------- Dialog editor singolo sensore --------
class ResourceManagerDialog(QtWidgets.QDialog):
    """
    Editor per un sensore alla volta con punti:
      [Misura] [Volt] [Valore (unità)] [Elimina]
    Grafico live (punti + retta best-fit) e salvataggio XML.
    """
    def __init__(self, acq_manager, xml_path: Optional[str] = None, parent=None):
        super().__init__(parent)
        self.setWindowTitle("Definisci Tipo Risorsa — Editor sensore")
        self.resize(780, 640)

        self.acq = acq_manager
        self.xml_path = xml_path or SENSOR_DB_DEFAULT

        self._rows = []  # (btnMeasure, spinVolt, spinVal, lblVoltUnit, lblValUnit, btnDelete)

        self._build_ui()
        self._connect()
        self._refresh_names()
        self._update_plot()

    def _default_supported_daq_text(self) -> str:
        return "NI9201"

    # ---- UI ----
    def _build_ui(self):
        layout = QtWidgets.QVBoxLayout(self)

        # riga file DB
        top = QtWidgets.QHBoxLayout()
        self.txtPath = QtWidgets.QLineEdit(self.xml_path)
        self.btnBrowse = QtWidgets.QPushButton("Sfoglia…")
        self.btnNewFile = QtWidgets.QPushButton("Genera nuovo file")
        self.btnReload = QtWidgets.QPushButton("Ricarica")
        top.addWidget(QtWidgets.QLabel("Sensor DB:"))
        top.addWidget(self.txtPath, 1)
        top.addWidget(self.btnBrowse)
        top.addWidget(self.btnNewFile)
        top.addWidget(self.btnReload)
        layout.addLayout(top)

        # form sensore
        form = QtWidgets.QGridLayout()
        form.setVerticalSpacing(6)
        r = 0
        # Nome risorsa
        self.cmbName = QtWidgets.QComboBox()
        self.cmbName.setEditable(True)
        form.addWidget(QtWidgets.QLabel("Nome risorsa"), r, 0)
        form.addWidget(self.cmbName, r, 1, 1, 3)
        r += 1

        # Supported DAQ / schede compatibili
        # Campo che permette di indicare quali modelli di scheda DAQ sono supportati dal sensore.
        self.txtSupportedDAQ = QtWidgets.QLineEdit()
        form.addWidget(QtWidgets.QLabel("Schede compatibili"), r, 0)
        form.addWidget(self.txtSupportedDAQ, r, 1, 1, 3)
        r += 1

        # Grandezza fisica (unità)
        self.txtUnit = QtWidgets.QLineEdit()
        form.addWidget(QtWidgets.QLabel("Grandezza fisica"), r, 0)
        form.addWidget(self.txtUnit, r, 1, 1, 3)
        r += 1

        self.cmbChannel = QtWidgets.QComboBox()
        for i in range(8):
            self.cmbChannel.addItem(f"ai{i}")
        form.addWidget(QtWidgets.QLabel("Canale di riferimento"), r, 0)
        form.addWidget(self.cmbChannel, r, 1, 1, 3); r += 1

        layout.addLayout(form)

        # header punti (compatti, nessun placeholder superfluo)
        header = QtWidgets.QGridLayout()
        header.setContentsMargins(0, 0, 0, 0)
        header.setHorizontalSpacing(16)
        header.addWidget(QtWidgets.QLabel(""), 0, 0)  # per il bottone Misura
        lblV = QtWidgets.QLabel("Volt")
        lblX = QtWidgets.QLabel("Valore (unità)")
        font_b = lblV.font(); font_b.setBold(True)
        lblV.setFont(font_b); lblX.setFont(font_b)
        header.addWidget(lblV, 0, 1)
        header.addWidget(lblX, 0, 3)
        layout.addLayout(header)

        # area punti (scrollable), allineata in alto
        self.pointsArea = QtWidgets.QScrollArea()
        self.pointsArea.setWidgetResizable(True)
        self.pointsArea.setVerticalScrollBarPolicy(QtCore.Qt.ScrollBarAlwaysOn)
        self.pointsArea.setHorizontalScrollBarPolicy(QtCore.Qt.ScrollBarAlwaysOff)
        self.pointsWidget = QtWidgets.QWidget()
        self.pointsLayout = QtWidgets.QGridLayout(self.pointsWidget)
        self.pointsLayout.setContentsMargins(0, 0, 0, 0)
        self.pointsLayout.setHorizontalSpacing(16)
        self.pointsLayout.setVerticalSpacing(4)
        # colonne: 0=Misura(btn), 1=Volt(spin), 2=Volt unit(lbl), 3=Val(spin), 4=Val unit(lbl), 5=Elimina(btn)
        self.pointsLayout.setAlignment(QtCore.Qt.AlignTop)
        # miglior allineamento: le colonne con gli spinbox si allargano
        self.pointsLayout.setColumnStretch(1, 1)
        self.pointsLayout.setColumnStretch(3, 1)
        self.pointsArea.setWidget(self.pointsWidget)
        layout.addWidget(self.pointsArea, 1)

        # grafico
        self.plot = pg.PlotWidget(title="Calibrazione: Valore vs Volt")
        self.plot.showGrid(x=True, y=True, alpha=0.3)
        self.plot.setLabel("bottom", "Volt")
        self.plot.setLabel("left", "Valore")
        self.scatter = self.plot.plot([], [], pen=None, symbol="o", symbolSize=7)
        self.line = self.plot.plot([], [], pen=pg.mkPen(width=2))
        layout.addWidget(self.plot, 2)

        # bottoni
        btm = QtWidgets.QHBoxLayout()
        self.btnAddPoint = QtWidgets.QPushButton("Aggiungi punto di calibrazione")
        self.btnApply = QtWidgets.QPushButton("Applica valori")
        self.btnClose = QtWidgets.QPushButton("Chiudi")
        btm.addWidget(self.btnAddPoint)
        btm.addStretch(1)
        btm.addWidget(self.btnApply)
        btm.addWidget(self.btnClose)
        layout.addLayout(btm)

        # almeno 2 punti iniziali
        self._add_point_row()
        self._add_point_row()
        self._update_delete_buttons_enabled()

    def _connect(self):
        self.btnBrowse.clicked.connect(self._choose_db)
        self.btnNewFile.clicked.connect(self._new_db)
        self.btnReload.clicked.connect(self._refresh_names)
        self.btnAddPoint.clicked.connect(lambda: (self._add_point_row(), self._update_delete_buttons_enabled(), self._update_plot()))
        self.btnApply.clicked.connect(self._apply_save)
        self.btnClose.clicked.connect(self.accept)
        self.cmbName.currentTextChanged.connect(lambda _: (self._load_selected_sensor(self.cmbName.currentText()), self._update_plot()))
        self.txtUnit.textChanged.connect(lambda _: (self._refresh_unit_labels(), self._update_plot()))

    # ---- helper punti ----
    def _add_point_row(self, v=None, x=None):
        row = len(self._rows)

        btnM = QtWidgets.QPushButton("Misura")
        btnM.setFixedWidth(90)

        spinV = QtWidgets.QDoubleSpinBox()
        spinV.setDecimals(9); spinV.setRange(-1e12, 1e12); spinV.setValue(v if v is not None else 0.0)
        spinV.setButtonSymbols(QtWidgets.QAbstractSpinBox.NoButtons)

        lblVoltUnit = QtWidgets.QLabel("Volt")
        lblVoltUnit.setMinimumWidth(34)

        spinX = QtWidgets.QDoubleSpinBox()
        spinX.setDecimals(9); spinX.setRange(-1e12, 1e12); spinX.setValue(x if x is not None else 0.0)
        spinX.setButtonSymbols(QtWidgets.QAbstractSpinBox.NoButtons)

        lblValUnit = QtWidgets.QLabel(self.txtUnit.text().strip())
        lblValUnit.setMinimumWidth(34)

        btnDel = QtWidgets.QPushButton("Elimina")
        btnDel.setFixedWidth(90)

        # posiziona la riga
        self.pointsLayout.addWidget(btnM,        row, 0)
        self.pointsLayout.addWidget(spinV,       row, 1)
        self.pointsLayout.addWidget(lblVoltUnit, row, 2, QtCore.Qt.AlignLeft)
        self.pointsLayout.addWidget(spinX,       row, 3)
        self.pointsLayout.addWidget(lblValUnit,  row, 4, QtCore.Qt.AlignLeft)
        self.pointsLayout.addWidget(btnDel,      row, 5, QtCore.Qt.AlignRight)

        # connessioni
        btnM.clicked.connect(lambda _, w=spinV: self._measure_into_widget(w))
        btnDel.clicked.connect(lambda _, tup=(btnM, spinV, spinX, lblVoltUnit, lblValUnit, btnDel): self._delete_row(tup))
        spinV.valueChanged.connect(lambda _=None: self._update_plot())
        spinX.valueChanged.connect(lambda _=None: self._update_plot())

        self._rows.append((btnM, spinV, spinX, lblVoltUnit, lblValUnit, btnDel))

    def _delete_row(self, tup):
        """Rimuove una riga (senza salvare sul DB finché non premi 'Applica valori')."""
        try:
            idx = self._rows.index(tup)
        except ValueError:
            return
        for w in tup:
            w.deleteLater()
        del self._rows[idx]
        self._rebuild_points_grid()
        self._update_delete_buttons_enabled()
        self._update_plot()

    def _rebuild_points_grid(self):
        while self.pointsLayout.count():
            item = self.pointsLayout.takeAt(0)
            w = item.widget()
            if w is not None:
                self.pointsLayout.removeWidget(w)
        for r, tup in enumerate(self._rows):
            btnM, spinV, spinX, lblVoltUnit, lblValUnit, btnDel = tup
            self.pointsLayout.addWidget(btnM,        r, 0)
            self.pointsLayout.addWidget(spinV,       r, 1)
            self.pointsLayout.addWidget(lblVoltUnit, r, 2, QtCore.Qt.AlignLeft)
            self.pointsLayout.addWidget(spinX,       r, 3)
            self.pointsLayout.addWidget(lblValUnit,  r, 4, QtCore.Qt.AlignLeft)
            self.pointsLayout.addWidget(btnDel,      r, 5, QtCore.Qt.AlignRight)

    def _update_delete_buttons_enabled(self):
        # abilita "Elimina" solo se ci sono almeno 3 righe (per mantenere >=2 punti)
        enable = len(self._rows) >= 3
        for _, _, _, _, _, btnDel in self._rows:
            btnDel.setEnabled(enable)

    def _clear_points(self):
        for tup in self._rows:
            for w in tup:
                w.deleteLater()
        self._rows.clear()

    def _measure_into_widget(self, spinV: QtWidgets.QDoubleSpinBox):
        ch = self.cmbChannel.currentText().strip()
        # Se il canale non è abilitato nell'acquisizione principale, chiedi all'utente se abilitarlo
        parent_win = None
        try:
            parent_win = self.parent()
        except Exception:
            parent_win = None
        if parent_win is not None and hasattr(parent_win, 'is_channel_enabled') and hasattr(parent_win, 'enable_physical_channel'):
            try:
                if not parent_win.is_channel_enabled(ch):
                    res = QtWidgets.QMessageBox.question(
                        self, "Canale non abilitato",
                        f"Il canale {ch} non è abilitato, vuoi abilitarlo per prendere la misura?",
                        QtWidgets.QMessageBox.Yes | QtWidgets.QMessageBox.No,
                        QtWidgets.QMessageBox.Yes)
                    if res == QtWidgets.QMessageBox.Yes:
                        try:
                            parent_win.enable_physical_channel(ch)
                            # Aggiorna l'acquisizione con la nuova configurazione
                            parent_win._update_acquisition_from_table()
                        except Exception:
                            pass
                    else:
                        return
            except Exception:
                pass
        # Procedi a leggere il valore istantaneo
        val = None
        try:
            val = self.acq.get_last_value(ch, apply_zero=False)
        except Exception:
            val = None
        if val is None:
            QtWidgets.QMessageBox.warning(self, "Attenzione", "Nessun valore disponibile (acquisizione non attiva?).")
            return
        try:
            spinV.setValue(float(val))  # triggerà _update_plot via valueChanged
        except Exception:
            pass

    def _refresh_unit_labels(self):
        unit = self.txtUnit.text().strip()
        for _, _, _, _, lblValUnit, _ in self._rows:
            lblValUnit.setText(unit)
        # aggiorna asse Y
        self.plot.setLabel("left", f"Valore ({unit})" if unit else "Valore")

    # ---- raccolta dati & fit ----
    def _collect_points(self) -> Tuple[np.ndarray, np.ndarray]:
        volts = []
        vals = []
        for (_, spinV, spinX, _, _, _) in self._rows:
            v = float(spinV.value()); x = float(spinX.value())
            if np.isfinite(v) and np.isfinite(x):
                volts.append(v); vals.append(x)
        if len(volts) == 0:
            return np.array([]), np.array([])
        return np.asarray(volts, dtype=float), np.asarray(vals, dtype=float)

    def _best_fit(self, V: np.ndarray, X: np.ndarray) -> Optional[Tuple[float, float]]:
        if V.size < 2:
            return None
        A = np.vstack([V, np.ones_like(V)]).T
        a, b = np.linalg.lstsq(A, X, rcond=None)[0]
        return float(a), float(b)

    def _update_plot(self):
        V, X = self._collect_points()
        # punti
        self.scatter.setData(V, X)
        # retta
        title = "Calibrazione: Valore vs Volt"
        if V.size >= 2:
            fit = self._best_fit(V, X)
            if fit is not None:
                a, b = fit
                vmin, vmax = float(V.min()), float(V.max())
                if vmin == vmax:
                    vmin -= 1.0; vmax += 1.0
                xs = np.linspace(vmin, vmax, 200)
                ys = a * xs + b
                self.line.setData(xs, ys)
                sign = "+" if b >= 0 else "−"
                title = f"Best-fit: y = {a:.6g}·V {sign} {abs(b):.6g}"
            else:
                self.line.setData([], [])
        else:
            self.line.setData([], [])
        self.plot.setTitle(title)

    # ---- DB ops ----
    def _choose_db(self):
        path, _ = QtWidgets.QFileDialog.getOpenFileName(self, "Seleziona Sensor database.xml", "", "XML (*.xml)")
        if path:
            self.txtPath.setText(path)
            self.xml_path = path
            self._refresh_names()
            self._update_plot()

    def _new_db(self):
        path, _ = QtWidgets.QFileDialog.getSaveFileName(self, "Crea nuovo Sensor database.xml", "", "XML (*.xml)")
        if not path:
            return
        if not path.lower().endswith(".xml"):
            path += ".xml"
        try:
            _ensure_db_exists(path)
            self.txtPath.setText(path)
            self.xml_path = path
            QtWidgets.QMessageBox.information(self, "Creato", f"Creato file XML:\n{path}")
            self._refresh_names()
            self._update_plot()
        except Exception as e:
            QtWidgets.QMessageBox.critical(self, "Errore", f"Impossibile creare il file:\n{e}")

    def _refresh_names(self):
        names = get_sensor_names(self.xml_path)
        self.cmbName.blockSignals(True)
        self.cmbName.clear()
        self.cmbName.setEditable(True)
        self.cmbName.addItems(names)
        self.cmbName.setEditText("New")  # per creare un nuovo sensore
        self.cmbName.blockSignals(False)
        self.txtUnit.setText("")
        # Imposta il campo supportedDAQ al valore predefinito quando non è selezionato alcun sensore
        try:
            # Valore predefinito allineato alla scheda del modulo corrente.
            self.txtSupportedDAQ.setText(self._default_supported_daq_text())
        except Exception:
            pass
        self._clear_points()
        self._add_point_row()
        self._add_point_row()
        self._update_delete_buttons_enabled()
        self._update_plot()

    def _load_selected_sensor(self, name: str):
        if not name or name.strip().lower() == "new":
            self.txtUnit.setText("")
            self._clear_points()
            self._add_point_row(); self._add_point_row()
            self._update_delete_buttons_enabled()
            self._update_plot()
            return
        if not os.path.isfile(self.xml_path):
            return
        try:
            tree = ET.parse(self.xml_path)
            root = tree.getroot()
        except Exception:
            return
        # cerca sensore
        sens = None
        for s in root.findall(XML_ITEM):
            if (s.findtext(XML_NAME, default="") or "").strip().lower() == name.strip().lower():
                sens = s; break
        if sens is None:
            return
        # unità
        self.txtUnit.setText(sens.findtext(XML_UNIT, default=""))
        # supportedDAQ: stringa con la lista dei modelli compatibili
        try:
            sup = sens.findtext(XML_SUPPORTED_DAQ, default="").strip()
            if sup:
                # Mostra il valore esistente
                self.txtSupportedDAQ.setText(sup)
            else:
                # Se non è definito, imposta il valore predefinito
                self.txtSupportedDAQ.setText(self._default_supported_daq_text())
        except Exception:
            # In caso di eccezione lascio il default
            try:
                self.txtSupportedDAQ.setText(self._default_supported_daq_text())
            except Exception:
                pass
        # carica punti (nuovo schema), altrimenti da vecchio schema
        pts = []
        cal = sens.find(XML_CAL)
        if cal is not None:
            for pt in cal.findall(XML_POINT):
                try:
                    v = float(pt.get("volt", "nan"))
                    x = float(pt.get("value", "nan"))
                except Exception:
                    continue
                if np.isfinite(v) and np.isfinite(x):
                    pts.append((v, x))
        else:
            # vecchio schema
            def _f(tag):
                try:
                    return float(sens.findtext(tag, default="0") or "0")
                except Exception:
                    return 0.0
            pts = [(_f(XML_V1V), _f(XML_V1)), (_f(XML_V2V), _f(XML_V2))]

        # riempi UI
        self._clear_points()
        if len(pts) == 0:
            self._add_point_row(); self._add_point_row()
        else:
            for v, x in pts:
                self._add_point_row(v, x)
        self._update_delete_buttons_enabled()
        self._refresh_unit_labels()
        self._update_plot()

    def _apply_save(self):
        name = self.cmbName.currentText().strip()
        if not name or name.lower() == "new":
            name, ok = QtWidgets.QInputDialog.getText(self, "Nuovo sensore", "Nome risorsa:")
            if not ok or not name.strip():
                return
            name = name.strip()

        unit = self.txtUnit.text().strip()
        # Valore del campo supportedDAQ (stringa separata da virgole)
        supported_daq_text = self.txtSupportedDAQ.text().strip()
        # raccogli punti validi
        V, X = self._collect_points()
        if V.size < 2:
            QtWidgets.QMessageBox.warning(self, "Attenzione", "Servono almeno 2 punti per la calibrazione.")
            return

        fit = self._best_fit(V, X)
        if fit is None:
            QtWidgets.QMessageBox.warning(self, "Attenzione", "Impossibile calcolare il best-fit con questi punti.")
            return
        a, b = fit

        # scrivi XML (nuovo schema multi-punti)
        _ensure_db_exists(self.xml_path)
        try:
            tree = ET.parse(self.xml_path)
            root = tree.getroot()
        except Exception:
            root = ET.Element(XML_ROOT)
            tree = ET.ElementTree(root)

        # trova/crea nodo sensore
        found = None
        for s in root.findall(XML_ITEM):
            if (s.findtext(XML_NAME, default="") or "").strip().lower() == name.lower():
                found = s; break
        if found is None:
            found = ET.SubElement(root, XML_ITEM)
            ET.SubElement(found, XML_NAME).text = name

        # Rimuovi eventuali vecchi tag di schema 2-punti
        for t in (XML_V1V, XML_V1, XML_V2V, XML_V2):
            old = found.find(t)
            if old is not None:
                found.remove(old)

        # Rimuovi unità e supportedDAQ se già presenti (verranno reinseriti in ordine)
        try:
            old_sup = found.find(XML_SUPPORTED_DAQ)
            if old_sup is not None:
                found.remove(old_sup)
        except Exception:
            pass
        try:
            old_unit = found.find(XML_UNIT)
            if old_unit is not None:
                found.remove(old_unit)
        except Exception:
            pass

        # Crea elementi unit e supportedDAQ con il valore corrente
        sup_elem = ET.Element(XML_SUPPORTED_DAQ)
        # Se il campo è vuoto, usa la stringa predefinita del modulo corrente.
        sup_elem.text = supported_daq_text if supported_daq_text else self._default_supported_daq_text()
        unit_elem = ET.Element(XML_UNIT)
        unit_elem.text = unit

        # Inserisci i nuovi elementi subito dopo il NomeRisorsa
        # Trova l'indice del tag NomeRisorsa all'interno di found
        inserted = False
        try:
            children = list(found)
            idx_name = None
            for i, child in enumerate(children):
                if child.tag == XML_NAME:
                    idx_name = i
                    break
            if idx_name is not None:
                # Inserisci i nuovi elementi in ordine: supportedDAQ poi unit
                found.insert(idx_name + 1, sup_elem)
                found.insert(idx_name + 2, unit_elem)
                inserted = True
        except Exception:
            pass
        if not inserted:
            # Se NomeRisorsa non è stato trovato, aggiungi alla fine
            found.append(sup_elem)
            found.append(unit_elem)

        # Rimuovi eventuali vecchi punti di calibrazione
        cal = found.find(XML_CAL)
        if cal is not None:
            found.remove(cal)
        # Scrivi i punti (nuovo schema multi-punti)
        cal = ET.SubElement(found, XML_CAL)
        for v, x in zip(V.tolist(), X.tolist()):
            pt = ET.SubElement(cal, XML_POINT)
            pt.set("volt", f"{float(v):.12g}")
            pt.set("value", f"{float(x):.12g}")

        try:
            tree.write(self.xml_path, encoding="utf-8", xml_declaration=True)
            sign = "+" if b >= 0 else "−"
            QtWidgets.QMessageBox.information(
                self, "Salvato",
                f"Salvato \"{name}\"  — unità: {unit}  |  best-fit: y = {a:.6g}·V {sign} {abs(b):.6g}"
            )
            self._refresh_names()
            self.cmbName.setEditText(name)
            self._update_plot()
        except Exception as e:
            QtWidgets.QMessageBox.critical(self, "Errore", f"Impossibile salvare:\n{e}")
