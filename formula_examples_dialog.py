from PyQt5 import QtCore, QtGui, QtWidgets


EXAMPLE_ITEMS = [
    (
        "Derivata filtrata (velocita)",
        """def cc0(ai0, Fs):
    n = len(ai0)
    if n < 11:
        return np.gradient(ai0, 1/Fs)
    w = min(151, n - 1 if (n - 1) % 2 == 1 else n - 2)
    y = sp.signal.savgol_filter(ai0, w, 3)
    d = np.gradient(y, 1/Fs)
    return sp.signal.savgol_filter(d, w, 3)""",
    ),
    ("Massimo storico", "max_storico(ai0)"),
    ("Minimo storico", "min_storico(ai0)"),
    ("media corrente", "media_corrente(ai0)"),
    ("media mobile", "media_mobile(ai0, 200)"),
]


class FormulaExamplesDialog(QtWidgets.QDialog):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setWindowTitle("Esempi formule canali calcolati")
        self.resize(760, 560)
        self.setModal(True)

        main = QtWidgets.QVBoxLayout(self)
        intro = QtWidgets.QLabel(
            "Esempi pronti all'uso. Le formule usano np/sp/pd, Fs, aiX, ccX.\n"
            "Le statistiche storiche (max/min/media) partono dall'abilitazione del canale calcolato."
        )
        intro.setWordWrap(True)
        main.addWidget(intro)

        scroll = QtWidgets.QScrollArea()
        scroll.setWidgetResizable(True)
        body = QtWidgets.QWidget()
        body_layout = QtWidgets.QVBoxLayout(body)
        body_layout.setContentsMargins(6, 6, 6, 6)
        body_layout.setSpacing(10)
        scroll.setWidget(body)
        main.addWidget(scroll, 1)

        for title, formula in EXAMPLE_ITEMS:
            box = QtWidgets.QGroupBox(title)
            box_layout = QtWidgets.QVBoxLayout(box)
            editor = QtWidgets.QPlainTextEdit()
            editor.setReadOnly(True)
            editor.setLineWrapMode(QtWidgets.QPlainTextEdit.NoWrap)
            editor.setPlainText(formula)
            editor.setMinimumHeight(64)
            editor.setTabStopDistance(4 * QtGui.QFontMetrics(editor.font()).horizontalAdvance(" "))
            box_layout.addWidget(editor)
            row = QtWidgets.QHBoxLayout()
            row.addStretch(1)
            btn_copy = QtWidgets.QPushButton("Copia")
            btn_copy.clicked.connect(lambda _=False, txt=formula: self._copy_formula(txt))
            row.addWidget(btn_copy)
            box_layout.addLayout(row)
            body_layout.addWidget(box)

        body_layout.addStretch(1)

        self.lbl_status = QtWidgets.QLabel("")
        self.lbl_status.setStyleSheet("color: #1f6f43;")
        main.addWidget(self.lbl_status)

        btn_close = QtWidgets.QPushButton("Chiudi")
        btn_close.clicked.connect(self.accept)
        row_bottom = QtWidgets.QHBoxLayout()
        row_bottom.addStretch(1)
        row_bottom.addWidget(btn_close)
        main.addLayout(row_bottom)

    def _copy_formula(self, text: str) -> None:
        try:
            QtWidgets.QApplication.clipboard().setText(str(text or ""))
            self.lbl_status.setText("Formula copiata negli appunti.")
            QtCore.QTimer.singleShot(2000, lambda: self.lbl_status.setText(""))
        except Exception:
            self.lbl_status.setText("Errore copia appunti.")
