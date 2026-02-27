from PyQt5 import QtCore, QtGui, QtWidgets

from formula_examples_dialog import FormulaExamplesDialog


class FormulaEditorDialog(QtWidgets.QDialog):
    def __init__(self, channel_id: str, formula_text: str = "", parent=None):
        super().__init__(parent)
        self.setWindowTitle(f"Formula canale {channel_id}")
        # Rimuove il pulsante "?" dalla title bar su Windows.
        self.setWindowFlag(QtCore.Qt.WindowContextHelpButtonHint, False)
        self.resize(760, 420)
        self.setModal(True)

        layout = QtWidgets.QVBoxLayout(self)
        hint = QtWidgets.QLabel(
            "Usa np/sp/pd, Fs, aiX, ccX.\n"
            "Puoi scrivere un'espressione oppure una funzione: def ccX(ai0, cc0, Fs): ..."
        )
        hint.setWordWrap(True)
        hint_row = QtWidgets.QHBoxLayout()
        hint_row.addWidget(hint, 1)
        self.btnHelp = QtWidgets.QToolButton()
        self.btnHelp.setText("Info")
        self.btnHelp.setToolTip("Apri esempi formule")
        self.btnHelp.setAutoRaise(False)
        self.btnHelp.setCursor(QtCore.Qt.PointingHandCursor)
        self.btnHelp.setIcon(self.style().standardIcon(QtWidgets.QStyle.SP_MessageBoxInformation))
        self.btnHelp.setIconSize(QtCore.QSize(18, 18))
        self.btnHelp.setToolButtonStyle(QtCore.Qt.ToolButtonTextBesideIcon)
        self.btnHelp.setFixedHeight(30)
        self.btnHelp.setMinimumWidth(72)
        hint_row.addWidget(self.btnHelp, 0, QtCore.Qt.AlignTop)
        layout.addLayout(hint_row)

        self.editor = QtWidgets.QPlainTextEdit()
        self.editor.setLineWrapMode(QtWidgets.QPlainTextEdit.NoWrap)
        self.editor.setTabStopDistance(4 * QtGui.QFontMetrics(self.editor.font()).horizontalAdvance(" "))
        self.editor.setPlainText(str(formula_text or ""))
        layout.addWidget(self.editor, 1)

        self.lblError = QtWidgets.QLabel("")
        self.lblError.setStyleSheet("color: #b00020;")
        self.lblError.setWordWrap(True)
        layout.addWidget(self.lblError)

        buttons = QtWidgets.QHBoxLayout()
        buttons.addStretch(1)
        self.btnInsert = QtWidgets.QPushButton("Inserisci")
        self.btnCancel = QtWidgets.QPushButton("Annulla")
        buttons.addWidget(self.btnInsert)
        buttons.addWidget(self.btnCancel)
        layout.addLayout(buttons)

        self.btnCancel.clicked.connect(self.reject)
        self.btnInsert.clicked.connect(self.accept)
        self.btnHelp.clicked.connect(self._open_examples)

    def formula_text(self) -> str:
        return str(self.editor.toPlainText() or "")

    def show_error(self, message: str) -> None:
        msg = str(message or "Formula non valida.")
        self.lblError.setText(msg)
        self.editor.setStyleSheet("QPlainTextEdit { background: #ffe8e8; border: 1px solid #d32f2f; }")
        cursor = self.editor.textCursor()
        cursor.select(QtGui.QTextCursor.Document)
        self.editor.setTextCursor(cursor)
        self.editor.setFocus(QtCore.Qt.OtherFocusReason)

    def clear_error(self) -> None:
        self.lblError.setText("")
        self.editor.setStyleSheet("")

    def _open_examples(self) -> None:
        dlg = FormulaExamplesDialog(self)
        dlg.exec_()
