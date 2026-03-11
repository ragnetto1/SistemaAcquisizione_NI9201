from __future__ import annotations

from PyQt5 import QtWidgets

from ui import AcquisitionWindow as _BaseAcquisitionWindow


_CDAQ_THEME = """
QMainWindow, QWidget {
    background: #f4f6fa;
    color: #111827;
}
QLabel {
    color: #111827;
}
QGroupBox {
    border: 1px solid #cbd5e1;
    border-radius: 8px;
    margin-top: 8px;
    font-weight: 600;
    background: #ffffff;
}
QGroupBox::title {
    subcontrol-origin: margin;
    left: 10px;
    padding: 0 4px;
}
QLineEdit, QComboBox, QSpinBox, QDoubleSpinBox {
    border: 1px solid #cbd5e1;
    border-radius: 6px;
    padding: 4px 6px;
    background: #ffffff;
    min-height: 24px;
}
QTableWidget {
    background: #ffffff;
    alternate-background-color: #f8fafc;
    border: 1px solid #cbd5e1;
    gridline-color: #e2e8f0;
}
QHeaderView::section {
    background: #e2e8f0;
    color: #111827;
    padding: 6px;
    border: none;
    border-right: 1px solid #cbd5e1;
    border-bottom: 1px solid #cbd5e1;
    font-weight: 600;
}
QTabWidget::pane {
    border: 1px solid #bfdbfe;
    background: #ffffff;
    margin-top: 2px;
}
QTabBar::tab {
    background: #dbeafe;
    border: 1px solid #93c5fd;
    border-bottom: none;
    border-top-left-radius: 8px;
    border-top-right-radius: 8px;
    min-width: 120px;
    padding: 8px 14px;
    margin-right: 4px;
    color: #0f172a;
    font-weight: 600;
}
QTabBar::tab:selected {
    background: #ffffff;
    color: #1d4ed8;
}
QPushButton {
    border: 1px solid #94a3b8;
    border-radius: 8px;
    padding: 7px 12px;
    background: #e2e8f0;
    font-weight: 600;
}
QPushButton:hover {
    background: #dbeafe;
}
QPushButton:disabled {
    background: #e5e7eb;
    color: #9ca3af;
    border-color: #d1d5db;
}
QCheckBox {
    spacing: 7px;
}
QCheckBox::indicator {
    width: 16px;
    height: 16px;
}
"""


class AcquisitionWindow(_BaseAcquisitionWindow):
    def __init__(self, acq_manager, merger, parent=None):
        super().__init__(acq_manager=acq_manager, merger=merger, parent=parent)
        self._apply_cdaq_theme()

    def _apply_cdaq_theme(self) -> None:
        self.setStyleSheet(_CDAQ_THEME)

        soft = "QPushButton {background:#e2e8f0; border:1px solid #94a3b8;} QPushButton:hover {background:#dbeafe;}"
        accent = (
            "QPushButton {background:#d1fae5; border:1px solid #6ee7b7;}"
            " QPushButton:hover {background:#a7f3d0;}"
            " QPushButton:disabled {"
            " background:#d8f3e4;"
            " color:#1f5134;"
            " border:1px solid #9bcfb3;"
            " font-weight:700;"
            "}"
        )
        danger = "QPushButton {background:#fee2e2; border:1px solid #fca5a5;} QPushButton:hover {background:#fecaca;}"

        for name in ("btnRefresh", "btnDefineTypes", "btnSaveWorkspace", "btnLoadWorkspace", "btnMerge", "btnViewTDMS"):
            btn = getattr(self, name, None)
            if isinstance(btn, QtWidgets.QPushButton):
                btn.setStyleSheet(soft)

        for name in ("btnStart",):
            btn = getattr(self, name, None)
            if isinstance(btn, QtWidgets.QPushButton):
                btn.setStyleSheet(accent)

        for name in ("btnStop",):
            btn = getattr(self, name, None)
            if isinstance(btn, QtWidgets.QPushButton):
                btn.setStyleSheet(danger)

    def closeEvent(self, event):  # type: ignore[override]
        super().closeEvent(event)
