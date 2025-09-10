import sys
from PyQt5 import QtWidgets
from ui import AcquisitionWindow
from acquisition import AcquisitionManager
from tdms_merge import TdmsMerger

def main():
    app = QtWidgets.QApplication(sys.argv)

    acq_manager = AcquisitionManager()
    window = AcquisitionWindow(acq_manager=acq_manager, merger=TdmsMerger())
    window.show()

    sys.exit(app.exec_())

if __name__ == "__main__":
    main()
