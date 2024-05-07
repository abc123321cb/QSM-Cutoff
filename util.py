from enum import Enum
UseMC = Enum('UseMC', ['sat', 'appMC'])
class QrmOptions():
    def __init__(self) -> None:
        self.verbosity  = 0
        self.filename     = ''
        self.ivy_filename = ''
        self.vmt_filename = ''
        self.R_filename   = ''
        self.writeR = False
        self.useMC = UseMC.sat
        self.all_solutions = False