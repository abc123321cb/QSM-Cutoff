from enum import Enum

Mode  = Enum('Mode', ['gen', 'qfy', 'min']) # generate prime, quantify prime, minimize prime
UseMC = Enum('UseMC', ['sat', 'appMC'])

class QrmOptions():
    def __init__(self) -> None:
        self.verbose  = 0
        self.filename = ''
        self.mode  = Mode.gen 
        self.useMC = UseMC.sat
        self.all_solutions = False 
