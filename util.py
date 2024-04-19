from typing import List

from enum import Enum
Mode  = Enum('Mode', ['ivy', 'vmt', 'gen', 'qfy', 'min']) 
# compile ivy, parse vmt, generate prime, quantify prime, minimize prime
UseMC = Enum('UseMC', ['sat', 'appMC'])
class QrmOptions():
    def __init__(self) -> None:
        self.verbosity  = 0
        self.filename = ''
        self.mode  = Mode.gen 
        self.useMC = UseMC.sat
        self.all_solutions = False 

import ast
from prime import PrimeOrbit, Prime
def read_orbits(filename: str) -> List[PrimeOrbit]:
    orbits : List[PrimeOrbit] = []
    with open(filename, 'r') as orb_file: 
        for line in orb_file:
            if line.startswith('= Orbit'):
                orbit = PrimeOrbit()
                size = int(next(orb_file).split(':')[1].strip())
                for i in range(size):
                    values = []
                    values.extend(next(orb_file).split(':')[1].strip())
                    prime_str =  next(orb_file).split(':')[1].strip()
                    prime = Prime(values, prime_str)
                    orbit.add_prime(prime)
                orbit.forall   = ast.literal_eval(next(orb_file).split(':')[1].strip())
                orbit.exists   = ast.literal_eval(next(orb_file).split(':')[1].strip())
                orbit.literals = ast.literal_eval(next(orb_file).split(':')[1].strip())
                qform = ' | '.join(orbit.literals)
                qform = '(' + qform + ')'
                if len(orbit.exists):
                    qform = '(exists ' + ', '.join(orbit.exists) + ' . ' + qform + ')'
                if len(orbit.forall):
                    qform = '(forall ' + ', '.join(orbit.forall) + ' . ' + qform + ')'
                orbit.quantified_form = qform
                orbit.qcost = len(orbit.forall) + len(orbit.exists) + len(orbit.literals)
                orbits.append(orbit)
    return orbits