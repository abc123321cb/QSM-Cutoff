from typing import Dict,List,Set
from pysat.solvers import Cadical153 as SatSolver 
from prime import *

class Minimizer():
    def __init__(self, orbits : List[PrimeOrbit]) -> None: 
        self.orbits  : List[PrimeOrbit] = orbits

    def _reduce(self) -> None:
        return
    
    def _addEssentials(self) -> None:
        return
    
    def _removeCovered(self) -> None:

    def solve(self) -> None:
        return

    
    