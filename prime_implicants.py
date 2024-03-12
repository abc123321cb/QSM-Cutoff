import sys
import itertools
from typing import Dict,Tuple,List,Optional,Set
from protocol import Protocol 

class Pi():
    count : int = 0 
    @classmethod
    def __init__(self, cube: str) -> None:
        self.cube : str = cube 
        self.id   : int = count
        count += 1

class PiOrbit():
    count : int = 0
    
    @classmethod
    def __init__(self, cube : str) -> None:
        self.repr_pi : Pi        = Pi(cube) 
        self.orbit   : List[Pi]  = [repr_pi]
        self.id      : int       = count 
        count += 1

        self.quantified_form  : str = ""
        self.qcost            : int = 0

    def finalize_orbit(self, orbit)  -> None:
        for cube in orbit:
            new_pi = Pi(cube)
            self.orbit.append(new_pi)

class PrimeImplicants():
    def __init__(self) -> None:
        self.orbits : List[PiOrbit] = {}
        
    def generate(self, protocol: Protocol) -> None:
        return