from typing import Dict,List
from pysat.solvers import Cadical153 as SatSolver 
from protocol import Protocol 
from dualrail import DualRailNegation
from util import QrmOptions 
from verbose import *

def make_key(values: List[str], protocol : Protocol) -> str:
    predicates = []
    for (atom_id, val) in enumerate(values):
        if val == '1':
            predicates.append(protocol.atom_sig[atom_id][0])
        elif val == '0':
            predicates.append('~'+protocol.atom_sig[atom_id][0])
    predicates.sort()
    return str(predicates)

class Prime():
    # static members
    count  : int = 0 
    _atoms : List[str]

    def __init__(self, values: List[str], literals ='' ) -> None:
        self.values   : List[str] = values
        self.id       : int = Prime.count
        self.literals : str = self._get_literals() if literals == '' else literals 
        Prime.count += 1

    def __str__(self) -> str:
        value_str = ''.join(self.values)
        lines  = f'{self.id} : {value_str}\n' 
        lines += f'{self.id} : {self.literals}\n'
        return lines
    
    def _get_literals(self) -> str:
        literals = []
        for (atom_id, val) in enumerate(self.values):
            if val == '1':
                literals.append(Prime._atoms[atom_id])
            elif val == '0':
                literals.append('~'+Prime._atoms[atom_id])
        literals.sort()
        return f'{str(literals)}'
        
    @staticmethod
    def setup(protocol : Protocol) -> None:
        Prime._atoms    = protocol.atoms

class PrimeOrbit():
    # static members
    count : int = 0

    def __init__(self) -> None:
        self.repr_prime : Prime      
        self.primes     : List[Prime] = []
        self.id         : int = PrimeOrbit.count   

        # quantifier inference
        self.forall      : List[str] = [] 
        self.exists      : List[str] = []
        self.literals    : List[str] = [] 
        self.quantified_form  : str = ""
        self.qcost            : int = 0
        PrimeOrbit.count += 1

    def __str__(self) -> str:
        lines  = f'= Orbit {self.id} ========================\n'
        lines += f'size : {len(self.primes)}\n'
        for prime in self.primes:
            lines += str(prime) 
        lines += f'forall : {self.forall}\n'
        lines += f'exists : {self.exists}\n'
        lines += f'literals : {self.literals}\n'
        lines += f'quantified form : {self.quantified_form}\n'
        lines += f'qcost : {self.qcost}\n'
        lines += '\n\n'
        return lines

    def add_prime(self, prime: Prime) -> None:
        if len(self.primes) == 0:
            self.repr_prime  = prime
        self.primes.append(prime)

class PrimeOrbits():
    def __init__(self, options : QrmOptions) -> None:
        self.orbits      : List[PrimeOrbit] = [] 
        self._formula    : DualRailNegation
        self._orbit_hash : Dict[str, PrimeOrbit] = {}
        self.options = options

    def __str__(self) -> str:
        lines ='' 
        for orbit in self.orbits:
            lines += str(orbit) 
        return lines

    def _make_orbit(self, values: List[str], protocol : Protocol) -> List[List[int]]:
        key = make_key(values,protocol)
        if not key in self._orbit_hash:
            orbit = PrimeOrbit()
            self._orbit_hash[key] = orbit
            self.orbits.append(orbit)
        orbit = self._orbit_hash[key]
        block_clauses = []
        for nvalues in protocol.all_permutations(values):
            clause = self._formula.block(nvalues) 
            block_clauses.append(clause)
            prime  = Prime(nvalues)
            orbit.add_prime(prime)
        return block_clauses

    def symmetry_aware_enumerate(self, protocol: Protocol) -> None:
        # setup
        Prime.setup(protocol)
        atom_num = protocol.atom_num
        # emumerate prime orbits
        self._formula = DualRailNegation(protocol)
        with SatSolver(bootstrap_with=self._formula.clauses) as sat_solver:
            for ubound in range(0,atom_num+1):
                assumptions = self._formula.assume(ubound)
                result = sat_solver.solve(assumptions)
                while (result):
                    model  = sat_solver.get_model()
                    values = self._formula.single_rail(model)
                    block_clauses  = self._make_orbit(values, protocol)
                    sat_solver.append_formula(block_clauses) 
                    result = sat_solver.solve(assumptions)
        vprint_banner(self, 'Prime Orbits', 3)
        vprint(self, str(self), 3)

    


