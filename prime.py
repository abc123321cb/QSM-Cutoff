from typing import Dict,List
from pysat.card import ITotalizer 
from pysat.solvers import Cadical153 as SatSolver 
from protocol import Protocol 
from dualrail import DualRailNegation

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
    _atoms    : List[str]

    def __init__(self, values: List[str]) -> None:
        self.values : List[str] = values
        self.id     : int = Prime.count
        Prime.count += 1

    def __str__(self) -> str:
        literals = []
        for (atom_id, val) in enumerate(self.values):
            if val == '1':
                literals.append(Prime._atoms[atom_id])
            elif val == '0':
                literals.append('~'+Prime._atoms[atom_id])
        literals.sort()
        return f'{self.id} : {str(literals)}\n' 

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
        self.quantified_form  : str = ""
        self.qcost            : int = 0
        PrimeOrbit.count += 1

    def __str__(self) -> str:
        lines  = f'= Orbit {self.id} ========================\n'
        lines += f'size: {len(self.primes)}\n'
        for prime in self.primes:
            lines += str(prime) 
        lines += '\n\n'
        return lines

    def add_prime(self, prime: Prime):
        if len(self.primes) == 0:
            self.repr_prime  = prime
        self.primes.append(prime)

class PrimeOrbits():
    def __init__(self) -> None:
        self.orbits      : List[PrimeOrbit] = [] 
        self._formula    : DualRailNegation
        self._orbit_hash : Dict[str, PrimeOrbit] = {}

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
        for new_values in protocol.permute(values):
            clause = self._formula.block(new_values) 
            block_clauses.append(clause)
            prime  = Prime(new_values)
            orbit.add_prime(prime)
        return block_clauses

    def symmetry_aware_enumerate(self, protocol: Protocol) -> None:
        Prime.setup(protocol)
        atom_num = protocol.atom_num

        self._formula = DualRailNegation(protocol)
        # ub=0 will cover the case when the formula is empty 
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