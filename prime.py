import sys
import itertools
from typing import Dict,Tuple,List,Optional,Set
from pysat.card import ITotalizer 
from pysat.solvers import Cadical153 as SatSolver 
from protocol import * 

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

class DualRailNegation():
    def __init__(self, protocol : Protocol) -> None:
        self.clauses    : List[List[int]] = [] 
        self._totalizer : ITotalizer
        self._atom_num  : int = protocol.atom_num 
        self._atom_id2vars : Dict[int, List[int]] = {}

        self._encode(protocol)
        self._set_totalizer()

    def _set_dualrail_vars(self, id: int) -> None:
        self._atom_id2vars[id] = [id*2+2, id*2+1]
        
    def _get_pos_var(self, id: int) -> int:
        return self._atom_id2vars[id][1]

    def _get_neg_var(self, id: int) -> int:
        return self._atom_id2vars[id][0]

    def _encode(self, protocol : Protocol) -> None:
        for atom_id in range(self._atom_num):
            self._set_dualrail_vars(atom_id) 
            pvar = self._get_pos_var(atom_id)
            nvar = self._get_neg_var(atom_id)
            self.clauses.append([-1*pvar, -1*nvar]) # (~pvar + ~nvar)

        for state in protocol.reachable_states:
            clause = []
            for (atom_id, value) in enumerate(state):
                if value == '0':
                    clause.append(self._get_pos_var(atom_id))
                elif value == '1':
                    clause.append(self._get_neg_var(atom_id))
            self.clauses.append(clause)

    def _set_totalizer(self) -> None:
        max_var = 2 * self._atom_num
        literals = list(range(1,max_var+1))
        self._totalizer = ITotalizer(lits=literals, ubound=self._atom_num, top_id=max_var)
        self.clauses.extend(self._totalizer.cnf.clauses)

    def assume(self, ubound: int) -> List[int]:
        return [-1*self._totalizer.rhs[ubound]]

    def block(self, values : List[str]) -> List[int]:
        var = 0
        block_clause = []
        for (atom_id, value) in enumerate(values):
            if value == '1':
                var = self._get_pos_var(atom_id)
                block_clause.append(-1*var)
            elif value == '0':
                var = self._get_neg_var(atom_id)
                block_clause.append(-1*var)
        return block_clause

    def single_rail(self, sat_model) -> List[str]:
        values = ['-']* self._atom_num
        for atom_id in range(self._atom_num):
            if self._get_pos_var(atom_id) in sat_model:
                values[atom_id] = '1'
            elif self._get_neg_var(atom_id) in sat_model:
                values[atom_id] = '0'
        return values

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