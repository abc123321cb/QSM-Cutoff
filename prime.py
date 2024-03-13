import sys
import itertools
from typing import Dict,Tuple,List,Optional,Set
from pysat.card import ITotalizer 
from pysat.solvers import Cadical153 as SatSolver 
from protocol import * 

class Prime():
    # static members
    count  : int = 0 
    _atoms    : List[str]
    _atom_sig : List[List[str]]

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
        return '{}: {}\n'.format(self.id, str(literals))

    def signature(self) -> str:
        predicates = []
        for (atom_id, val) in enumerate(self.values):
            if val == '1':
                predicates.append(Prime._atom_sig[atom_id][0])
            elif val == '0':
                predicates.append('~'+Prime._atoms[atom_id][0])
        predicates.sort()
        return str(predicates)

    @staticmethod
    def setup(protocol : Protocol) -> None:
        Prime._atoms    = protocol.atoms
        Prime._atom_sig = protocol.atom_sig

class PrimeOrbit():
    # static members
    count : int = 0
    _protocol : Protocol

    def __init__(self, prime : Prime) -> None:
        self.repr_prime : Prime       = prime
        self.primes     : List[Prime] = []
        self.id         : int         = PrimeOrbit.count 
        self.quantified_form  : str = ""
        self.qcost            : int = 0

        PrimeOrbit.count += 1
        self._finalize_orbit()

    def __str__(self) -> str:
        lines  = '= Orbit {} ========================\n'.format(self.id)
        lines += 'size: {}\n'.format(len(self.primes))
        for prime in self.primes:
            lines += str(prime) 
        lines += '\n\n'
        return lines

    def _finalize_orbit(self) -> None:
        prime_values = self.repr_prime.values
        permuted_val_list = PrimeOrbit._protocol.permute(prime_values)
        for values in permuted_val_list:
            self.primes.append(Prime(values))

    @staticmethod
    def setup(protocol : Protocol) -> None:
        PrimeOrbit._protocol = protocol

class DualRailNegation():
    def __init__(self, protocol : Protocol) -> None:
        self.clauses    : List[List[int]] = [] 
        self.max_var    : int = 0
        self._totalizer : ITotalizer
        self._atom_id2vars : Dict[int, List[int]] = {}

        self._encode(protocol)
        self._set_totalizer(protocol.atom_num)

    def _set_dualrail_vars(self, id: int) -> None:
        self._atom_id2vars[id] = [id*2+2, id*2+1]
        
    def _get_pos_var(self, id: int) -> int:
        return self._atom_id2vars[id][1]

    def _get_neg_var(self, id: int) -> int:
        return self._atom_id2vars[id][0]

    def _encode(self, protocol : Protocol) -> None:
        for atom_id in range(protocol.atom_num):
            self._set_dualrail_vars(atom_id) 
            pvar = self._get_pos_var(atom_id)
            nvar = self._get_neg_var(atom_id)
            self.clauses.append([-1*pvar, -1*nvar]) # (~pvar + ~nvar)

        self.max_var = 2*(protocol.atom_num)

        for state in protocol.reachable_states:
            clause = []
            for (atom_id, value) in enumerate(state):
                if value == '0':
                    clause.append(self._get_pos_var(atom_id))
                elif value == '1':
                    clause.append(self._get_neg_var(atom_id))
            self.clauses.append(clause)

    def _set_totalizer(self, atom_num : int) -> None:
        literals = list(range(1,self.max_var+1))
        self._totalizer = ITotalizer(lits=literals, ubound=atom_num, top_id=self.max_var)
        self.clauses.extend(self._totalizer.cnf.clauses)

    def assume(self, ubound: int) -> List[int]:
        return [-1*self._totalizer.rhs[ubound]]

    def get_single_rail(self, sat_model, atom_num : int) -> Prime:
        values = ['-']*atom_num
        for atom_id in range(atom_num):
            if self._get_pos_var(atom_id) in sat_model:
                values[atom_id] = '1'
            elif self._get_neg_var(atom_id) in sat_model:
                values[atom_id] = '0'
        return Prime(values)

    def block(self, orbit: PrimeOrbit) -> List[List[int]]:
        var = 0
        block_clauses = []
        for prime in orbit.primes:
            values = prime.values
            block_clause = []
            for (atom_id, value) in enumerate(values):
                if value == '1':
                    var = self._get_pos_var(atom_id)
                    block_clause.append(-1*var)
                elif value == '0':
                    var = self._get_neg_var(atom_id)
                    block_clause.append(-1*var)
            block_clauses.append(block_clause)
        return block_clauses

class PrimeOrbits():
    def __init__(self) -> None:
        self.orbits     : List[PrimeOrbit] = [] 
        self._formula   : DualRailNegation
        self._sig2Orbit : Dict[str, PrimeOrbit]

    def __str__(self) -> str:
        lines ='' 
        for orbit in self.orbits:
            lines += str(orbit) 
        return lines

    def add_orbit(self, prime: Prime) -> PrimeOrbit:


    def symmetry_aware_enumerate(self, protocol: Protocol) -> None:
        Prime.setup(protocol)
        PrimeOrbit.setup(protocol)
        atom_num = protocol.atom_num

        self._formula = DualRailNegation(protocol)
        # ub=0 will cover the case when the formula is empty ????
        with SatSolver(bootstrap_with=self._formula.clauses) as sat_solver:
            for ubound in range(0,atom_num+1):
                assumptions = self._formula.assume(ubound)
                result = sat_solver.solve(assumptions)
                while (result):
                    model = sat_solver.get_model()
                    prime = self._formula.get_single_rail(model, atom_num) 
                    orbit = self.add_orbit(prime)                    
                    block_clauses = self._formula.block(orbit)
                    sat_solver.append_formula(block_clauses)
                    result = sat_solver.solve(assumptions)