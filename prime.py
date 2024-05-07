import sys
from typing import Dict,List
from pysat.solvers import Cadical153 as SatSolver 
from frontend.utils import count_quantifiers_and_literals, pretty_print_str
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

    def __init__(self, values: List[str], is_sub_repr = False) -> None:
        self.values   : List[str] = values
        self.is_sub_repr = is_sub_repr
        self.id       : int = Prime.count
        self.literals : str = self._get_literals() 
        Prime.count += 1

    def __str__(self) -> str:
        value_str = ''.join(self.values)
        annotation = '(*)' if self.is_sub_repr else '   '
        lines  = f'{self.id} {annotation} : {value_str}\n' 
        lines += f'{self.id}     : {self.literals}\n'
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
        self.num_suborbits = 0

        # quantifier inference
        self.num_forall   = 0 
        self.num_exists   = 0 
        self.num_literals = 0 
        self.qcost        = 0
        self.quantified_form  : str = ''
        PrimeOrbit.count += 1

    def __str__(self) -> str:
        lines  = f'--- Orbit {self.id} ----------------\n'
        lines += f'size : {len(self.primes)}\n'
        lines += f'num_suborbits: {self.num_suborbits}\n'
        for prime in self.primes:
            lines += str(prime) 
        lines += f'num_forall :   {self.num_forall}\n'
        lines += f'num_exists :   {self.num_exists}\n'
        lines += f'num_literals : {self.num_literals}\n'
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
        is_sub_repr = True
        orbit.num_suborbits += 1
        for nvalues in protocol.all_permutations(values):
            clause = self._formula.block(nvalues) 
            block_clauses.append(clause)
            prime  = Prime(nvalues, is_sub_repr)
            is_sub_repr = False
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


    def quantifier_inference(self, atoms, tran_sys, options) -> None:
        from qinference import QInference
        QInference.setup(atoms, tran_sys)
        for orbit in self.orbits:
            qInfr = QInference(orbit, options)
            if orbit.num_suborbits > 1:
                print('Cannot perform quantifier inference for suborbits')
                # sys.exit(1)
            qclauses = qInfr.infer_quantifier()
            assert(len(qclauses) == 1)
            qclause   = qclauses[0]
            num_forall, num_exists, num_literals = count_quantifiers_and_literals(qclause)
            orbit.num_forall    = num_forall
            orbit.num_exists    = num_exists
            orbit.num_literals  = num_literals
            orbit.qcost         = num_forall + num_exists + num_literals
            orbit.quantified_form = pretty_print_str(qclause)
        vprint_banner(self, 'Quantified Prime Orbits', 3)
        vprint(self, str(self), 3)

