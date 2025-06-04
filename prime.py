import sys
from typing import Dict,List
from pysat.solvers import Cadical153 as SatSolver 
from protocol import Protocol 
from dualrail import DualRailNegation
from transition_system import TransitionSystem
from finite_ivy_instantiate import FiniteIvyInstantiator
from util import QrmOptions, PrimeGen
from util import FormulaUtility as futil
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
    count      : int = 0 
    _atoms_str   = []

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
                literals.append(Prime._atoms_str[atom_id])
            elif val == '0':
                literals.append('~'+Prime._atoms_str[atom_id])
        literals.sort()
        return f'{str(literals)}'

    @staticmethod
    def set_atoms(atoms_str) -> None:
        Prime._atoms_str  = atoms_str

    def reset() -> None:
        Prime.count = 0
        Prime._atoms_str   = []

class PrimeOrbit():
    # static members
    count : int = 0

    def __init__(self) -> None:
        self.repr_prime : Prime      
        self.primes     : List[Prime] = []
        self.id         : int = PrimeOrbit.count   
        self.num_suborbits = 0
        self.suborbit_repr_primes : List[Prime] = []

        # quantifier inference
        self.num_forall   = 0 
        self.num_exists   = 0 
        self.num_literals = 0 
        self.qcost        = 0
        self.quantified_form  = None # first-order formula
        PrimeOrbit.count += 1

    def __str__(self) -> str:
        lines  = f'\n=== Prime Orbit {self.id} =====================\n'
        lines += f'size : {len(self.primes)}\n'
        lines += f'num_suborbits: {self.num_suborbits}\n'
        for prime in self.primes:
            lines += str(prime) 
        lines += f'num_forall :   {self.num_forall}\n'
        lines += f'num_exists :   {self.num_exists}\n'
        lines += f'num_literals : {self.num_literals}\n'
        lines += f'quantified form : {self.quantified_form}\n'
        lines += f'qcost : {self.qcost}\n'
        lines += '\n'
        return lines

    def add_prime(self, prime: Prime) -> None:
        if len(self.primes) == 0:
            self.repr_prime  = prime
        self.primes.append(prime)
        if prime.is_sub_repr:
            self.suborbit_repr_primes.append(prime)

    def set_quantifier_inference_result(self, qclause):
        num_forall, num_exists, num_literals = futil.count_quantifiers_and_literals(qclause)
        self.num_forall      = num_forall
        self.num_exists      = num_exists
        self.num_literals    = num_literals
        self.qcost           = num_forall + num_exists + num_literals
        self.qclause         = qclause
        self.quantified_form = qclause

    @staticmethod
    def reset() -> None:
        PrimeOrbit.count = 0

class PrimeOrbits():
    def __init__(self, options : QrmOptions) -> None:
        self.orbits      : List[PrimeOrbit] = [] 
        self._formula    : DualRailNegation
        self._orbit_hash : Dict[str, PrimeOrbit] = {}
        self._sub_orbit_count = 0 
        self.options = options
        Prime.reset()
        PrimeOrbit.reset()

    def __str__(self) -> str:
        lines ='' 
        for orbit in self.orbits:
            lines += str(orbit) 
        return lines

    def _write_primes(self, filename) -> None:
        outF = open(filename, "w")
        outF.write(str(self)+'\n')
        outF.close()

    def _make_orbit(self, values: List[str], protocol : Protocol) -> None:
        key = make_key(values,protocol)
        if key in self._orbit_hash and self.options.merge_suborbits:
            self._sub_orbit_count += 1
        if not key in self._orbit_hash or not self.options.merge_suborbits:
            orbit = PrimeOrbit()
            self._orbit_hash[key] = orbit
            self.orbits.append(orbit)
        orbit = self._orbit_hash[key]
        orbit.num_suborbits += 1
        is_sub_repr = True
        for nvalues in protocol.all_permutations(values):
            prime  = Prime(nvalues, is_sub_repr)
            is_sub_repr = False
            orbit.add_prime(prime)

    def _get_block_clauses(self, values: List[str], protocol: Protocol) -> List[List[int]]:
        block_clauses = []
        for nvalues in protocol.all_permutations(values):
            clause = self._formula.block(nvalues) 
            block_clauses.append(clause)
        return block_clauses

    def _ilp_prime_gen(self, sat_solver, protocol : Protocol):
        for ubound in range(0,protocol.state_atom_num+1):
            assumptions = self._formula.assume(ubound)
            result = sat_solver.solve(assumptions)
            while (result):
                model  = sat_solver.get_model()
                values = self._formula.single_rail(model)
                self._make_orbit(values, protocol)
                block_clauses  = self._get_block_clauses(values, protocol)
                sat_solver.append_formula(block_clauses) 
                result = sat_solver.solve(assumptions)

    def _enumerate_prime_gen(self, sat_solver, protocol : Protocol):
        result = sat_solver.solve()
        while (result):
            model  = sat_solver.get_model()
            values = self._formula.single_rail(model)
            self._make_orbit(values, protocol)
            block_clauses  = self._get_block_clauses(values, protocol)
            sat_solver.append_formula(block_clauses) 
            result = sat_solver.solve() 

    def symmetry_aware_enumerate(self, protocol: Protocol) -> None:
        Prime.set_atoms(atoms_str=protocol.state_atoms)
        # emumerate prime orbits
        self._formula = DualRailNegation(self.options, protocol)
        with SatSolver(bootstrap_with=self._formula.clauses) as sat_solver:
            if self.options.prime_gen == PrimeGen.ilp:
                self._ilp_prime_gen(sat_solver, protocol)
            elif self.options.prime_gen == PrimeGen.enumerate:
                self._enumerate_prime_gen(sat_solver, protocol)

        # output result
        if self.options.writePrime:
            prime_filename   = self.options.instance_name + '.' + self.options.instance_suffix + '.pis'
            self._write_primes(prime_filename)
        vprint_step_banner(self.options, f'[PRIME RESULT]: Prime Orbits on [{self.options.ivy_filename}: {self.options.size_str}]', 3)
        vprint(self.options, str(self), 3)
        vprint(self.options, f'[PRIME NOTE]: number of orbits after merging: {PrimeOrbit.count}', 2)
        vprint(self.options, f'[PRIME NOTE]: number of orbits before merging: {PrimeOrbit.count + self._sub_orbit_count}', 2)
        vprint(self.options, f'[PRIME NOTE]: number of primes: {Prime.count}', 2)

