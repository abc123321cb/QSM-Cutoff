import sys
from typing import Dict,List
from pysat.solvers import Cadical153 as SatSolver 
from frontend.utils import count_quantifiers_and_literals
from protocol import Protocol 
from dualrail import DualRailNegation
from util import QrmOptions
from util import FormulaPrinter as printer
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
    def setup_atoms(protocol : Protocol) -> None:
        Prime._atoms    = protocol.atoms

    def reset() -> None:
        Prime.count = 0

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
        self.quantified_form  : str = ''
        PrimeOrbit.count += 1

    def __str__(self) -> str:
        lines  = f'\n=== Orbit {self.id} =====================\n'
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
        num_forall, num_exists, num_literals = count_quantifiers_and_literals(qclause)
        self.num_forall      = num_forall
        self.num_exists      = num_exists
        self.num_literals    = num_literals
        self.qcost           = num_forall + num_exists + num_literals
        self.qclause         = qclause
        self.quantified_form = printer.pretty_print_str(qclause)

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

    def _make_orbit(self, values: List[str], protocol : Protocol) -> List[List[int]]:
        key = make_key(values,protocol)
        if key in self._orbit_hash:
            self._sub_orbit_count += 1
        if not key in self._orbit_hash or not self.options.merge_suborbits:
            orbit = PrimeOrbit()
            self._orbit_hash[key] = orbit
            self.orbits.append(orbit)
        orbit = self._orbit_hash[key]
        orbit.num_suborbits += 1
        block_clauses = []
        is_sub_repr = True
        for nvalues in protocol.all_permutations(values):
            clause = self._formula.block(nvalues) 
            block_clauses.append(clause)
            prime  = Prime(nvalues, is_sub_repr)
            is_sub_repr = False
            orbit.add_prime(prime)
        return block_clauses

    def symmetry_aware_enumerate(self, protocol: Protocol) -> None:
        # setup
        Prime.setup_atoms(protocol)
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
        # output result
        if self.options.writePrime:
            prime_filename   = self.options.instance_name + '.' + self.options.instance_suffix + '.pis'
            self._write_primes(prime_filename)
        vprint_step_banner(self.options, f'[PRIME RESULT]: Prime Orbits on [{self.options.instance_name}: {self.options.size_str}]', 3)
        vprint(self.options, str(self), 3)
        vprint(self.options, f'[PRIME NOTE]: number of orbits: {PrimeOrbit.count}', 2)
        vprint(self.options, f'[PRIME NOTE]: number of suborbits: {self._sub_orbit_count}', 2)
        vprint(self.options, f'[PRIME NOTE]: number of primes: {Prime.count}', 2)

    def quantifier_inference(self, atoms, tran_sys) -> None:
        from qinference import QInference
        from merge import Merger
        Merger.setup(atoms, tran_sys)
        QInference.setup(atoms, tran_sys)
        vprint_title(self.options, 'quantifier_inference', 5)
        for orbit in self.orbits:
            vprint(self.options, str(orbit), 5)
            repr_primes = orbit.suborbit_repr_primes
            qclause = None
            if len(repr_primes) == 1:
                is_orbit_size_1 = (len(orbit.primes) == 1)
                qInfr = QInference(repr_primes[0], self.options, is_orbit_size_1)
                qclause = qInfr.infer_quantifier() 
            else:
                merger  = Merger(self.options, repr_primes)
                qclause = merger.merge()
            orbit.set_quantifier_inference_result(qclause)
        # output result
        if self.options.writeQI:
            prime_filename   = self.options.instance_name + '.' + self.options.instance_suffix + '.qpis'
            self._write_primes(prime_filename)
        vprint_step_banner(self.options, f'[QI RESULT]: Quantified Prime Orbits on [{self.options.instance_name}: {self.options.size_str}]', 3)
        vprint(self.options, str(self), 3)

