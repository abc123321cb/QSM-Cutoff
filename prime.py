import sys
from typing import Dict,List
from pysat.solvers import Cadical153 as SatSolver 
from protocol import Protocol 
from dualrail import DualRail
from transition_system import TransitionSystem
from finite_ivy_instantiate import FiniteIvyInstantiator
from util import QrmOptions, PrimeGen
from util import FormulaUtility as futil
from verbose import *
import json
import os

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
        self.sig         :  tuple[int, ...]

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
        # Always keep repr_prime as the lexicographically minimum prime for determinism
        if len(self.primes) == 0 or prime.literals < self.repr_prime.literals:
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
        self._formula    : DualRail
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
        key = make_key(values,protocol) # see how orbit merging is done
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
            assumptions = self._formula.assume(ubound) #adds clause that only upto ubound trues
            result = sat_solver.solve(assumptions)
            while (result):
                model  = sat_solver.get_model()
                values = self._formula.single_rail(model) # returns a list of strings like ["1","0","-","1"]
                self._make_orbit(values, protocol)
                block_clauses  = self._get_block_clauses(values, protocol) # returns in form like [[2,3,5],[2,3,6]]
                sat_solver.append_formula(block_clauses) 
                result = sat_solver.solve(assumptions)

    def _enumerate_prime_gen(self, sat_solver, protocol : Protocol):
        # a different way to solve the problem it should work but is less efficent
        result = sat_solver.solve()
        while (result):
            model  = sat_solver.get_model()
            values = self._formula.single_rail(model)
            self._make_orbit(values, protocol)
            block_clauses  = self._get_block_clauses(values, protocol)
            sat_solver.append_formula(block_clauses)
            result = sat_solver.solve()
    
    def _sort_orbits(self):
        # Sort primes within each orbit for deterministic output
        for orbit in self.orbits:
            orbit.primes.sort(key=lambda prime: prime.literals)
            # Update is_sub_repr flags: only the first prime (lexicographically minimum) should be marked
            for idx, prime in enumerate(orbit.primes):
                prime.is_sub_repr = (idx == 0)
        
        # Sort orbits by: 1) length of primes (number of literals, ascending), 2) repr_prime literals (lexicographic)
        # repr_prime is deterministically the lexicographically minimum prime in each orbit
        def prime_length(orbit):
            return sum(1 for v in orbit.repr_prime.values if v != '-')
        self.orbits.sort(key=lambda orbit: (prime_length(orbit), orbit.repr_prime.literals))
        
        # Reassign orbit IDs after sorting
        for idx, orbit in enumerate(self.orbits):
            orbit.id = idx

    def symmetry_aware_enumerate(self, protocol: Protocol) -> None:
        Prime.set_atoms(atoms_str=protocol.state_atoms)
        # emumerate prime orbits
        self._formula = DualRail(self.options, protocol)
        with SatSolver(bootstrap_with=self._formula.clauses) as sat_solver:
            if self.options.prime_gen == PrimeGen.ilp:
                self._ilp_prime_gen(sat_solver, protocol)
            elif self.options.prime_gen == PrimeGen.enumerate:
                self._enumerate_prime_gen(sat_solver, protocol)
        
        # sort orbits
        self._sort_orbits()

        # output result
        if self.options.writePrime:
            prime_filename   = self.options.instance_name + '.' + self.options.instance_suffix + '.pis'
            self._write_primes(prime_filename)
        vprint_step_banner(self.options, f'[PRIME RESULT]: Prime Orbits on [{self.options.ivy_filename}: {self.options.size_str}]', 3)
        vprint(self.options, str(self), 3)
        vprint(self.options, f'[PRIME NOTE]: number of orbits after merging: {PrimeOrbit.count}', 2)
        vprint(self.options, f'[PRIME NOTE]: number of orbits before merging: {PrimeOrbit.count + self._sub_orbit_count}', 2)
        vprint(self.options, f'[PRIME NOTE]: number of primes: {Prime.count}', 2)
        #self._formula.debug_print()

class OrbitGroup():
    def __init__(self) -> None:
        self.orbits     : List[PrimeOrbit] = []
        self.id         : int
        self.group_num  : int
        self.group_type : str

        # quantifier inference
        self.sig         :  tuple[int, ...]

        self.num_forall   = 0 
        self.num_exists   = 0 
        self.num_literals = 0 
        
        self.pattern : int
        
        self.qcost        = 0
    
        
    def __repr__(self):
        return ''.join(str(x) for x in self.sig)

class OrbitGroups():
    def __init__(self, orbits: List[PrimeOrbit], protocol : Protocol, state_vars, options : QrmOptions) -> None:
        self.groups : List[OrbitGroup] = []
        self.options = options
        self.protocol = protocol
        self.state_vars = [state_var.name for state_var in state_vars]
        self.atom_literals = [lit.rstrip('=') for lit in list(zip(*protocol.atom_sig))[0]]
        self.predicates = {k.rstrip('='): v for k, v in self.protocol.predicates.items()}

        self.sig_to_group = {}
        self.forall_count = 0
        self.exists_count = 0

        self.sig_to_forall_group_num = {}
        self.sig_to_exists_group_num = {}
        if options.read_groups:
            self.read_dict()

        self.init_groups(orbits)

        self.write_dict()
        # self.group_singletons()
        self.sort_groups()


    def _sig_to_json_key(self, sig: tuple[int, ...]) -> str:
        # JSON object keys must be strings; encode directly as concatenated digits.
        return ''.join(str(v) for v in sig)

    def _json_key_to_sig(self, key: str) -> tuple[int, ...]:
        if key == '':
            return tuple()
        # Parse key as a tuple of single-digit integers.
        return tuple(int(ch) for ch in key)


    def read_dict(self):
        json_filename = self.options.instance_name + '.groups.json'
        try:
            with open(json_filename, 'r') as file:
                data = json.load(file)
                forall_data = data.get('forall', {})
                exists_data = data.get('exists', {})
                self.sig_to_forall_group_num = {
                    self._json_key_to_sig(key): int(group_num)
                    for key, group_num in forall_data.items()
                }
                self.sig_to_exists_group_num = {
                    self._json_key_to_sig(key): int(group_num)
                    for key, group_num in exists_data.items()
                }
        except Exception as e:
            self.sig_to_forall_group_num = {}
            self.sig_to_exists_group_num = {}
    
    def write_dict(self):
        json_filename = self.options.instance_name + '.groups.json'
        with open(json_filename, 'w') as file:
            data = {
                'forall': {
                    self._sig_to_json_key(sig): group_num
                    for sig, group_num in self.sig_to_forall_group_num.items()
                },
                'exists': {
                    self._sig_to_json_key(sig): group_num
                    for sig, group_num in self.sig_to_exists_group_num.items()
                },
            }
            json.dump(data, file, indent=4)

    
    def init_groups(self, orbits: List[PrimeOrbit]):
        used_forall_group_nums = set(self.sig_to_forall_group_num.values())
        used_exists_group_nums = set(self.sig_to_exists_group_num.values())
        for orbit in orbits:
            sig = [0] * (len(self.state_vars) * 2 + 2)

            for atom_idx in range(self.protocol.state_atom_num):
                value = orbit.repr_prime.values[atom_idx]
                if value != '-':
                    assert(value == '0' or value == '1')
                    var_name = self.protocol.atom_sig[atom_idx][0].rstrip('=')
                    sig_idx = self.state_vars.index(var_name) * 2
                    if value == '0': sig_idx += 1
                    sig[sig_idx] = 1   
            
            # for var_idx, var_name in enumerate(self.state_vars):
            #     left_atom_num = self.atom_literals.index(var_name)
            #     right_atom_num = len(self.atom_literals) - 1 - self.atom_literals[::-1].index(var_name)
            #     var_bit_string = orbit.repr_prime.values[left_atom_num:right_atom_num+1]
            #     arity = len(self.protocol.atom_sig[left_atom_num])-1
            #     dimensions = [len(self.protocol.sort_constants[self.protocol.sorts.index(sort)])
            #                    for sort in self.predicates[var_name]]
            #     assert(len(dimensions)) == arity
            #     table = np.array(var_bit_string).reshape(dimensions)
                
            #     axis = 0
            #     while axis < table.ndim:
            #         # To get the 'first row' along the CURRENT axis:
            #         # We need index 0 for all dimensions EXCEPT the current one.
            #         # Example for 3D: if axis=1, we want table[0, :, 0]
                    
            #         selection = [0] * table.ndim
            #         selection[axis] = slice(None) # This targets the 'row' along this axis
            #         first_row = table[tuple(selection)]
                    
            #         if np.all(first_row == 1) or np.all(first_row == 0):
            #             # The row is uniform. We collapse PERPENDICULAR to this row.
            #             # This means we fix this axis at index 0 and keep all others.
            #             table = np.take(table, indices=0, axis=axis)
                        
            #             # Do not increment axis; the next dimension is now at this index
            #             print(f"Dimension collapsed. Remaining shape: {table.shape}")
            #         else:
            #             axis += 1
            #     for value in table.flat:
            #         if value != '-':
            #             assert(value == '0' or value == '1')
            #             sig_idx = var_idx*2
            #             if value == '0': sig_idx += 1
            #             sig[sig_idx] += 1
            #     pass
            
            sig[-2] = orbit.num_forall
            sig[-1] = orbit.num_exists

            sig = tuple(sig)
            orbit.sig = sig


            if sig not in self.sig_to_group:
                new_orbit_group = OrbitGroup()
                new_orbit_group.orbits.append(orbit)
                new_orbit_group.sig = sig
                new_orbit_group.num_forall = orbit.num_forall
                new_orbit_group.num_exists = orbit.num_exists
                new_orbit_group.num_literals = orbit.num_literals
                if (new_orbit_group.num_forall >= 1):
                    new_orbit_group.pattern = sum(sig[:-2])
                    new_orbit_group.group_type = 'F'
                    if sig in self.sig_to_forall_group_num:
                        new_orbit_group.group_num = self.sig_to_forall_group_num[sig]
                    else:
                        valid_num = False
                        while not valid_num:
                            self.forall_count += 1
                            new_orbit_group.group_num =self.forall_count
                            valid_num = new_orbit_group.group_num not in used_forall_group_nums
                        self.sig_to_forall_group_num[sig] = new_orbit_group.group_num
                    used_forall_group_nums.add(new_orbit_group.group_num)
                else:
                    assert(new_orbit_group.num_exists >= 1)
                    new_orbit_group.pattern = sum(min(1, literal) for literal in sig[:-2])
                    new_orbit_group.group_type = 'E'
                    if sig in self.sig_to_exists_group_num:
                        new_orbit_group.group_num = self.sig_to_exists_group_num[sig]
                    else:
                        valid_num = False
                        while not valid_num:
                            self.exists_count += 1
                            new_orbit_group.group_num =self.exists_count
                            valid_num = new_orbit_group.group_num not in used_exists_group_nums
                        self.sig_to_exists_group_num[sig] = new_orbit_group.group_num
                    used_exists_group_nums.add(new_orbit_group.group_num)
                new_orbit_group.qcost = orbit.qcost
                self.sig_to_group[sig] = new_orbit_group
            else:
                self.sig_to_group[sig].orbits.append(orbit)
            

    def group_singletons(self):
        # Group singletons and pin them to the beginning of the group list
        singleton_group = OrbitGroup()
        singleton_group.sig = (0,)
        singleton_group.qcost = 0
        for group in self.sig_to_group.values():
            if len(group.orbits) == 1:
                singleton_group.orbits.append(group.orbits[0])
        self.sig_to_group = {sig:group for sig, group in self.sig_to_group.items()
                              if len(group.orbits) > 1}
        self.sig_to_group[(0,)] = singleton_group

    
    def sort_groups(self):
        self.groups = list(self.sig_to_group.values())
        self.groups.sort(key=lambda group: (group.qcost, (group.num_exists>0), group.group_num))
        for idx, group in enumerate(self.groups):
            group.id = idx

