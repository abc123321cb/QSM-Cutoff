import sys
from typing import Dict, List, Any, Optional
from pysat.solvers import Cadical153 as SatSolver 
from protocol import Protocol 
from dualrail import DualRail
from collections import Counter, defaultdict
from transition_system import TransitionSystem
from finite_ivy_instantiate import FiniteIvyInstantiator
from util import QrmOptions, PrimeGen
from util import FormulaUtility as futil
from verbose import *
import re

def make_key(values: List[str], protocol : Protocol) -> str:
    predicates = []
    for (atom_id, val) in enumerate(values):
        if val == '1':
            predicates.append(protocol.atom_sig[atom_id][0])
        elif val == '0':
            predicates.append('~'+protocol.atom_sig[atom_id][0])
    predicates.sort()
    return str(predicates)

# this is bad code only for this one protocol it needs to be genrelized
_ORBIT_GROUP_DIGIT_RE = re.compile(r"\d+")


def get_orbit_group_key(obj, protocol: Protocol | None = None):
    """Return a coarse (protocol-specific) key for grouping prime orbits.

    This is currently tailored to protocols like `distributed_lock` where
    constant names carry indices (e.g. NODE0/NODE1, epoch2/epoch3, ...).

    The key is built by:
    - taking the orbit representative's literals (or an explicit literal list)
    - stripping all digits from predicate/constant names
    - returning a hashable multiset of the resulting normalized signatures

    Args:
        obj: `PrimeOrbit`, `Prime`, or `List[str]` of literals.
        protocol: optional, used to normalize via `protocol.atom_sig` when
            available. If omitted, falls back to string-based normalization.

    Returns:
        A hashable multiset key (frozenset of (term, count) pairs).
    """

    def strip_digits(text: str) -> str:
        return _ORBIT_GROUP_DIGIT_RE.sub("", text)

    # Accept PrimeOrbit / Prime / raw literal list
    if hasattr(obj, "repr_prime") and hasattr(obj.repr_prime, "literals_list"):
        literals = obj.repr_prime.literals_list
    elif hasattr(obj, "literals_list"):
        literals = obj.literals_list
    else:
        literals = obj

    if not isinstance(literals, list):
        raise TypeError("get_orbit_group_key expects a PrimeOrbit, Prime, or List[str]")

    terms = []
    for lit in literals:
        if not isinstance(lit, str):
            raise TypeError("get_orbit_group_key expects a list of literal strings")

        sign = '-'
        atom = lit
        if lit.startswith('~'):
            atom = lit[1:]
        else:
            sign = '+'

        # Prefer structured normalization via atom_sig when possible
        if protocol is not None and atom in protocol.atom_Name2Id:
            atom_id = protocol.atom_Name2Id[atom]
            sig = protocol.atom_sig[atom_id]
            pred = strip_digits(sig[0])
            args = tuple(strip_digits(a) for a in sig[1:])
            terms.append((sign, pred, args))
        else:
            # Fall back to string-level normalization
            terms.append((sign, strip_digits(atom)))

    return frozenset(Counter(terms).items())

class Prime():
    # static members
    count      : int = 0 
    _atoms_str   = []

    def __init__(self, values: List[str], is_sub_repr = False) -> None:
        self.values   : List[str] = values
        self.is_sub_repr = is_sub_repr
        self.id       : int = Prime.count
        self.literals_list = []
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
        self.literals_list = literals
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

        # orbit-grouping (coarser than symmetry orbit)
        self.group_key: Any = None
        self.group_id: Optional[int] = None
        self.group_size: Optional[int] = None

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

    def uncurry_quantified_form(self, old_protocol: Protocol, new_protocol: Protocol) -> None:
        if self.quantified_form is not None:
            for atom_id in old_protocol.curry_map:
                curried_atom, curried_pred, curried_args, atom_sig = old_protocol.curry_map[atom_id]
                print("old debug: ")
                for i in old_protocol.state_atoms:
                    print(i)
                print("new debug: ")
                for i in new_protocol.state_atoms:
                    print(i)





        


    @staticmethod
    def reset() -> None:
        PrimeOrbit.count = 0

class PrimeOrbits():
    def __init__(self, options : QrmOptions) -> None:
        self.orbits      : List[PrimeOrbit] = [] 
        self._formula    : DualRail
        self._orbit_hash : Dict[str, PrimeOrbit] = {}
        self._sub_orbit_count = 0
        # orbit groups (computed on demand)
        self.orbit_groups_by_value: Dict[Any, List[PrimeOrbit]] = {}
        self.orbit_groups_list: List[List[PrimeOrbit]] = []
        self.options = options
        Prime.reset()
        PrimeOrbit.reset()

    def __str__(self) -> str:
        lines ='' 
        for orbit in self.orbits:
            lines += str(orbit) 
        return lines

    def format_orbits_grouped_by_value(self, protocol: Protocol | None = None) -> str:
        """Pretty-print orbits grouped by `get_orbit_group_key`.

        This is intentionally separate from `__str__` so you can switch between
        the old printing behavior and this grouped view.

        Args:
            protocol: Optional protocol to enable signature-based normalization
                in `get_orbit_group_key`.
        """
        self.build_orbit_groups_by_value(protocol=protocol)
        groups = self.orbit_groups_by_value

        # deterministic ordering: larger groups first, then key string
        sorted_groups = sorted(groups.items(), key=lambda kv: (-len(kv[1]), str(kv[0])))

        out_lines: List[str] = []
        out_lines.append(f"number of orbit groups: {len(sorted_groups)}")
        for group_id, (key, orbits) in enumerate(sorted_groups):
            orbits_sorted = sorted(orbits, key=lambda o: o.id)
            out_lines.append(
                f"\n================= Orbit_group {group_id} size {len(orbits_sorted)} ================="
            )
            out_lines.append(f"value: {key}")
            for orbit in orbits_sorted:
                out_lines.append(f"[orbit {orbit.id}] value: {orbit.group_key}")
                out_lines.append(str(orbit).rstrip())
        out_lines.append("")
        return "\n".join(out_lines)

    def print_orbits_grouped_by_value(self, protocol: Protocol | None = None) -> None:
        print(self.format_orbits_grouped_by_value(protocol=protocol), end="")

    def build_orbit_groups_by_value(self, protocol: Protocol | None = None) -> Dict[Any, List[PrimeOrbit]]:
        """Compute and cache orbit groups, and store membership on each PrimeOrbit.

        After calling this:
        - `self.orbit_groups_by_value[key]` gives the list of orbits in that group
        - each `PrimeOrbit` has `.group_key`, `.group_id`, `.group_size` populated
        - `self.orbit_groups_list` stores the groups in a deterministic order
        """
        groups: Dict[Any, List[PrimeOrbit]] = defaultdict(list)
        for orbit in self.orbits:
            key = get_orbit_group_key(orbit, protocol=protocol)
            orbit.group_key = key
            groups[key].append(orbit)

        # deterministic ordering: larger groups first, then key string
        ordered = sorted(groups.items(), key=lambda kv: (-len(kv[1]), str(kv[0])))
        self.orbit_groups_by_value = {k: v for (k, v) in ordered}
        self.orbit_groups_list = [v for (_, v) in ordered]

        # store group ids and sizes on each orbit
        for group_id, (_, orbits) in enumerate(ordered):
            group_size = len(orbits)
            for orbit in orbits:
                orbit.group_id = group_id
                orbit.group_size = group_size

        return self.orbit_groups_by_value

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

    def symmetry_aware_enumerate(self, protocol: Protocol) -> None:
        Prime.set_atoms(atoms_str=protocol.state_atoms)
        # emumerate prime orbits
        self._formula = DualRail(self.options, protocol)
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
        #self._formula.debug_print()

    def remove_num(self, l):
        newl = []
        for i in l:
            out = re.sub(r"\d+", "", i)
            newl.append(out)
        return newl

    def uncurry_orbits(self, old_protocol: Protocol, new_protocol: Protocol) -> None:
        return # stop printing
        vprint(self.options, f'[UNCURRY]: Find super-orbits',3)
        print("debug state atoms: ", len(self.orbits[-1].repr_prime.literals_list))
        print(self.orbits[0])
        l = defaultdict(list)
        for j, orbit in enumerate(self.orbits):
            c = Counter(self.remove_num(orbit.repr_prime.literals_list))
            key = frozenset(c.items())  # hashable key
            l[key].append(j)
        
        print("debug: ", l)
        print("Fancy formatting")
        print("Basic info")
        print(f'number of new orbits: {len(l.keys())}')
        count = [0] * 100
        for v in l.values():
            count[len(v)-1]+=1

        for i,val in enumerate(count):
            if(val != 0):
                print(f"number of orbit groups with {i+1} orbits: {val}")


        for i, values in enumerate(l.values()):
            print("================= Orbit_group " + str(i) +  " size " + str(len(values)) + " =================")
            for j in values:
                print(self.orbits[j], end="")



        # for orbit in self.orbits:
        #     orbit.uncurry_quantified_form(old_protocol, new_protocol)