from typing import List
from pysat.solvers import Glucose4 as SatCounter 
from pysat.solvers import Cadical153 as SatSolver
from pysat.allies.approxmc import Counter
from ivy import ivy_logic as il
from ivy import logic as lg
from transition_system import TransitionSystem
from finite_ivy_instantiate import FiniteIvyInstantiator
from prime import *
from util import UseMC

class CoverConstraints():
    def __init__(self, tran_sys : TransitionSystem, instantiator : FiniteIvyInstantiator, orbits : List[PrimeOrbit], useMC : UseMC) -> None:
        self.tran_sys       = tran_sys
        self.instantiator   = instantiator
        self.sat_solver     = SatSolver() 
        self.sat_counter    = SatCounter()
        self.approx_counter = None 
        self.useMC          = useMC
        self.top_var        = 0
        self.symbol2var_num = {}
        self.atom_vars : List[int] = []
        self.axiom_vars: List[int] = []
        self.orbit_vars: List[int] = []
        self.root_clause    = [] # axiom, definition
        self.coverage  : List[int] = [-1]*len(orbits) 
        self.clauses       = []
        
        self._init_vars(orbits)
        self._init_solver(orbits)

    def new_var(self) -> int:
        self.top_var += 1
        return self.top_var

    def tseitin_encode(self, symbol) -> int:
        if str(symbol) in self.symbol2var_num:
            return self.symbol2var_num[str(symbol)]
        else:
            if isinstance(symbol, il.Not):
                return -1*self.tseitin_encode(symbol.args[0])
            assert(len(symbol.args) > 1)
            symbol_var = self.new_var()
            args = [self.tseitin_encode(arg) for arg in symbol.args]
            clauses = []
            if isinstance(symbol, il.And):
                # y = arg1 & arg2
                # (~y + arg1) & (~y + arg2) & (y + ~arg1 + ~arg2)
                clauses.append([symbol_var] + [-1*arg for arg in args])
                for arg in args:
                    clauses.append([-1*symbol_var, arg])
            elif isinstance(symbol, il.Or):
                # y = arg1 | arg2
                # (y + ~arg1) & (y + ~arg2) & (~y + arg1 + arg2)
                clauses.append([-1*symbol_var] + args)
                for arg in args:
                    clauses.append([symbol_var, -1*arg])
            elif isinstance(symbol, il.Implies):
                # y = arg1 -> arg2 = ~arg1 | arg2
                # (y + arg1) & (y + ~arg2) & (~y + ~arg1 + arg2)
                assert(len(args) == 2)
                args[0] = -1*args[0]
                clauses.append([-1*symbol_var, -1*args[0], args[1]])
                clauses.append([symbol_var,    args[0]])
                clauses.append([symbol_var, -1*args[1]])
            elif isinstance(symbol, lg.Eq):
                # y = arg1 <-> arg2 = (~arg1 + arg2)(arg1 + ~arg2)
                # (~y + ~arg1 + arg2) & (~y + arg1 + ~arg2)
                # (y + ~arg1 + ~arg2) & (y + arg1 + arg2 )
                clauses.append([-1*symbol_var, -1*args[0],    args[1]])
                clauses.append([-1*symbol_var,    args[0], -1*args[1]])
                clauses.append([symbol_var, -1*args[0], -1*args[1]])
                clauses.append([symbol_var,    args[0],    args[1]])
            else:
                assert(0)
            for clause in clauses:
                self.sat_solver.add_clause(clause)
                self.sat_counter.add_clause(clause)
                self.clauses.append(clause)
            return symbol_var

    def get_prime_literals(self, prime : Prime, negate=False) -> List[int]:
        literals = []
        for (id, val) in enumerate(prime.values):
            lit = self.atom_vars[id]
            if (val == '1' and negate) or (val == '0' and not negate):
                literals.append(-1*lit) 
            elif (val == '1' and not negate) or (val == '0' and negate):
                literals.append(lit)
        return literals

    def _init_vars(self, orbits : List[PrimeOrbit]) -> None:
        for atom in self.instantiator.protocol_atoms:
            atom_var = self.new_var()
            self.atom_vars.append(atom_var)
            self.symbol2var_num[atom] = atom_var 
        for axiom in self.instantiator.protocol_axioms:
            axiom_var = self.new_var()
            self.axiom_vars.append(axiom_var)
            self.symbol2var_num[axiom] = axiom_var 
        for orbit_id in range(len(orbits)):
            orbit_var = self.new_var()
            self.orbit_vars.append(orbit_var)

    def _init_axioms_formula(self) -> None:
        axioms_str = set(self.instantiator.dep_axioms_str)
        for axiom_str in self.instantiator.protocol_axioms:
            axiom_var = self.symbol2var_num[axiom_str]
            if axiom_str in axioms_str:  # member(n,q) in axioms_str
                self.root_clause.append(-1*axiom_var)
            else:                        # ~member(n,q) not in axioms_str
                self.root_clause.append(axiom_var)

    def _init_definitions_formula(self) -> None:
        for def_lhs, def_rhs in self.instantiator.instantiated_def_map.items():
            def_equal_symbol = il.Equals(def_lhs, def_rhs)
            def_equal_var    = self.tseitin_encode(def_equal_symbol) 
            self.root_clause.append(-1*def_equal_var)

    def _init_orbit_selection_formula(self, orbits : List[PrimeOrbit]) -> None:
        # Eq (10) in FMCAD paper
        for (orbit_id, orbit) in enumerate(orbits):
            orbit_var = self.orbit_vars[orbit_id]
            for prime in orbit.primes:
                clause = self.get_prime_literals(prime, negate=True) 
                clause.append(-1*orbit_var)
                self.clauses.append(clause)

    def _push_clauses_into_solver(self) -> None:
        self.sat_solver.add_clause(self.root_clause)
        self.sat_counter.add_clause(self.root_clause)
        for clause in self.clauses:
            self.sat_solver.add_clause(clause)
            self.sat_counter.add_clause(clause)

    def _init_solver(self, orbits : List[PrimeOrbit]) -> None:
        self._init_axioms_formula()
        self._init_definitions_formula()
        self._init_orbit_selection_formula(orbits)
        self._push_clauses_into_solver()

    def _count_atom_var(self, assigned) -> int:
        count = 0
        for lit in assigned:
            var = abs(lit)
            if var <= len(self.atom_vars):
                count +=1
        return count

    def reset_coverage(self) -> None:
        for (i, _) in enumerate(self.coverage):
            self.coverage[i] = -1

    def is_essential(self, orbit : PrimeOrbit, pending, solution) -> bool:
        result = False
        for repr_prime in orbit.suborbit_repr_primes:
            assumptions = self.get_prime_literals(repr_prime)
            assumptions += [self.orbit_vars[i] for i in pending  if i != orbit.id]
            assumptions += [self.orbit_vars[i] for i in solution if i != orbit.id]
            result = self.sat_solver.solve(assumptions)
            if result:
                break
        return result

    def get_coverage(self, orbit : PrimeOrbit, solution) -> int:
        for repr_prime in orbit.suborbit_repr_primes:
            assumptions = self.get_prime_literals(repr_prime)
            assumptions += [self.orbit_vars[i] for i in solution]
            result = self.sat_counter.solve(assumptions)
            self.coverage[orbit.id] = 0
            if result:
                result, assigned = self.sat_counter.propagate(assumptions)
                atom_count = self._count_atom_var(assigned)
                len_assigned = len(self.atom_vars) +1 - atom_count

                if self.useMC == UseMC.sat:
                    self.coverage[orbit.id] += len_assigned 
                else:
                    cnf  = self.clauses                                                                    
                    cnf += [[a] for a in assumptions]
                    self.approx_counter = Counter(formula=cnf, epsilon=0.50, delta=0.50)
                    result = self.approx_counter.count()
                    self.coverage[orbit.id] += max(len_assigned, result)
                    self.approx_counter.delete()
                    self.approx_counter = None
            else:
                self.coverage[orbit.id] += 0 # covered by existing solution 
        return self.coverage[orbit.id] 