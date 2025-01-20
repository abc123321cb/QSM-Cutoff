import os
from typing import List
from pysat.solvers import Glucose4 as SatCounter 
from pysat.solvers import Cadical153 as SatSolver
from pysat.allies.approxmc import Counter
from ivy import ivy_logic as il
from ivy import logic as lg
from transition_system import TransitionSystem
from finite_ivy_instantiate import FiniteIvyInstantiator
from prime import *
from util import UseMC, ForwardMode

class CoverConstraints():
    def __init__(self, options: QrmOptions, tran_sys : TransitionSystem, instantiator : FiniteIvyInstantiator, orbits : List[PrimeOrbit], useMC : UseMC) -> None:
        self.options           = options
        self.tran_sys          = tran_sys
        self.instantiator      = instantiator
        self.sat_solver        = SatSolver() 
        if useMC == UseMC.sat:
            self.sat_counter   = SatCounter()
        self.def_prime_checker = SatSolver()
        self.min_checker       = None   
        self.useMC             = useMC
        self.top_var           = 0
        self.root_top_var      = 0
        self.symbol2var_num    = {}
        self.atom_vars : List[int] = []
        self.orbit_vars: List[List[int]] = [] # orbit_id -> [suborbit_var1, suborbit_var2, ...]
        
        # axiom, definition
        self.root_assume_clauses   = [] 
        self.root_tseitin_clauses  = [] # axiom, definition
        # when reach is computed with BDD-based symbolic image computation
        self.rmin_var   = 0
        self.reach_var  = 0
        # min_check or qinfer_check
        self.instantiated_orbit_assume_clauses    = [] 
        self.instantiated_orbit_tseitin_clauses   = [] 
        self.clauses               = []
        self.coverage  : List[int] = [-1]*len(orbits) 
        
        self._init_vars(orbits)
        self._init_solvers(orbits)

    def new_var(self) -> int:
        self.top_var += 1
        return self.top_var

    def _get_canonical_equal_term(self, symbol):
        if str(symbol) in self.symbol2var_num:
            return symbol
        symbol1 = il.Equals(symbol.args[1], symbol.args[0])
        if str(symbol1) in self.symbol2var_num:
            return symbol1
        a = symbol.args[0]
        b = symbol.args[1]
        a_eqs = {} 
        b_eqs = {}
        for atom in self.instantiator.protocol_atoms_fmlas:
            if il.is_eq(atom):
                if a == atom.args[0]:
                    a_eqs[str(atom.args[1])] = atom
                elif a == atom.args[1]:
                    a_eqs[str(atom.args[0])] = atom
                elif b == atom.args[0]:
                    b_eqs[str(atom.args[1])] = atom
                elif b == atom.args[1]:
                    b_eqs[str(atom.args[0])] = atom
        assert(len(a_eqs) == len(b_eqs))
        eq_terms = []
        for other_arg, a_eq in a_eqs.items():
            assert(other_arg in b_eqs)
            b_eq = b_eqs[other_arg]
            eq_terms.append(il.And(*[a_eq, b_eq]))
        return il.Or(*eq_terms)

    def tseitin_encode(self, symbol, is_root=True) -> int:
        # e.g. a = b
        if isinstance(symbol, lg.Eq) and il.is_enumerated(symbol.args[0]) and il.is_enumerated(symbol.args[1]):
            symbol = self._get_canonical_equal_term(symbol)

        if str(symbol) in self.symbol2var_num:
            return self.symbol2var_num[str(symbol)]
        else:
            if isinstance(symbol, il.Not):
                return -1*self.tseitin_encode(symbol.args[0], is_root)
            if len(symbol.args) == 1:
                assert( isinstance(symbol, il.And) or isinstance(symbol, il.Or) )
                return self.tseitin_encode(symbol.args[0], is_root)
            assert(len(symbol.args) > 1) 
            symbol_var = self.new_var()
            args = [self.tseitin_encode(arg, is_root) for arg in symbol.args]
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
                clauses.append([-1*symbol_var, -1*args[0], args[1]])
                clauses.append([symbol_var,    args[0]])
                clauses.append([symbol_var, -1*args[1]])
            elif isinstance(symbol, lg.Eq):
                # y = arg1 <-> arg2 = (~arg1 + arg2)(arg1 + ~arg2)
                # (~y + ~arg1 + arg2) & (~y + arg1 + ~arg2)
                # (y + ~arg1 + ~arg2) & (y + arg1 + arg2 )
                assert(len(args) == 2)
                clauses.append([-1*symbol_var, -1*args[0],    args[1]])
                clauses.append([-1*symbol_var,    args[0], -1*args[1]])
                clauses.append([symbol_var, -1*args[0], -1*args[1]])
                clauses.append([symbol_var,    args[0],    args[1]])
            else:
                assert(0)
            vprint_title(self.options, 'tseitin_encode', 6)
            vprint(self.options, f'type: {type(symbol)}', 6)
            vprint(self.options, str(symbol), 6)
            vprint(self.options, f'{symbol} : {args}', 6)
            for clause in clauses:
                vprint(self.options, f'clause: {clause}', 6)
                if is_root:
                    self.root_tseitin_clauses.append(clause)
                else:
                    self.instantiated_orbit_tseitin_clauses.append(clause)
            return symbol_var

    def get_prime_literals(self, prime : Prime, negate=False) -> List[int]:
        literals = []
        for (var_id, val) in enumerate(prime.values):
            lit = self.atom_vars[var_id]
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
        for orbit in orbits:
            sub_orbit_vars = []
            for i in range(orbit.num_suborbits):
                sub_orbit_var = self.new_var()
                sub_orbit_vars.append(sub_orbit_var)
            self.orbit_vars.append(sub_orbit_vars)

    def _init_axioms_formula(self) -> None:
        dep_axioms = set(self.instantiator.dep_axioms_str)
        if len(dep_axioms) > 0:
            for axiom_str in self.instantiator.protocol_interpreted_atoms:
                axiom_var = self.symbol2var_num[axiom_str]
                if axiom_str in dep_axioms:  # member(n,q) in axioms_str
                    self.root_assume_clauses.append([axiom_var])
                elif '~'+axiom_str in dep_axioms: # ~member(n,q) not in axioms_str
                    self.root_assume_clauses.append([-1*axiom_var])
        if self.instantiator.axiom_fmla != None:
            axiom_fmla_var = self.tseitin_encode(self.instantiator.axiom_fmla)
            self.root_assume_clauses.append([axiom_fmla_var])

    def _init_definitions_formula(self) -> None:
        for def_lhs, def_rhs in self.instantiator.instantiated_def_map.items():
            def_equal_symbol = il.Equals(def_lhs, def_rhs)
            def_equal_var    = self.tseitin_encode(def_equal_symbol) 
            self.root_assume_clauses.append([def_equal_var])

    def _init_equal_atoms_constraints(self) -> None:
        lhs_set = {} 
        for atom_id, atom in enumerate(self.instantiator.protocol_atoms_fmlas):
            if il.is_eq(atom):
                lhs = atom.args[0]
                if str(lhs) not in lhs_set:
                    lhs_set[str(lhs)] = []
                lhs_set[str(lhs)].append(atom_id)
        for eq_ids in lhs_set.values():
            at_least_one = [self.atom_vars[i] for i in eq_ids]
            self.root_assume_clauses.append(at_least_one)
            for id0 in range(len(eq_ids)-1):
                for id1 in range(id0+1, len(eq_ids)):
                    var0 = self.atom_vars[eq_ids[id0]]
                    var1 = self.atom_vars[eq_ids[id1]]
                    at_most_one = [-1*var0, -1*var1]
                    self.root_assume_clauses.append(at_most_one)

    def _init_orbit_selection_formula(self, orbits : List[PrimeOrbit]) -> None:
        # Eq (10) in FMCAD paper
        for (orbit_id, orbit) in enumerate(orbits):
            sub_orbit_vars = self.orbit_vars[orbit_id]
            sub_orbit_id   = -1
            for prime in orbit.primes:
                if prime.is_sub_repr:
                    sub_orbit_id += 1
                sub_orbit_var = sub_orbit_vars[sub_orbit_id]
                clause = self.get_prime_literals(prime, negate=True) 
                clause.append(-1*sub_orbit_var)
                self.clauses.append(clause)

    def _push_clauses_into_solvers(self) -> None:
        for clause in self.root_assume_clauses:
            self.def_prime_checker.add_clause(clause)
            self.sat_solver.add_clause(clause)
            if self.useMC == UseMC.sat:
                self.sat_counter.add_clause(clause)
        for clause in self.root_tseitin_clauses:
            self.def_prime_checker.add_clause(clause)
            self.sat_solver.add_clause(clause)
            if self.useMC == UseMC.sat:
                self.sat_counter.add_clause(clause)
        for clause in self.clauses:
            self.sat_solver.add_clause(clause)
            if self.useMC == UseMC.sat:
                self.sat_counter.add_clause(clause)

    def _write_model_count_cnf(self):
        fout = open('cnf', 'w')
        self.root_top_var = self.top_var
        clause_num = len(self.root_assume_clauses) + len(self.root_tseitin_clauses) + len(self.clauses) 
        fout.write(f'p cnf {self.root_top_var} {clause_num}'+'\n')
        for clause in self.root_assume_clauses:
            fout.write(f'{' '.join([str(lit) for lit in clause])} 0' + '\n')
        for clause in self.root_tseitin_clauses:
            fout.write(f'{' '.join([str(lit) for lit in clause])} 0' + '\n')
        for clause in self.clauses:
            fout.write(f'{' '.join([str(lit) for lit in clause])} 0' + '\n')
        fout.close()

    def _init_solvers(self, orbits : List[PrimeOrbit]) -> None:
        self._init_axioms_formula()
        self._init_definitions_formula()
        self._init_equal_atoms_constraints()
        self._init_orbit_selection_formula(orbits)
        self._push_clauses_into_solvers()
        if self.useMC == UseMC.mc:
            self._write_model_count_cnf()

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
            for i in pending:
                if i != orbit.id:
                    assumptions += [sub_orbit_var for sub_orbit_var in self.orbit_vars[i]]
            for i in solution:
                if i != orbit.id:
                    assumptions += [sub_orbit_var for sub_orbit_var in self.orbit_vars[i]]
            result = self.sat_solver.solve(assumptions)
            if result:
                break
        return result

    def _get_sharp_sat_count(self, assumptions) -> int:
        # update cnf
        clause_num = len(self.root_assume_clauses) + len(self.root_tseitin_clauses) + len(self.clauses) + len(assumptions) 
        sed_cmd    = f'sed -i \'1c\p cnf {self.root_top_var} {clause_num}\' cnf'
        vprint(self.options, sed_cmd)
        os.system(sed_cmd)
        fout = open('cnf', 'a')
        for a in assumptions:
            fout.write(f'{a} 0'+'\n')
        fout.close()
        # sharpSAT
        sharp_sat_cmd  = './sharpSAT/build/Profiling/sharpSAT cnf > out'
        vprint(self.options, sharp_sat_cmd)
        os.system(sharp_sat_cmd)
        # grep result
        tail_cmd = f'tail -5 out > out1'
        os.system(tail_cmd)
        head_cmd = f'head -1 out1 > out2'
        os.system(head_cmd)
        fin  = open('out2', 'r')
        line = next(fin)
        result  = int(line.split()[0])
        vprint(self.options, f'[SharpSAT RESULT]: {result}')
        # remove trailing assumptions in cnf
        head_cmd = f'head -n -{len(assumptions)} cnf > temp && mv temp cnf'
        os.system(head_cmd)
        return result

    def _get_sat_count(self, assumptions) -> int:
        result = self.sat_counter.solve(assumptions)
        if result:
            result, assigned = self.sat_counter.propagate(assumptions)
            atom_count = self._count_atom_var(assigned)
            len_assigned = len(self.atom_vars) - atom_count
            return (1 << len_assigned)
        else:
            return 0 # covered by existing solution

    def get_coverage(self, orbit : PrimeOrbit, solution) -> int:
        self.coverage[orbit.id] = 0
        block_sub_vars = []
        for sub_orbit_id, repr_prime in enumerate(orbit.suborbit_repr_primes):
            assumptions = self.get_prime_literals(repr_prime)
            for i in solution:
                assumptions += [sub_orbit_var for sub_orbit_var in self.orbit_vars[i]]
            assumptions += [sub_orbit_var for sub_orbit_var in block_sub_vars]
            if self.useMC == UseMC.sat:
                self.coverage[orbit.id]  +=  self._get_sat_count(assumptions)
            else:
                self.coverage[orbit.id]  += self._get_sharp_sat_count(assumptions)
            block_sub_vars.append(self.orbit_vars[orbit.id][sub_orbit_id])
        return self.coverage[orbit.id] 

    def is_definition_prime(self, orbit : PrimeOrbit) -> bool:
        assumptions = self.get_prime_literals(orbit.repr_prime)
        result      = self.def_prime_checker.solve(assumptions)
        return False if result else True

    def init_minimization_check_clauses(self):
        for atom_eq in self.tran_sys.atom_equivalence_constraints:
            atom_eq_var = self.tseitin_encode(atom_eq, is_root=True)
            self.root_assume_clauses.append([atom_eq_var])

    def _get_cube_fmla(self, cube):
        literals = []
        for (var_id, val) in enumerate(cube):
            lit  = self.instantiator.protocol_atoms_fmlas[var_id]
            if val == '1':
                literals.append(lit) 
            elif val == '0':
                literals.append(il.Not(lit))
        return il.And(*literals)

    def init_minimization_check_solver(self, quantified_orbits, protocol : Protocol):
        top_var = self.top_var
        self.min_checker = SatSolver()   
        self.instantiated_orbit_assume_clauses  = []
        self.instantiated_orbit_tseitin_clauses = []
        invariants = [self.instantiator.instantiate_quantifier(qorbit) for qorbit in quantified_orbits]
        if self.options.forward_mode == ForwardMode.Sym_DFS:
            for invar in invariants: 
                orbit_fmla_var = self.tseitin_encode(invar, is_root=False)
                self.instantiated_orbit_assume_clauses.append([orbit_fmla_var])
            if len(quantified_orbits) == 0: # edge case
                top_atom_var = self.atom_vars[-1]
                self.min_checker.add_clause([top_atom_var, -1*top_atom_var])
        else:
            # invars
            if len(invariants) == 0: # edge case
                self.rmin_var = self.new_var()
            else:
                and_invars = il.And(*invariants)
                self.rmin_var = self.tseitin_encode(and_invars, is_root=False) 
            # reachable states
            cube_fmlas = [self._get_cube_fmla(cube) for cube in protocol.reachable_states]
            or_cubes = il.Or(*cube_fmlas)
            self.reach_var  = self.tseitin_encode(or_cubes)
            # self.reach_var XOR self.rmin_var
            self.min_checker.add_clause([self.reach_var, self.rmin_var])
            self.min_checker.add_clause([-1*self.reach_var, -1*self.rmin_var])

        for clause in self.root_assume_clauses:
            self.min_checker.add_clause(clause)
        for clause in self.root_tseitin_clauses:
            self.min_checker.add_clause(clause)
        for clause in self.instantiated_orbit_assume_clauses:
            self.min_checker.add_clause(clause)
        for clause in self.instantiated_orbit_tseitin_clauses:
            self.min_checker.add_clause(clause)
        self.top_var = top_var

    def get_minimization_check_minterm(self):
        result  = self.min_checker.solve()
        minterm = None 
        if result:
            model   = self.min_checker.get_model()
            minterm = ['1' if model[atom_id] == atom_var else '0' for atom_id, atom_var in enumerate(self.atom_vars)] 
        return (result, minterm)

    def block_minimization_check_minterm(self, values):
        block_clause = []
        for atom_id, atom_var in enumerate(self.atom_vars):
            if values[atom_id] == '1':
                block_clause.append(-1*atom_var)
            elif values[atom_id] == '0':
                block_clause.append(atom_var)
        self.min_checker.add_clause(block_clause)

    def _get_prime_clause(self, prime : Prime):
        literals = []
        for (var_id, val) in enumerate(prime.values):
            lit  = self.instantiator.protocol_atoms_fmlas[var_id]
            if val == '1':
                literals.append(lit) 
            elif val == '0':
                literals.append(il.Not(lit))
        return il.Not(il.And(*literals))

    def init_quantifier_inference_check_solver(self, primes : List[Prime], quantified_orbit):
        top_var = self.top_var
        self.qinfer_checker = SatSolver()
        self.instantiated_orbit_assume_clauses  = []
        self.instantiated_orbit_tseitin_clauses = []
        primes_clauses = [self._get_prime_clause(prime) for prime in primes]
        inst_orbit     = self.instantiator.instantiate_quantifier(quantified_orbit)
        eq_term        = il.Equals(il.And(*primes_clauses), inst_orbit)
        eq_var         = self.tseitin_encode(eq_term, is_root=False)
        # assume neq
        self.instantiated_orbit_assume_clauses.append([-1*eq_var])

        for clause in self.root_assume_clauses:
            self.qinfer_checker.add_clause(clause)
        for clause in self.root_tseitin_clauses:
            self.qinfer_checker.add_clause(clause)
        for clause in self.instantiated_orbit_assume_clauses:
            self.qinfer_checker.add_clause(clause)
        for clause in self.instantiated_orbit_tseitin_clauses:
            self.qinfer_checker.add_clause(clause)
        self.top_var = top_var
            
    def quantifier_inference_check(self):
        result  = self.qinfer_checker.solve()
        return not result



