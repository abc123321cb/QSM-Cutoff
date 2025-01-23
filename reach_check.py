from pysat.solvers import Cadical153 as SatSolver
from typing import List, Dict
from finite_ivy_instantiate import FiniteIvyInstantiator
from util import QrmOptions, ForwardMode
from verbose import *
from transition_system import TransitionSystem, get_transition_system
from forward_reach import ForwardReachability
from minimize import Rmin
from protocol import Protocol
from ivy import ivy_logic as il
from ivy import logic as lg
from ivy import ivy_logic_utils as ilu

class ReachCheck():
    def __init__(self, options : QrmOptions, tran_sys : TransitionSystem, instantiator : FiniteIvyInstantiator, protocol : Protocol) -> None: 
        self.options       = options
        self.tran_sys      = tran_sys
        self.instantiator  = instantiator 
        self.protocol      = protocol
        self.sat_solver    = SatSolver() 
        self.top_var               = 0
        self.symbol2var_num        = {}
        self.atom_vars : List[int] = []
        # axiom, definition
        self.root_assume_clauses   = [] 
        self.root_tseitin_clauses  = [] # axiom, definition
        # when reach is computed with BDD-based symbolic image computation
        self.rmin_var   = 0
        self.reach_var  = 0
        # min_check or qinfer_check
        self.clauses               = []

        self._init_vars()
        self._init_solvers()

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

    def _tseitin_encode(self, symbol) -> int:
        # e.g. a = b
        if isinstance(symbol, lg.Eq) and il.is_enumerated(symbol.args[0]) and il.is_enumerated(symbol.args[1]):
            symbol = self._get_canonical_equal_term(symbol)

        if str(symbol) in self.symbol2var_num:
            return self.symbol2var_num[str(symbol)]
        else:
            if isinstance(symbol, il.Not):
                return -1*self._tseitin_encode(symbol.args[0])
            if len(symbol.args) == 1:
                assert( isinstance(symbol, il.And) or isinstance(symbol, il.Or) )
                return self._tseitin_encode(symbol.args[0])
            assert(len(symbol.args) > 1) 
            symbol_var = self.new_var()
            args = [self._tseitin_encode(arg) for arg in symbol.args]
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
            vprint_title(self.options, '_tseitin_encode', 6)
            vprint(self.options, f'type: {type(symbol)}', 6)
            vprint(self.options, str(symbol), 6)
            vprint(self.options, f'{symbol} : {args}', 6)
            for clause in clauses:
                vprint(self.options, f'clause: {clause}', 6)
                self.root_tseitin_clauses.append(clause)
            return symbol_var

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
            axiom_fmla_var = self._tseitin_encode(self.instantiator.axiom_fmla)
            self.root_assume_clauses.append([axiom_fmla_var])

    def _init_definitions_formula(self) -> None:
        for def_lhs, def_rhs in self.instantiator.instantiated_def_map.items():
            def_equal_symbol = il.Equals(def_lhs, def_rhs)
            def_equal_var    = self._tseitin_encode(def_equal_symbol) 
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

    def _init_invariants(self) -> None:
        invariants  = []
        for invar in self.tran_sys.safety_properties:
            invar = self.instantiator.instantiate_quantifier(invar)
            if invar != il.And():
                invariants.append(invar)
        if self.options.forward_mode == ForwardMode.Sym_DFS:
            for invar in invariants: 
                invar_fmla_var = self._tseitin_encode(invar)
                self.root_assume_clauses.append([invar_fmla_var])
            if len(invariants) == 0: # edge case
                top_atom_var = self.atom_vars[-1]
                self.sat_solver.add_clause([top_atom_var, -1*top_atom_var])
        else:
            if len(invariants) == 0: # edge case
                self.rmin_var = self.new_var()
            else:
                and_invars = il.And(*invariants)
                self.rmin_var = self._tseitin_encode(and_invars) 

    def _get_cube_fmla(self, cube):
        literals = []
        for (var_id, val) in enumerate(cube):
            lit  = self.protocol.atoms_fmla[var_id]
            if val == '1':
                literals.append(lit) 
            elif val == '0':
                literals.append(il.Not(lit))
        return il.And(*literals)

    def _init_reachable_states(self) -> None:
        cube_fmlas = []
        for cube in self.protocol.reachable_states:
            cube_fmla = self._get_cube_fmla(cube)
            cube_fmlas.append(cube_fmla)
        or_cubes = il.Or(*cube_fmlas)
        self.reach_var  = self._tseitin_encode(or_cubes)

    def _push_clauses_into_solvers(self) -> None:
        for clause in self.root_assume_clauses:
            self.sat_solver.add_clause(clause)
        for clause in self.root_tseitin_clauses:
            self.sat_solver.add_clause(clause)
        for clause in self.clauses:
            self.sat_solver.add_clause(clause)
        if self.options.forward_mode == ForwardMode.BDD_Symbolic:
            # self.reach_var XOR self.rmin_var
            self.sat_solver.add_clause([self.reach_var, self.rmin_var])
            self.sat_solver.add_clause([-1*self.reach_var, -1*self.rmin_var])

    def _init_vars(self) -> None:
        for atom in self.instantiator.protocol_atoms:
            atom_var = self.new_var()
            self.atom_vars.append(atom_var)
            self.symbol2var_num[atom] = atom_var 

    def _init_solvers(self) -> None:
        self._init_axioms_formula()
        self._init_definitions_formula()
        self._init_equal_atoms_constraints()
        self._init_invariants()
        if self.options.forward_mode == ForwardMode.BDD_Symbolic:
            self._init_reachable_states()
        self._push_clauses_into_solvers()

    def _get_model(self):
        result  = self.sat_solver.solve()
        minterm = None 
        if result:
            model   = self.sat_solver.get_model()
            minterm = ['1' if model[atom_id] == atom_var else '0' for atom_id, atom_var in enumerate(self.atom_vars)] 
        return (result, minterm)

    def _block_model(self, values):
        block_clause = []
        for atom_id, atom_var in enumerate(self.atom_vars):
            if values[atom_id] == '1':
                block_clause.append(-1*atom_var)
            elif values[atom_id] == '0':
                block_clause.append(atom_var)
        self.sat_solver.add_clause(block_clause)

    def _compare_symmetry_quotient(self) -> bool:
        (result, values)  = self._get_model()
        model_repr_states = set()
        model_match = True
        while result:
            repr_int = int(''.join(values), 2)
            for nvalues in self.protocol.all_permutations(values[:self.protocol.state_atom_num]): # only permute the mutable part
                nvalues += values[self.protocol.state_atom_num:]
                repr_int = min(int(''.join(nvalues), 2), repr_int)
                self._block_model(nvalues)
            if not repr_int in self.protocol.repr_states:
                bit_str = '{0:0{1}b}'.format(repr_int, self.protocol.atom_num)[:self.protocol.state_atom_num]
                vprint(self.options, f'Found a representative state in Rmin not in reachability: decimal: {repr_int}, binary: {bit_str}')
                model_match = False 
                if self.options.early_terminate_reach:
                    vprint(self.options, f'[REACH_CHECK RESULT]: FAIL')
                    return model_match
            model_repr_states.add(repr_int)
            (result, values) = self._get_model()

        difference = self.protocol.repr_states - model_repr_states
        if len(difference) > 0:
            vprint(self.options, 'Representatitive states in reachability not in Rmin')
            vprint(self.options, f'{difference}')
            model_match = False
        if model_match:
            vprint(self.options, f'[REACH_CHECK RESULT]: PASS')
        else:
            vprint(self.options, f'[REACH_CHECK RESULT]: FAIL')
        return model_match 

    def _equivalence_checking(self) -> bool:
        result = self.sat_solver.solve()
        if result: # Non-equal
            vprint(self.options, f'[REACH_CHECK RESULT]: FAIL')
            return False
        else:
            vprint(self.options, f'[REACH_CHECK RESULT]: PASS')
            return True

    def is_rmin_matching_reachability(self) -> bool:
        if self.options.forward_mode == ForwardMode.Sym_DFS:
            return self._compare_symmetry_quotient()
        else:
            return self._equivalence_checking()

