import re
from itertools import product
from ivy import ivy_logic as il
from ivy import ivy_solver as slv
from ivy import ivy_logic_utils as ilu
from transition_system import TransitionSystem
from finite_ivy_instantiate import FiniteIvyInstantiator
from util import QrmOptions
from verbose import *

class PrimeChecker():
    def __init__(self, options : QrmOptions, tran_sys : TransitionSystem, instantiator : FiniteIvyInstantiator, atoms_str, atoms_fmla):
        self.options      = options
        self._atoms_str   = atoms_str
        self._atoms_fmla  = atoms_fmla.copy()
        self._axioms_fmla = instantiator.dep_axioms_fmla
        self._tran_sys    = tran_sys
        self._instantiated_def_map = {} 
        self.set_definitions(instantiator.instantiated_def_map)

    def set_definitions(self, instantiated_dep_map):
        for def_lhs, def_rhs in instantiated_dep_map.items():
            self._instantiated_def_map[str(def_lhs)] = def_rhs
        for atom_id, atom_str in enumerate(self._atoms_str):
            if atom_str in self._instantiated_def_map:
                def_fmla =  self._instantiated_def_map[atom_str]
                self._atoms_fmla[atom_id] = def_fmla

    def get_literals(self, values):
        literals = []
        for (atom_id, val) in enumerate(values):
            if val == '1':
                literals.append(self._atoms_fmla[atom_id])
            elif val == '0':
                literals.append(il.Not(self._atoms_fmla[atom_id]))
        return literals

    def verbose_definition_prime(self, values, check_prime_fmla, res):
        if self.options.verbosity >= 5:
            literals = []
            for (atom_id, val) in enumerate(values):
                if val == '1':
                    literals.append(self._atoms_str[atom_id])
                elif val == '0':
                    literals.append('~' + self._atoms_str[atom_id])
            vprint_title(self.options, 'is_definition_prime', 5)
            vprint(self.options, 'Prime: ' + ' & '.join(literals), 5)
            vprint(self.options, 'Satisfiability check on: ' + str(check_prime_fmla), 5)
            vprint(self.options, str(res), 5)

    def verbose_dependent_relation(self, values, res):
        if self.options.verbosity >= 5:
            literals = []
            for (atom_id, val) in enumerate(values):
                if val == '1':
                    literals.append(self._atoms_str[atom_id])
                elif val == '0':
                    literals.append('~' + self._atoms_str[atom_id])
            vprint_title(self.options, 'requires_dependet_relation', 5)
            vprint(self.options, 'Prime: ' + ' & '.join(literals), 5)
            vprint(self.options, 'Requires dependent relation: ' + str(res))

    def is_definition_prime(self, values):
        literals = self.get_literals(values)
        fmlas    = self._axioms_fmla + literals
        check_prime_fmla = il.And(*fmlas)
        solver = slv.z3.Solver()
        solver.add(slv.formula_to_z3(check_prime_fmla))
        res = solver.check()
        assert(res == slv.z3.unsat or slv.z3.sat)
        self.verbose_definition_prime(values, check_prime_fmla, res)
        return True if res == slv.z3.unsat else False

    def requires_dependent_relation(self, values):
        literals = self.get_literals(values)
        formula  = il.And(*literals)
        used_sorts = ilu.used_sorts_ast(formula)
        res = False
        for set_sort, dep_type in self._tran_sys.dep_types.items():
            elem_sort = dep_type.elem_sort
            if set_sort in used_sorts and elem_sort in used_sorts:
                res = True
                break
        self.verbose_dependent_relation(values, res)
        return res
        
