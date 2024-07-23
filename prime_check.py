import re
from itertools import product
from ivy import ivy_logic as il
from ivy import ivy_solver as slv
from ivy import ivy_logic_utils as ilu
from transition_system import TransitionSystem
from util import QrmOptions
from verbose import *

def get_instantiated_definition_key(instantiated_def):
    def_atom = str(instantiated_def)
    match_pred = re.search(r'(\w+)\(([^)]+)\)',  def_atom)
    assert(match_pred)
    predicate = match_pred.group(1)
    args      = match_pred.group(2).split(', ')
    return predicate + '(' + ','.join(args) + ')'

class PrimeChecker():
    def __init__(self, options : QrmOptions, tran_sys : TransitionSystem, atoms_str, atoms_fmla):
        self.options      = options
        self._atoms_str   = atoms_str
        self._atoms_fmla  = atoms_fmla.copy()
        self._axioms_fmla = []
        self._tran_sys    = tran_sys
        self.set_definitions()
        self.set_axiom_formula()

    def get_var_substitution(self, var_list):
        vars_domain = []
        for var in var_list:
            var_sort   = var.sort
            var_domain = self._tran_sys.sort2consts[var_sort]
            vars_domain.append(var_domain)
        var_subst_candidates = list(product(*vars_domain))
        substition_maps = [] 
        for subst_candidate in var_subst_candidates:
            subst_map = {}
            for i, var in enumerate(var_list):
                subst_map[var] = subst_candidate[i]
            substition_maps.append(subst_map)
        return substition_maps

    def recursive_instantiate_quantifier(self, formula):
        if il.is_quantifier(formula):
            prefix_vars = il.quantifier_vars(formula)
            if len(prefix_vars) > 0:
                instantiated_matrix = self.recursive_instantiate_quantifier(formula.body)
                prefix_subst_maps   = self.get_var_substitution(prefix_vars)
                instantiated_fmlas  = [il.substitute(instantiated_matrix, subst) for subst in prefix_subst_maps]
                if il.is_exists(formula):
                    formula = il.Or(*instantiated_fmlas)
                else:
                    formula = il.And(*instantiated_fmlas)
            else:
                for i, arg in enumerate(formula.args):
                    instantiated_arg = self.recursive_instantiate_quantifier(arg)
                    formula._content.args[i] = instantiated_arg
        return formula

    def set_definitions(self):
        def_map = self._tran_sys.definitions
        instantiated_def_map = {}
        for def_ast in def_map.values():
            def_lhs = def_ast.lhs()  # didNotVote(N)
            def_rhs = def_ast.rhs()  # forall V. ~vote(N,V)
            assert(il.is_forall(def_rhs))
            def_lhs_free_vars = def_lhs.terms # N
            var_subst_maps = self.get_var_substitution(def_lhs_free_vars)
            def_rhs  = self.recursive_instantiate_quantifier(def_rhs)
            for subst_map in var_subst_maps:
                instantiated_lhs = il.substitute(def_lhs, subst_map)
                instantiated_rhs = il.substitute(def_rhs, subst_map)
                def_atom = get_instantiated_definition_key(instantiated_lhs) 
                instantiated_def_map[def_atom] = instantiated_rhs
        for atom_id, atom_str in enumerate(self._atoms_str):
            if atom_str in instantiated_def_map:
                def_fmla =  instantiated_def_map[atom_str]
                self._atoms_fmla[atom_id] = def_fmla

    def set_axiom_formula(self):
        self._axioms_fmla = self._tran_sys.get_dependent_axioms_fmla()

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
        
