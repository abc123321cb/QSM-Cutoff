import re
import z3
from itertools import product
from pysmt.shortcuts import Or, And, Not, is_unsat
from pysmt.logics import QF_UF
from transition import TransitionSystem
from util import QrmOptions
from util import FormulaPrinter as printer

def get_instantiated_definition_key(instantiated_def, pretty_subst):
    def_atom = printer.pretty_print_str(instantiated_def, pretty_subst)
    match_pred = re.search(r'(\w+)\(([^)]+)\)',  def_atom)
    assert(match_pred)
    predicate = match_pred.group(1)
    args      = match_pred.group(2).split(', ')
    return predicate + '(' + ','.join(args) + ')'

class PrimeChecker():
    def __init__(self, atoms_str, atoms_fmla, tran_sys : TransitionSystem):
        self._atoms_str   = atoms_str
        self._atoms_fmla  = atoms_fmla.copy()
        self._axioms_fmla = []
        self._tran_sys    = tran_sys
        self.set_definitions()
        self.set_axiom_formula()

    def get_quantified_var_substitution(self, quantified_vars):
        vars_domain = []
        for var in quantified_vars:
            var_sort   = var.get_type()
            var_domain = self._tran_sys.sort2consts[var_sort]
            vars_domain.append(var_domain)
        var_subst_candidates = list(product(*vars_domain))
        substition_maps = [] 
        for subst_candidate in var_subst_candidates:
            subst_map = {}
            for i, var in enumerate(quantified_vars):
                subst_map[var] = subst_candidate[i]
            substition_maps.append(subst_map)
        return substition_maps

    def recursive_instantiate_quantifier(self, formula):
        if formula.has_quantifier_variables():
            prefix_vars = formula.quantifier_vars()
            if len(prefix_vars) > 0:
                instantiated_matrix = self.recursive_instantiate_quantifier(formula.arg(0))
                prefix_subst_maps   = self.get_quantified_var_substitution(prefix_vars)
                instantiated_fmlas  = [instantiated_matrix.substitute(subst) for subst in prefix_subst_maps]
                if formula.is_exists():
                    formula = Or(instantiated_fmlas)
                else:
                    formula = And(instantiated_fmlas)
            else:
                for i, arg in enumerate(formula.args()):
                    instantiated_arg = self.recursive_instantiate_quantifier(arg)
                    formula._content.args[i] = instantiated_arg
        return formula

    def set_definitions(self):
        def_map = self._tran_sys.finite_system.definitions
        pretty_subst = self._tran_sys.get_pretty_set_substitution_map()
        instantiated_def_map = {}
        for def_var, def_fmla in def_map.items():
            if def_var.startswith('__'):
                assert(def_fmla.is_forall())
                def_prefix_vars = def_fmla.quantifier_vars()
                def_matrix      = def_fmla.arg(0)
                assert(def_matrix.is_iff() or def_matrix.is_equals())
                def_lhs = def_matrix.arg(0)
                def_rhs = def_matrix.arg(1)
                def_rhs  = self.recursive_instantiate_quantifier(def_rhs)
                prefix_subst_maps = self.get_quantified_var_substitution(def_prefix_vars)
                for subst_map in prefix_subst_maps:
                    instantiated_lhs = def_lhs.substitute(subst_map)
                    instantiated_rhs = def_rhs.substitute(subst_map)
                    def_atom = get_instantiated_definition_key(instantiated_lhs, pretty_subst) 
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
                literals.append(Not(self._atoms_fmla[atom_id]))
        return literals

    def is_definition_prime(self, values):
        literals = self.get_literals(values)
        fmlas    = self._axioms_fmla + literals
        check_prime_fmla = And(fmlas)
        res = None
        res = is_unsat(check_prime_fmla, solver_name='z3', logic=QF_UF)
        if res != None:
            return res
        return False
