from pysmt.shortcuts import Function, EqualsOrIff
from itertools import product

import re
from util import FormulaPrinter as printer
from verbose import *
from system  import *

class FiniteIvyInstantiator():
    def __init__(self, tran_sys):
        self.tran_sys           = tran_sys
        self._global_vars        = [] # global non-defined + global-defined
        self._non_global_vars    = [] # local non-defined + local-defined
        self._indep_vars         = [] # local non-defined
        self._initialize()

        # instantiated
        self._instantiated_global_vars       = [] # can contain non-boolean output functions
        self._instantiated_indep_vars        = []
        self._instantiated_global_equals     = [] # either atomic predicate or equality term (f=g)
        self._instantiated_non_global_equals = []
        self._instantiated_actions           = []
        self._instantiate()


        # public member 
        self.dfs_state_vars      = []
        self.dfs_global_vars     = []
        self.protocol_atoms      = []
        self.protocol_atoms_fmls = []        
        self.ivy_state_vars      = []
        self.ivy_actions         = []
        self._set_pretty_instantiations()

    def _init_global_vars(self):
        self._global_vars = self.tran_sys.finite_system.global_symbols

    def _init_non_global_vars(self):
        for symbol in self.tran_sys.finite_system.states:
            if symbol not in self.tran_sys.finite_system.global_symbols:
                self._non_global_vars.append(symbol)

    def _init_independent_vars(self):
        for symbol in self.tran_sys.finite_system.states:
            if (symbol not in self.tran_sys.finite_system.global_symbols and
                printer.pretty_print_str(symbol) not in self.tran_sys.finite_system.definitions.keys()):
                self._indep_vars.append(symbol)

    def _initialize(self):
        self._init_global_vars()
        self._init_non_global_vars()
        self._init_independent_vars()

    def _get_all_params_of_param_types(self, param_types):
        elems = []
        for ptype in param_types:
            elems.append(self.tran_sys.sort2consts[ptype])
        all_params = list(product(*elems))
        all_params = [list(params) for params in all_params]
        return all_params

    def _get_instantiated_variables(self, var, var_type, to_equals):
        if var_type.is_bool_type() or not to_equals:
            return [var]
        eq_symbols = []
        for elem in self.sort2elems[var_type]:
            eq_symbols.append(EqualsOrIff(var, elem))
        return eq_symbols

    def _get_instantiated_functions(self, func_symbol, to_equals):
        func_type   = func_symbol.symbol_type()
        param_types = func_type._param_types
        return_type = func_type._return_type
        all_params  = self._get_all_params_of_param_types(param_types)
        functions  = []
        for params in all_params:
            func  = Function(func_symbol, params)
            funcs = self._get_instantiated_variables(func, return_type, to_equals)
            functions += funcs
        return functions 

    def _get_instantiated_terms(self, terms, to_equals):
        instantiated_terms = []
        for var in terms:
            var_type = var.symbol_type() 
            if var_type.is_function_type(): 
                instantiated_terms += self._get_instantiated_functions(var, to_equals)
            else: 
                instantiated_terms += self._get_instantiated_variables(var, var_type, to_equals)
        return instantiated_terms

    def _get_all_parameterized_actions(self):
        actions = self.tran_sys.finite_system.actions
        parameterized_actions = []
        for action in actions:
            parameterized_actions += self._get_instantiated_functions(action, to_equals=False)
        return parameterized_actions

    def _instantiate(self):
        self._instantiated_global_vars       = self._get_instantiated_terms(terms=self._global_vars,     to_equals=False)
        self._instantiated_indep_vars        = self._get_instantiated_terms(terms=self._indep_vars,      to_equals=False)
        self._instantiated_global_equals     = self._get_instantiated_terms(terms=self._global_vars,     to_equals=True)
        self._instantiated_non_global_equals = self._get_instantiated_terms(terms=self._non_global_vars, to_equals=True)
        self._instantiated_actions           = self._get_all_parameterized_actions()

    def _get_dfs_variables_from_instantiated_equals(self, instantiated_equals):
        pretty_equals   = []
        subst = self.tran_sys.get_pretty_set_substitution_map()
        for equal in instantiated_equals:
            pretty_equals.append(printer.pretty_print_str(equal, subst).replace(' ',''))

        pretty_dfs_vars = []
        for var in pretty_equals:
            symbol_name = '' 
            args        = []
            match_predicate = re.search(r'(\w+)\(([^)]+)\)',         var)
            match_eq        = re.search(r'\((\w+)\s*=\s*(\w+)\)',    var)
            match_func_eq   = re.search(r'\((\w+)\((\w+)\)=(\w+)\)', var)
            if match_func_eq: # case 4: general function
                symbol_name = match_func_eq.group(1) + '='
                args        = match_func_eq.group(2).split(', ') + match_func_eq.group(3).split(', ')
            elif match_predicate: # case 3: predicate 
                symbol_name = match_predicate.group(1)
                args        = match_predicate.group(2).split(',') + ['true']
            elif match_eq: # case 1
                symbol_name = match_eq.group(1) + '='
                args        = match_eq.group(2).split(',')
            else: # case 2: bool
                symbol_name = var.strip('( )')            
                args        = ['true']
            pretty_var = symbol_name + '(' + ','.join(args) + ')'
            pretty_dfs_vars.append(pretty_var)
        return pretty_dfs_vars

    def _set_dfs_variables(self):
        self.dfs_state_vars  = self._get_dfs_variables_from_instantiated_equals(self._instantiated_non_global_equals)
        self.dfs_global_vars = self._get_dfs_variables_from_instantiated_equals(self._instantiated_global_equals)

    def _set_protocol_atoms(self):
        atoms = self._instantiated_non_global_equals
        subst = self.tran_sys.get_pretty_set_substitution_map()
        for atom in atoms:
            self.protocol_atoms.append(printer.pretty_print_str(atom, subst).replace(' ',''))
        self.protocol_atoms_fmls = self._instantiated_non_global_equals
    
    def _set_ivy_variables(self):
        ivy_vars  = self._instantiated_indep_vars
        subst = self.tran_sys.get_pretty_set_substitution_map()
        for var in ivy_vars:
            self.ivy_state_vars.append(printer.pretty_print_str(var, subst).replace(' ',''))

    def _set_ivy_actions(self):
        actions = self._instantiated_actions
        subst = self.tran_sys.get_pretty_set_substitution_map()
        for action in actions:
            self.ivy_actions.append(printer.pretty_print_str(action, subst).replace(' ',''))

    def _set_pretty_instantiations(self):
        self._set_dfs_variables()
        self._set_protocol_atoms()
        self._set_ivy_variables()
        self._set_ivy_actions()
 