from __future__ import print_function
import sys
from pysmt.smtlib.parser import SmtLibParser
from pysmt.shortcuts import Symbol, Not, Enum, Function, EqualsOrIff
from pysmt.typing import EnumType
from pysmt.environment import get_env
from itertools import combinations, product

from util import FormulaPrinter as printer
from util import SORT_SUFFIX, SET_DELIM
from verbose import *
from system  import *

#*************************************************************************
# utils 
#*************************************************************************
registered_dependent_relations           = {}
registered_dependent_relations['member'] = lambda elem_size : int(elem_size/2)+1 # member selection function
set_delim = SET_DELIM

#*************************************************************************
# helpers 
#*************************************************************************
def get_enum_element_names(sort, size, idx):
    enum_elem_names = []
    sort_suffix = SORT_SUFFIX + str(idx) + ':'
    for i in range(size):
        # create the symbol of one finite element of sort
        symbol_name = str(sort) + ':f' + str(i)
        symbol      = Symbol(symbol_name, sort)
        elem_name   = str(sort) + sort_suffix + str(i)
        enum_elem_names.append(elem_name)
    return enum_elem_names

def get_enum_sort(sort, enum_elem_names, idx):
    sort_suffix = SORT_SUFFIX + str(idx) + ':'
    enum_sort_name = str(sort) + sort_suffix
    enum_sort      = EnumType(enum_sort_name,  enum_elem_names)
    return enum_sort

def get_enum_elements(enum_sort, enum_elem_names):
    enum_elems = []
    for elem_name in enum_elem_names:
        elem = Enum(elem_name, enum_sort)
        enum_elems.append(elem)
    return enum_elems

def get_enum_qvars(enum_sort, enum_elem_names):
    enum_qvars = []
    for elem_name in enum_elem_names:
        qvar_name = 'Q:' + elem_name                
        qvar = Symbol(qvar_name, enum_sort)
        enum_qvars.append(qvar)
    return enum_qvars

#*************************************************************************
# class: DependentType
#*************************************************************************
class DependentType():
    # static data
    def __init__(self, dep_relation, set_sort, elem_sort, elements, select_func):
        self.dep_relation = dep_relation  # e.g. "member"
        self.set_sort     = set_sort      # e.g. "quorum"
        self.elem_sort    = elem_sort     # e.g. "node"
        self.sets         = []            # e.g. 0 -> [0,1], 1 -> [0,2], 2 -> [1,2] .....
        elem_size     = len(elements)
        select_space  = list(range(elem_size))
        selections    = list(combinations(select_space, select_func(elem_size)))
        for selection in selections:
            elems_in_set = [elements[elem_id] for elem_id in selection]
            self.sets.append(elems_in_set)

    def get_elements_in_set(self, set_id):
        return  self.sets[set_id] 

#*************************************************************************
# class: TransistionSystem
#*************************************************************************
class TransitionSystem(SmtLibParser):
    def __init__(self, options, env=None, interactive=False):
        # helpers
        self.options    = options
        self._parser    = SmtLibParser(env,interactive)
        # data
        self.infinite_sorts  = dict()   # sort name to sort of infinite size
        self.sort2elems      = dict()   # finite sort to finite set of elements
        self.sort2qvars      = dict()   # finit sort to quantified variables
        self.sort_fin2inf    = dict()   # finit sort to infinite sort
        self.sort_inf2fin    = dict()   # infinite sort to enumsort
        self.infinite_system = InfiniteSystem() # original infinite system from vmt
        self.finite_system   = FiniteSystem()   # finitized system 
        self._idx = 0                   # subscript for enum type
        # dependent sorts
        self.dep_types       = dict()   # "quorum" to quorum meta data (e.g. "member", "node" ...) 

    #------------------------------------------------------------
    # TransitionSystem: helper methods     
    #------------------------------------------------------------
    def _get_dependent_set_sort(self, dep_relation, inf2fin=False):
        dep_type = dep_relation.symbol_type()
        assert(len(dep_type.param_types) == 2)
        set_sort  = dep_type.param_types[1]
        if inf2fin:
            return self.sort_inf2fin[set_sort]
        return set_sort

    def _get_dependent_element_sort(self, dep_relation, inf2fin=False):
        dep_type = dep_relation.symbol_type()
        assert(len(dep_type.param_types) == 2)
        elem_sort = dep_type.param_types[0]
        if inf2fin:
            return self.sort_inf2fin[elem_sort]
        return elem_sort

    #------------------------------------------------------------
    # TransitionSystem: private methods
    #------------------------------------------------------------
    def _add_sort(self, sort, size):
        assert(size > 0)
        self.options.sizes[str(sort)]  = size
        self.infinite_sorts[str(sort)] = sort
        enum_elem_names = get_enum_element_names(sort, size, self._idx)
        enum_sort       = get_enum_sort(sort, enum_elem_names, self._idx)
        enum_elems      = get_enum_elements(enum_sort, enum_elem_names)
        enum_qvars      = get_enum_qvars(enum_sort, enum_elem_names)
        self.sort2elems[enum_sort]    = enum_elems
        self.sort2qvars[enum_sort]    = enum_qvars
        self.sort_inf2fin[sort]       = enum_sort
        self.sort_fin2inf[enum_sort]  = sort

    def _read_sort(self, fmla, annot_list):
        assert(len(annot_list)==1)
        size = int(annot_list[0])
        sort = fmla.symbol_type()
        sort_str = str(sort)
        if sort_str in self.options.sizes:
            size = self.options.sizes[sort_str]
        if size > 0:
            self._add_sort(sort, size)

    def _add_dependent_sorts(self):
        from math import comb 
        for symbol in self.infinite_system.global_symbols:
            if str(symbol) in registered_dependent_relations:
                dep_relation  = symbol 
                select_func   = registered_dependent_relations[str(symbol)]
                elem_sort     = self._get_dependent_element_sort(dep_relation, inf2fin=True) # finite
                set_sort      = self._get_dependent_set_sort(dep_relation) # infinite
                elem_size     = self.get_sort_size(elem_sort)
                self._add_sort(set_sort, comb(elem_size, select_func(elem_size)))

    def _instantiate_dependent_types(self):
        for symbol in self.infinite_system.global_symbols:
            if str(symbol) in registered_dependent_relations:
                dep_relation = symbol.fsubstitute() 
                select_func  = registered_dependent_relations[str(symbol)]
                elem_sort    = self._get_dependent_element_sort(dep_relation)
                set_sort     = self._get_dependent_set_sort(dep_relation)
                elements     = self.sort2elems[elem_sort]
                dep_type     = DependentType(dep_relation, set_sort, elem_sort, elements, select_func)
                self.dep_types[set_sort] = dep_type

    def _get_filtered_state_variables(self, var_filter='non-global'):
        if var_filter == 'global':
            global_vars = []
            for symbol in self.finite_system.states:
                if symbol in self.finite_system.global_symbols:
                    global_vars.append(symbol)
            return global_vars
        elif var_filter == 'non-global':
            non_global_vars = []
            for symbol in self.finite_system.states:
                if symbol not in self.finite_system.global_symbols:
                    non_global_vars.append(symbol)
            return non_global_vars
        else:
            indep_vars = [] 
            for prev_symbol in self.finite_system.states:
                if prev_symbol not in self.finite_system.global_symbols:
                    next_symbol = self.finite_system.prev2next[prev_symbol]
                    if printer.pretty_print_str(next_symbol) not in self.finite_system.definitions.keys():
                        indep_vars.append(prev_symbol)
            return indep_vars

    def _get_all_params_of_param_types(self, param_types):
        elems = []
        for ptype in param_types:
            elems.append(self.sort2elems[ptype])
        all_params = list(product(*elems))
        all_params = [list(params) for params in all_params]
        return all_params

    def _get_instantiated_variables(self, var, var_type, to_eq_term=False):
        if var_type.is_bool_type() or not to_eq_term:
            return [var]
        eq_symbols = []
        for elem in self.sort2elems[var_type]:
            eq_symbols.append(EqualsOrIff(var, elem))
        return eq_symbols

    def _get_instantiated_functions(self, func_symbol, to_eq_term=False):
        func_type   = func_symbol.symbol_type()
        param_types = func_type._param_types
        return_type = func_type._return_type
        all_params  = self._get_all_params_of_param_types(param_types)
        functions  = []
        for params in all_params:
            func  = Function(func_symbol, params)
            funcs = self._get_instantiated_variables(func, return_type, to_eq_term)
            functions += funcs
        return functions 

    def _get_filtered_ground_atoms(self, var_filter='non-global', to_eq_term=False):
        state_vars = self._get_filtered_state_variables(var_filter)
        atoms = []
        for var in state_vars:
            var_type = var.symbol_type() 
            if var_type.is_function_type(): 
                atoms += self._get_instantiated_functions(var, to_eq_term)
            else: 
                atoms += self._get_instantiated_variables(var, var_type, to_eq_term)
        return atoms

    def _get_all_parameterized_actions(self):
        actions = self.finite_system.actions
        parameterized_actions = []
        for action in actions:
            parameterized_actions += self._get_instantiated_functions(action)
        return parameterized_actions

    #------------------------------------------------------------
    # TransitionSystem: public methods
    #------------------------------------------------------------
    def read_infinite_system_from_vmt(self, vmt_file):
        script = self._parser.get_script(vmt_file)
        annotations = script.annotations.get_annotations()
        for fmla, annot in annotations.items():
            for label, annot_set in annot.items():
                annot_list = list(annot_set)
                if   label == 'sort':
                    self._read_sort(fmla, annot_list)
                elif label == 'init':
                    self.infinite_system.read_init(fmla)
                elif label == 'axiom':
                    self.infinite_system.read_axiom(fmla, annot_list)
                elif label == 'action':
                    self.infinite_system.read_action(fmla, annot_list)
                elif label == 'invar-property':
                    self.infinite_system.read_invariant_property(fmla, annot_list)
                elif label == 'definition':
                    self.infinite_system.read_definitions(fmla, annot_list)
                elif label == 'next':
                    self.infinite_system.read_state(fmla, annot_list)
                elif label == 'global':
                    self.infinite_system.read_global_symbol(fmla, annot_list)
                else:
                    assert(0)
        self.infinite_system.read_declared_symbols(script)
        self._add_dependent_sorts()

    def set_finite_system(self):
        get_env().fsubstituter.set_ssubs(self.sort_inf2fin, self._idx, False)
        self._instantiate_dependent_types()
        self.finite_system.set_reference(self.infinite_system)
        self.finite_system.set_finitized_init()
        self.finite_system.set_finitized_axioms()
        self.finite_system.set_finitized_actions()
        self.finite_system.set_finitized_invariant_properties()
        self.finite_system.set_finitized_definitions()
        self.finite_system.set_finitized_states()
        self.finite_system.set_finitized_next_states()
        self.finite_system.set_finitized_symbols()
        self.finite_system.set_finitized_non_state_symbols()
        self.finite_system.set_finitized_global_symbols()
        self.finite_system.set_finitized_leq_symbols()
        self.finite_system.set_finitized_prev_to_next()
        self.finite_system.set_finitized_next_to_prev()
        self._idx += 1

    #------------------------------------------------------------
    # TransitionSystem: public access methods
    #------------------------------------------------------------
    def get_sort_name_from_finite_sort(self, sort):
        return str(self.sort_fin2inf[sort])

    def get_finite_sort_from_sort_name(self, sort_name):
        inf_sort = self.infinite_sorts[sort_name]
        return self.sort_inf2fin[inf_sort]

    def get_state_variables(self):
        return list(self.infinite_system.next_states)

    def get_sort_size(self, sort):
        sort_name = self.get_sort_name_from_finite_sort(sort)
        return self.options.sizes[sort_name]

    def get_dependent_relation(self, set_sort):
        dep_type  = self.dep_types[set_sort]
        return dep_type.dep_relation

    def get_dependent_element_sort(self, set_sort):
        dep_type  = self.dep_types[set_sort]
        return dep_type.elem_sort

    def get_dependent_elements(self, set_sort):
        elem_sort = self.get_dependent_element_sort(set_sort)
        return self.sort2elems[elem_sort]

    def get_dependent_sets(self, set_sort):
        return self.sort2elems[set_sort]

    def get_dependent_elements_in_set(self, set_sort, set_id):
        return self.dep_types[set_sort].get_elements_in_set(set_id)

    def get_pretty_set(self, set_sort, set_id):
        # e.g. quorum_node0_node1
        elems_in_set = self.get_dependent_elements_in_set(set_sort, set_id)
        label_header = self.get_sort_name_from_finite_sort(set_sort)
        labels = []
        for elem in elems_in_set:
            labels.append(printer.pretty_print_enum_constant(elem))
        labels.sort()
        labels = [label_header] + labels
        return set_delim.join(labels)

    def get_pretty_elements_of_dependent_sort(self, set_sort):
        num_sets   = self.get_sort_size(set_sort) 
        sort_elems = []
        for set_id in range(num_sets):
            sort_elems.append(self.get_pretty_set(set_sort, set_id))
        return sort_elems
    
    def get_pretty_elements_of_non_dependent_sort(self, sort):
        sort_elems = self.sort2elems[sort]
        sort_elems = [printer.pretty_print_enum_constant(elem) for elem in sort_elems]
        return sort_elems

    def get_pretty_elements_of_sort(self, sort_name):
        sort = self.get_finite_sort_from_sort_name(sort_name)
        if sort in self.dep_types:
            return self.get_pretty_elements_of_dependent_sort(sort)
        else:
            return self.get_pretty_elements_of_non_dependent_sort(sort)

    def get_pretty_set_substitution_map(self):
        subst = {}
        for set_sort in self.dep_types.keys():
            dep_sets = self.get_dependent_sets(set_sort)
            for set_id, dep_set in enumerate(dep_sets):
                subst[dep_set] = self.get_pretty_set(set_sort, set_id)
        return subst

    def get_dependent_axioms(self):
        axioms = []
        subst  = self.get_pretty_set_substitution_map()
        for set_sort in self.dep_types.keys():
            dep_relation = self.get_dependent_relation(set_sort)
            dep_sets     = self.get_dependent_sets(set_sort)
            dep_elems    = self.get_dependent_elements(set_sort)
            for set_id, dep_set in enumerate(dep_sets):
                elems_in_set   = self.get_dependent_elements_in_set(set_sort, set_id)
                for elem in dep_elems:
                    args = [elem, dep_set]
                    dep_symbol = Function(dep_relation, args)
                    if elem not in elems_in_set:
                        dep_symbol = Not(dep_symbol)
                    axioms.append(printer.pretty_print_str(dep_symbol, subst))
        return axioms

    def get_pretty_filtered_atoms(self, var_filter='non-global'):
        atoms = self._get_filtered_ground_atoms(var_filter)
        subst = self.get_pretty_set_substitution_map()
        pretty_atoms = []
        for atom in atoms:
            pretty_atoms.append(printer.pretty_print_str(atom, subst).replace(' ',''))
        return pretty_atoms
    
    def get_pretty_ivy_variables(self):
        atoms  = self._get_filtered_ground_atoms(var_filter='global')
        atoms += self._get_filtered_ground_atoms(var_filter='independent')
        subst = self.get_pretty_set_substitution_map()
        pretty_atoms = []
        for atom in atoms:
            pretty_atoms.append(printer.pretty_print_str(atom, subst).replace(' ',''))
        return pretty_atoms

    def get_pretty_parameterized_actions(self):
        actions = self._get_all_parameterized_actions()
        subst = self.get_pretty_set_substitution_map()
        pretty_actions = []
        for action in actions:
            pretty_actions.append(printer.pretty_print_str(action, subst).replace(' ',''))
        return pretty_actions 

def vmt_parse(options, vmt_filename): 
    tran_sys = TransitionSystem(options)
    with open(vmt_filename, 'r') as vmt_file:
        tran_sys.read_infinite_system_from_vmt(vmt_file)
        tran_sys.set_finite_system()
    return tran_sys  