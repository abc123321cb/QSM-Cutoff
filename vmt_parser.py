from __future__ import print_function
import sys
from pysmt.smtlib.parser import SmtLibParser
from pysmt.shortcuts import Symbol, Not, Enum
from pysmt.typing import EnumType
from pysmt.environment import get_env

from util import FormulaPrinter as printer
from util import SORT_SUFFIX
from verbose import *

registered_dependent_relations           = {}
registered_dependent_relations['member'] = lambda elem_size : int(elem_size/2)+1 # member selection function

# utils
def flatten_or(cube):
    flat = set()
    cube_flat = cube
        
    if (cube_flat.is_or()):
        for arg in cube_flat.args():
            for flat_arg in flatten_or(arg):
                flat.add(flat_arg)
    else:
        flat.add(cube_flat)
    return flat

def flatten_and(formula):
    flat = set()
    if (formula.is_and()):
        for arg in formula.args():
            for flat_arg in flatten_and(arg):
                flat.add(flat_arg)
    elif (formula.is_not()):
        formulaNeg = formula.arg(0)
        if formulaNeg.is_or():
            for arg in formulaNeg.args():
                for flat_arg in flatten_or(arg):
                    flat.add(Not(flat_arg))
        else:
            flat.add(formula)
    else:
        flat.add(formula)
    return flat

class DependentType():
    def __init__(self, dep_relation, set_sort, elem_sort, elem_size, select_func):
        self.dep_relation = dep_relation  # e.g. "member"
        self.set_sort     = set_sort      # e.g. "quorum"
        self.elem_sort    = elem_sort     # e.g. "node"
        self.sets         = []            # e.g. 0 -> [0,1], 1 -> [0,2], 2 -> [1,2] .....
        from itertools import combinations
        select_space  = list(range(elem_size))
        selections    = list(combinations(select_space, select_func(elem_size)))
        for selection in selections:
            self.sets.append(list(selection))

class System():
    def __init__(self):
        # formulas
        self.init              = set()
        self.axioms            = set()
        self.actions           = list()
        self.invar_props       = set()   # invariant properties
        self.definitions       = dict()
        # symbols
        self.states            = set()   # state variable with prefix '__' in name
        self.next_states       = set()   # state variable without prefix '__' in name
        self.symbols           = set()   # all declared symbols
        self.non_state_symbols = set()   # all declared symbols except states/next_states
        self.global_symbols    = set()   # globally unchanged symbols, e.g. member, le
        self.leq_symbols       = set()   # the symbol representing "<="
        # transitions
        self.prev2next         = dict()
        self.next2prev         = dict()

class TransitionSystem(SmtLibParser):
    def __init__(self, options, env=None, interactive=False):
        # helpers
        self.options    = options
        self._parser    = SmtLibParser(env,interactive)
        # data
        self.infinite_sorts  = set()    # sort of infinite size
        self.sort2elems      = dict()   # finite sort to finite set of elements
        self.sort2qvars      = dict()   # finit sort to quantified variables
        self.sort_fin2inf    = dict()   # finit sort to infinite sort
        self.sort_inf2fin    = dict()   # infinite sort to enumsort
        self.infinite_system = System() # original infinite system from vmt
        self.finite_system   = System() # finitized system 
        self._idx = 0                   # subscript for enum type
        # dependent sorts
        self.dep_types       = dict()   # "quorum" to quorum meta data (e.g. "member", "node" ...) 

    # helper functions
    def _get_enum_element_names(self, sort, size):
        enum_elem_names = []
        sort_suffix = SORT_SUFFIX + str(self._idx) + ':'
        for i in range(size):
            # create the symbol of one finite element of sort
            symbol_name = str(sort) + ':f' + str(i)
            symbol      = Symbol(symbol_name, sort)
            elem_name   = str(sort) + sort_suffix + str(i)
            enum_elem_names.append(elem_name)
        return enum_elem_names
    
    def _get_enum_sort(self, sort, enum_elem_names):
        sort_suffix = SORT_SUFFIX + str(self._idx) + ':'
        enum_sort_name = str(sort) + sort_suffix
        enum_sort      = EnumType(enum_sort_name,  enum_elem_names)
        return enum_sort

    def _get_enum_elements(self, enum_sort, enum_elem_names):
        enum_elems = []
        for elem_name in enum_elem_names:
            elem = Enum(elem_name, enum_sort)
            enum_elems.append(elem)
        return enum_elems

    def _get_enum_qvars(self, enum_sort, enum_elem_names):
        enum_qvars = []
        for elem_name in enum_elem_names:
            qvar_name = 'Q:' + elem_name                
            qvar = Symbol(qvar_name, enum_sort)
            enum_qvars.append(qvar)
        return enum_qvars

    def _add_sort(self, sort, size):
        assert(size > 0)
        self.options.sizes[str(sort)] = size
        self.infinite_sorts.add(sort)
        enum_elem_names = self._get_enum_element_names(sort, size)
        enum_sort       = self._get_enum_sort(sort, enum_elem_names)
        enum_elems      = self._get_enum_elements(enum_sort, enum_elem_names)
        enum_qvars      = self._get_enum_qvars(enum_sort, enum_elem_names)
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

    def _read_init(self, fmla):
        self.infinite_system.init.add(fmla)

    def _read_axiom(self, fmla, annot_list): 
        assert(len(annot_list) == 1)
        if (fmla.is_and()):
            for arg in fmla.args():
                self.infinite_system.axioms.add(arg)
        else:
            self.infinite_system.axioms.add(fmla)

    def _read_action(self, fmla, annot_list):
        assert(len(annot_list) == 1)
        action_name = annot_list[0]
        action      = fmla
        if action.is_exists():
            qvars = action.quantifier_vars()
            for qvar in qvars:
                self.infinite_system.symbols.add(qvar)
                self.infinite_system.non_state_symbols.add(qvar)
            action = action.arg(0)
        self.infinite_system.actions.append([action, action_name, fmla])

    def _read_invariant_property(self, fmla, annot_list):
        assert(len(annot_list) == 1)
        clauses = flatten_and(fmla)
        for clause in clauses:
            self.infinite_system.invar_props.add(clause)

    def _read_state(self, fmla, annot_list):
        assert(len(annot_list) == 1)
        next_name = annot_list[0]
        if fmla.is_function_application():
            prev_sym = fmla.function_name()
        else:
            prev_sym = fmla 
        self.infinite_system.states.add(prev_sym)
        next_sym = Symbol(next_name, prev_sym.symbol_type())
        self.infinite_system.next_states.add(next_sym)
        self.infinite_system.prev2next[prev_sym] = next_sym
        self.infinite_system.next2prev[next_sym] = prev_sym

    def _add_leq_symbol(self, prev_symbol, prev_type, param_types):
        if (len(param_types) == 2 and prev_type.return_type.is_bool_type() and param_types[0] == param_types[1]):
            prev_name = str(prev_symbol)
            if prev_name == 'le' or prev_name.endswith('.le') or prev_name.startswith('le_'):
                self.infinite_system.leq_symbols.add(prev_symbol)

    def _read_global_symbol(self, fmla, annot_list):
        assert(len(annot_list) == 1)
        if fmla.is_function_application():
            prev_symbol = fmla.function_name()
            prev_type   = prev_symbol.symbol_type()
            param_types = prev_type.param_types
            self._add_leq_symbol(prev_symbol, prev_type, param_types)
        else:
            prev_symbol = fmla 
        self.infinite_system.global_symbols.add(prev_symbol)
        self.infinite_system.states.add(prev_symbol)
        self.infinite_system.next_states.add(prev_symbol)

    def _read_definitions(self, fmla, annot_list):
        assert(len(annot_list) == 1)
        defn_name = annot_list[0]
        self.infinite_system.definitions[defn_name] = fmla 

    def _read_declared_symbols(self, script):
        symbols = script.get_declared_symbols()
        for sym in symbols:
            self.infinite_system.symbols.add(sym)
            if sym not in self.infinite_system.states and sym not in self.infinite_system.next_states:
                self.infinite_system.non_state_symbols.add(sym)

    def _get_set_sort(self, dep_relation, inf2fin=False):
        dep_type = dep_relation.symbol_type()
        assert(len(dep_type.param_types) == 2)
        set_sort  = dep_type.param_types[1]
        if inf2fin:
            return self.sort_inf2fin[set_sort]
        return set_sort

    def _get_element_sort(self, dep_relation, inf2fin=False):
        dep_type = dep_relation.symbol_type()
        assert(len(dep_type.param_types) == 2)
        elem_sort = dep_type.param_types[0]
        if inf2fin:
            return self.sort_inf2fin[elem_sort]
        return elem_sort

    def _add_dependent_sorts(self):
        from math import comb 
        for symbol in self.infinite_system.global_symbols:
            if str(symbol) in registered_dependent_relations:
                dep_relation  = symbol 
                select_func   = registered_dependent_relations[str(symbol)]
                elem_sort     = self._get_element_sort(dep_relation, inf2fin=True) # finite
                elem_size     = self.get_sort_size(elem_sort)
                set_sort      = self._get_set_sort(dep_relation) # infinite
                self._add_sort(set_sort, comb(elem_size, select_func(elem_size)))

    def read_infinite_system_from_vmt(self, vmt_file):
        script = self._parser.get_script(vmt_file)
        annotations = script.annotations.get_annotations()

        for fmla, annot in annotations.items():
            for label, annot_set in annot.items():
                annot_list = list(annot_set)
                if   label == 'sort':
                    self._read_sort(fmla, annot_list)
                elif label == 'init':
                    self._read_init(fmla)
                elif label == 'axiom':
                    self._read_axiom(fmla, annot_list)
                elif label == 'action':
                    self._read_action(fmla, annot_list)
                elif label == 'invar-property':
                    self._read_invariant_property(fmla, annot_list)
                elif label == 'definition':
                    self._read_definitions(fmla, annot_list)
                elif label == 'next':
                    self._read_state(fmla, annot_list)
                elif label == 'global':
                    self._read_global_symbol(fmla, annot_list)
                else:
                    assert(0)
        self._read_declared_symbols(script)
        self._add_dependent_sorts()

    def _set_finitized_init(self):
        self.finite_system.init = set()
        for init in self.infinite_system.init:
            self.finite_system.init.add(init.fsubstitute())

    def _set_finitized_axioms(self):
        self.finite_system.axioms = set()
        for axiom in self.infinite_system.axioms:
            self.finite_system.axioms.add(axiom.fsubstitute())

    def _set_finitized_actions(self):
        self.finite_system.actions = list()
        for action in self.infinite_system.actions:
            fin_action = []
            fin_action.append(action[0].fsubstitute())
            fin_action.append(action[1])
            fin_action.append(action[2].fsubstitute())
            self.finite_system.actions.append(fin_action)

    def _set_finitized_invariant_properties(self):
        self.finite_system.invar_props = set()
        for invar_prop in self.infinite_system.invar_props:
            self.finite_system.invar_props.add(invar_prop.fsubstitute())

    def _set_finitized_definitions(self):
        self.finite_system.definitions = dict()
        for defn_name, fmla in self.infinite_system.definitions.items():
            self.finite_system.definitions[defn_name] = fmla.fsubstitute()

    def _set_finitized_states(self):
        self.finite_system.states = set()
        for state in self.infinite_system.states:
            self.finite_system.states.add(state.fsubstitute())
    
    def _set_finitized_next_states(self):
        self.finite_system.next_states = set()
        for next_state in self.infinite_system.next_states:
            self.finite_system.next_states.add(next_state.fsubstitute())

    def _set_finitized_symbols(self):
        self.finite_system.symbols = set()
        for sym in self.infinite_system.symbols:
            self.finite_system.symbols.add(sym.fsubstitute())

    def _set_finitized_non_state_symbols(self):
        self.finite_system.non_state_symbols = set()
        for sym in self.infinite_system.non_state_symbols:
            self.finite_system.non_state_symbols.add(sym.fsubstitute())
    
    def _set_finitized_global_symbols(self):
        self.finite_system.global_symbols = set()
        for symbol in self.infinite_system.global_symbols:
            self.finite_system.global_symbols.add(symbol.fsubstitute())

    def _set_finitized_leq_symbols(self):
        self.finite_system.leq_symbols = set()
        for symbol in self.infinite_system.leq_symbols:
            self.finite_system.leq_symbols.add(symbol.fsubstitute())

    def _set_finitized_prev_to_next(self):
        self.finite_system.prev2next = dict()
        for prev_sym, next_sym in self.infinite_system.prev2next.items():
            self.finite_system.prev2next[prev_sym.fsubstitute()] = next_sym.fsubstitute()

    def _set_finitized_next_to_prev(self):
        self.finite_system.next2prev = dict()
        for next_sym, prev_sym in self.infinite_system.next2prev.items():
            self.finite_system.next2prev[next_sym.fsubstitute()] = prev_sym.fsubstitute()

    def _instantiate_dependent_types(self):
        for symbol in self.infinite_system.global_symbols:
            if str(symbol) in registered_dependent_relations:
                dep_relation = symbol.fsubstitute() 
                select_func  = registered_dependent_relations[str(symbol)]
                elem_sort    = self._get_element_sort(dep_relation)
                set_sort     = self._get_set_sort(dep_relation)
                elem_size    = self.get_sort_size(elem_sort)
                dep_type     = DependentType(dep_relation, set_sort, elem_sort, elem_size, select_func)
                self.dep_types[set_sort] = dep_type

    def set_finite_system(self):
        get_env().fsubstituter.set_ssubs(self.sort_inf2fin, self._idx, False)
        self._instantiate_dependent_types()
        self._set_finitized_init()
        self._set_finitized_axioms()
        self._set_finitized_actions()
        self._set_finitized_invariant_properties()
        self._set_finitized_definitions()
        self._set_finitized_states()
        self._set_finitized_next_states()
        self._set_finitized_symbols()
        self._set_finitized_non_state_symbols()
        self._set_finitized_global_symbols()
        self._set_finitized_leq_symbols()
        self._set_finitized_prev_to_next()
        self._set_finitized_next_to_prev()
        self._idx += 1

    # public access functions 
    def get_sort_name_from_finite_sort(self, sort):
        return str(self.sort_fin2inf[sort])

    def get_predicates(self):
        return self.infinite_system.next_states

    def get_sort_size(self, sort):
        sort_name = self.get_sort_name_from_finite_sort(sort)
        sort_size = self.options.sizes[sort_name]
        return sort_size

    def get_dep_relation(self, set_sort):
        dep_type  = self.dep_types[set_sort]
        return dep_type.dep_relation

    def get_element_sort(self, set_sort):
        dep_type  = self.dep_types[set_sort]
        elem_sort = dep_type.elem_sort
        return elem_sort

    def get_elements(self, set_sort):
        elem_sort = self.get_element_sort(set_sort)
        return self.sort2elems[elem_sort]

    def get_sets(self, set_sort):
        return self.sort2elems[set_sort]

    def get_elements_in_set(self, set_sort, set_id):
        elements     = self.get_elements(set_sort)
        elem_indices = self.dep_types[set_sort].sets[set_id]
        elems_in_set = set()
        for elem_id in elem_indices:
            elems_in_set.add(elements[elem_id])
        return  elems_in_set 

    def get_set_label_with_id(self, set_sort, set_id):
        sets = self.get_sets(set_sort) 
        return printer.pretty_print_enum_constant(sets[set_id])

    def get_set_label_with_elements(self, set_sort, set_id, delim):
        # e.g. q-n1-n2
        elems_in_set = self.get_elements_in_set(set_sort, set_id)
        label_header = self.get_sort_name_from_finite_sort(set_sort)
        labels = []
        for elem in elems_in_set:
            labels.append(printer.pretty_print_enum_constant(elem))
        labels.sort()
        labels = [label_header] + labels
        return delim.join(labels)

def vmt_parse(options, vmt_filename): 
    tran_sys = TransitionSystem(options)
    with open(vmt_filename, 'r') as vmt_file:
        tran_sys.read_infinite_system_from_vmt(vmt_file)
        tran_sys.set_finite_system()
    return tran_sys  