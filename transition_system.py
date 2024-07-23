from itertools import combinations as combinations
from ivy_parser import parse_ivy
from ivy import ivy_logic as il
from ivy import ivy_utils as iu
from ivy import ivy_logic_utils as ilu
from ivy import ivy_actions as ia
from util import QrmOptions, SET_DELIM
from verbose import *

#*************************************************************************
# utils 
#*************************************************************************
registered_dependent_relations           = {}
registered_dependent_relations['member'] = lambda elem_size : int(elem_size/2)+1 # member selection function
set_delim = SET_DELIM

#*************************************************************************
# helpers 
#*************************************************************************

def get_enum_constant_names(sort_str, size):
    enum_const_names = []
    for i in range(size):
        const_name = sort_str + str(i)
        enum_const_names.append(const_name)
    return enum_const_names

def get_enum_sort(sort_str, enum_const_names):
    enum_sort = il.EnumeratedSort(sort_str,enum_const_names)
    return enum_sort

def get_enum_constants(enum_sort):
    return enum_sort.constructors

#*************************************************************************
# class: DependentType
#*************************************************************************
class DependentType():
    # static data
    def __init__(self, dep_relation, set_sort, elem_sort, constants, select_func):
        self.dep_relation = dep_relation  # e.g. "member"
        self.set_sort     = set_sort      # e.g. "quorum"
        self.elem_sort    = elem_sort     # e.g. "node"
        self.sets         = []            # e.g. 0 -> [node0,node1], 1 -> [node0,node2], 2 -> [node1,node2] .....
        select_domain_size = len(constants)
        select_domain      = list(range(select_domain_size))
        selections         = list(combinations(select_domain, select_func(select_domain_size)))
        for selection in selections:
            # e.g. quorum_node0_node1 : [node0, node1]
            elems_in_set = [constants[const_id] for const_id in selection]
            label_header = set_sort.name
            labels = []
            for elem in elems_in_set:
                labels.append(str(elem))
            labels.sort()
            labels = [label_header] + labels
            set_label = set_delim.join(labels)
            self.sets.append((set_label, elems_in_set))

    def get_elements_in_set(self, set_id):
        return  self.sets[set_id][1]
    
    def get_set_label(self, set_id):
        return  self.sets[set_id][0]

#*************************************************************************
# class: TransistionSystem
#*************************************************************************
class TransitionSystem():
    def __init__(self, options : QrmOptions, ivy_module):
        # helpers
        self.options    = options
        self.ivy_module = ivy_module
        # sorts
        self.sorts            = dict() # sort name to sort of finite domain size
        self.sort2consts      = dict() # finite sort to its finite domain of constants
        self.sort_fin2inf     = dict() # finit sort to infinite sort
        self.sort_inf2fin     = dict() # infinite sort to enumsort
        # symbols & formulas
        self.symbols          = set()  # all declared symbols
        self.definitions      = dict() # definition symbols to Definition ast
        self.axiom_fmla       = None 
        self.axiom_symbols    = set()  # globally unchanged symbols, e.g. member, le
        self.state_symbols    = set()  # state variables (symbols that are non-axiom symbols)
        # dependent sorts
        self.dep_types        = dict() # "quorum" to quorum meta data (e.g. "member", "node" ...) 
        self.pretty_set_sort_subst = {}
        # actions
        self.exported_actions = []

        self._initialize()

    def _init_sort(self, sort_str, sort, size):
        assert(size > 0)
        enum_const_names = get_enum_constant_names(sort_str, size)
        enum_sort        = get_enum_sort(sort_str, enum_const_names)
        enum_consts      = get_enum_constants(enum_sort)
        self.sorts[sort_str]         = enum_sort
        self.sort2consts[enum_sort]  = enum_consts
        self.sort_inf2fin[sort]      = enum_sort
        self.sort_fin2inf[enum_sort] = sort

    def _init_sorts(self):
        for sort_str, sort in self.ivy_module.sig.sorts.items():
            if sort_str == 'bool':
                continue
            if not isinstance(sort,il.UninterpretedSort):
                raise iu.IvyError(None,f'Cannot handle interprested sort {sort}')
            if sort_str in self.options.sizes:
                size = self.options.sizes[sort_str]
            if size > 0:
                self._init_sort(sort_str, sort, size)

    def _init_symbols(self):
        for symbol in self.ivy_module.sig.symbols.values():
            if symbol in self.symbols:
                continue
            if isinstance(symbol.sort, il.UnionSort):
                raise iu.IvyError(None,f'Cannot handle unionsort symbol {symbol}')
            finite_symbol = ilu.resort_symbol(symbol, self.sort_inf2fin)
            self.symbols.add(finite_symbol)

    def _init_definitions(self):
        for update in self.ivy_module.updates:
            if type(update) == ia.DerivedUpdate:
                defn = update.defn
                finite_defn = ilu.resort_ast(defn, self.sort_inf2fin)
                self.definitions[finite_defn.defines()] = finite_defn

    def _init_axioms(self):
        fmlas = []
        for fmla in self.ivy_module.axioms:
            fmlas.append(fmla)
        axiom_fmla = il.And(*fmlas) 
        axiom_fmla = ilu.resort_ast(axiom_fmla, self.sort_inf2fin)
        self.axiom_fmla = axiom_fmla
        self.axiom_symbols.update(ilu.used_symbols_ast(axiom_fmla))

    def _init_state_symbols(self):
        for symbol in self.symbols:
            if symbol not in self.axiom_symbols:
                self.state_symbols.add(symbol)

    def _get_dependent_set_sort(self, dep_relation):
        assert(len(dep_relation.sort.dom) == 2)
        set_sort  = dep_relation.sort.dom[1]
        return set_sort

    def _get_dependent_element_sort(self, dep_relation):
        assert(len(dep_relation.sort.dom) == 2)
        elem_sort = dep_relation.sort.dom[0]
        return elem_sort
    
    def _instantiate_dependent_types(self):
        for symbol in self.axiom_symbols:
            if str(symbol) in registered_dependent_relations:
                dep_relation = symbol 
                select_func  = registered_dependent_relations[str(symbol)]
                elem_sort    = self._get_dependent_element_sort(dep_relation)
                set_sort     = self._get_dependent_set_sort(dep_relation)
                elem_consts  = self.sort2consts[elem_sort]
                dep_type     = DependentType(dep_relation, set_sort, elem_sort, elem_consts, select_func)
                self.dep_types[set_sort] = dep_type

    def _init_exported_actions(self):
        exports = set([str(export) for export in self.ivy_module.exports])
        for action_name, action in self.ivy_module.actions.items():
            if action_name in exports:
                param_sorts = [ilu.resort_symbol(param, self.sort_inf2fin).sort for param in action.formal_params]
                action_func_sort = il.FunctionSort(*param_sorts, il.BooleanSort())
                action_symbol    = il.Symbol(action_name, action_func_sort)
                self.exported_actions.append(action_symbol)

    def _init_pretty_set_substitution_map(self):
        pretty_set_names = []
        for set_sort in self.dep_types.keys():
            dep_sets = self.get_dependent_sets(set_sort)
            for set_id, dep_set in enumerate(dep_sets):
                pretty_set_names.append(self.get_set_label(set_sort, set_id))
            pretty_enum_sort   = il.EnumeratedSort(self.get_sort_name_from_finite_sort(set_sort), pretty_set_names)
            self.pretty_set_sort_subst[set_sort] = pretty_enum_sort

    def _update_pretty_set(self):
        # sorts
        sorts = self.sorts.copy()
        self.sorts  = {}
        for sort_str, sort in sorts.items():
            if sort in self.pretty_set_sort_subst:
                sort = self.pretty_set_sort_subst[sort]
            self.sorts[sort_str] = sort
        sort2consts = self.sort2consts.copy()
        self.sort2consts = {}
        for sort, consts in sort2consts.items():
            if sort in self.pretty_set_sort_subst:
                sort   = self.pretty_set_sort_subst[sort]
                consts = sort.constructors
            self.sort2consts[sort] = consts
        sort_fin2inf = self.sort_fin2inf.copy()
        self.sort_fin2inf = {}
        for fin_sort, inf_sort in sort_fin2inf.items():
            if fin_sort in self.pretty_set_sort_subst:
                fin_sort = self.pretty_set_sort_subst[fin_sort]
            self.sort_fin2inf[fin_sort] = inf_sort
        sort_inf2fin = self.sort_inf2fin.copy()
        self.sort_inf2fin = {}
        for inf_sort, fin_sort in sort_inf2fin.items():
            if fin_sort in self.pretty_set_sort_subst:
                fin_sort = self.pretty_set_sort_subst[fin_sort]
            self.sort_inf2fin[inf_sort] = fin_sort
        # symbols & formulas
        symbols = self.symbols.copy()
        self.symbols = set()
        for symbol in symbols:
            self.symbols.add(ilu.resort_symbol(symbol, self.pretty_set_sort_subst))
        definitions = self.definitions.copy() 
        self.definitions = {}
        for defn in definitions.values():
            defn = ilu.resort_ast(defn, self.pretty_set_sort_subst)
            self.definitions[defn.defines()] = defn
        self.axiom_fmla = ilu.resort_ast(self.axiom_fmla, self.pretty_set_sort_subst)
        axiom_symbols = self.axiom_symbols.copy()
        self.axiom_symbols = set()
        for axiom_symbol in axiom_symbols:
            self.axiom_symbols.add(ilu.resort_symbol(axiom_symbol, self.pretty_set_sort_subst))
        state_symbols = self.state_symbols.copy()
        self.state_symbols = set()  
        for state_symbol in state_symbols:
            self.state_symbols.add(ilu.resort_symbol(state_symbol, self.pretty_set_sort_subst))
        # dependent sorts
        dep_types = self.dep_types.copy()
        self.dep_types = dict() # "quorum" to quorum meta data (e.g. "member", "node" ...) 
        for set_sort, dep_type in dep_types.items():
            set_sort = self.pretty_set_sort_subst[set_sort]
            dep_relation = ilu.resort_symbol(dep_type.dep_relation, self.pretty_set_sort_subst)
            dep_type.set_sort     = set_sort
            dep_type.dep_relation = dep_relation
            self.dep_types[set_sort] = dep_type
        # actions
        exported_actions = self.exported_actions.copy()
        self.exported_actions = []
        for action in exported_actions:
            self.exported_actions.append(ilu.resort_symbol(action, self.pretty_set_sort_subst))

    def _initialize(self):
        with self.ivy_module.theory_context():
            self._init_sorts()
            self._init_symbols()
            self._init_definitions()
            self._init_axioms()
            self._init_state_symbols()
            self._instantiate_dependent_types()
            self._init_exported_actions()
            self._init_pretty_set_substitution_map()
            self._update_pretty_set()

    #------------------------------------------------------------
    # TransitionSystem: public access methods
    #------------------------------------------------------------
    def get_sort_name_from_finite_sort(self, sort):
        return sort.name

    def get_finite_sort_from_sort_name(self, sort_name):
        return self.sorts[sort_name]

    def get_state_variables(self):
        return self.state_symbols 

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
        return self.sort2consts[elem_sort]

    def get_dependent_sets(self, set_sort):
        return self.sort2consts[set_sort]

    def get_dependent_elements_in_set(self, set_sort, set_id):
        return self.dep_types[set_sort].get_elements_in_set(set_id)

    def get_set_label(self, set_sort, set_id):
        # e.g. quorum_node0_node1
        return self.dep_types[set_sort].get_set_label(set_id)

    def get_sort_constants_str(self, sort):
        consts = self.sort2consts[sort]
        consts_str = [str(const) for const in consts]
        return consts_str

    def get_dependent_axioms_fmla(self):
        axioms = []
        for set_sort in self.dep_types.keys():
            dep_relation = self.get_dependent_relation(set_sort)
            dep_sets     = self.get_dependent_sets(set_sort)
            dep_elems    = self.get_dependent_elements(set_sort)
            for set_id, dep_set in enumerate(dep_sets):
                elems_in_set   = self.get_dependent_elements_in_set(set_sort, set_id)
                for elem in dep_elems:
                    args = [elem, dep_set]
                    dep_symbol = il.apply(dep_relation, args)
                    if elem not in elems_in_set:
                        dep_symbol = il.Not(dep_symbol)
                    axioms.append(dep_symbol)
        return axioms

    def get_dependent_axioms_str(self):
        axioms = self.get_dependent_axioms_fmla() 
        axioms = [str(axiom) for axiom in axioms]
        return axioms

def get_transition_system(options, ivy_filename): 
    module   = parse_ivy(options, ivy_filename)
    tran_sys = TransitionSystem(options, module)
    return tran_sys  