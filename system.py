from pysmt.shortcuts import Symbol
from util import FormulaUtility as futil

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

class InfiniteSystem(System):
    def __init__(self):
        System.__init__(self)

    def read_init(self, fmla):
        self.init.add(fmla)

    def read_axiom(self, fmla, annot_list): 
        assert(len(annot_list) == 1)
        if (fmla.is_and()):
            for arg in fmla.args():
                self.axioms.add(arg)
        else:
            self.axioms.add(fmla)

    def read_action(self, fmla, annot_list):
        assert(len(annot_list) == 1)
        action_name = annot_list[0]
        action      = fmla
        if action.is_exists():
            qvars = action.quantifier_vars()
            for qvar in qvars:
                self.symbols.add(qvar)
                self.non_state_symbols.add(qvar)
            action = action.arg(0)
        self.actions.append([action, action_name, fmla])

    def read_invariant_property(self, fmla, annot_list):
        assert(len(annot_list) == 1)
        clauses = futil.flatten_and(fmla)
        for clause in clauses:
            self.invar_props.add(clause)

    def read_state(self, fmla, annot_list):
        assert(len(annot_list) == 1)
        next_name = annot_list[0]
        if fmla.is_function_application():
            prev_sym = fmla.function_name()
        else:
            prev_sym = fmla 
        self.states.add(prev_sym)
        next_sym = Symbol(next_name, prev_sym.symbol_type())
        self.next_states.add(next_sym)
        self.prev2next[prev_sym] = next_sym
        self.next2prev[next_sym] = prev_sym

    def add_leq_symbol(self, prev_symbol, prev_type, param_types):
        if (len(param_types) == 2 and prev_type.return_type.is_bool_type() and param_types[0] == param_types[1]):
            prev_name = str(prev_symbol)
            if prev_name == 'le' or prev_name.endswith('.le') or prev_name.startswith('le_'):
                self.leq_symbols.add(prev_symbol)

    def read_global_symbol(self, fmla, annot_list):
        assert(len(annot_list) == 1)
        if fmla.is_function_application():
            prev_symbol = fmla.function_name()
            prev_type   = prev_symbol.symbol_type()
            param_types = prev_type.param_types
            self.add_leq_symbol(prev_symbol, prev_type, param_types)
        else:
            prev_symbol = fmla 
        self.global_symbols.add(prev_symbol)
        self.states.add(prev_symbol)
        self.next_states.add(prev_symbol)

    def read_definitions(self, fmla, annot_list):
        assert(len(annot_list) == 1)
        defn_name = annot_list[0]
        self.definitions[defn_name] = fmla 

    def read_declared_symbols(self, script):
        symbols = script.get_declared_symbols()
        for sym in symbols:
            self.symbols.add(sym)
            if sym not in self.states and sym not in self.next_states:
                self.non_state_symbols.add(sym)

class FiniteSystem(System):
    def __init__(self):
        System.__init__(self)

    def set_reference(self, infinite_system):
        self.infinite_system = infinite_system

    def set_finitized_init(self):
        self.init = set()
        for init in self.infinite_system.init:
            self.init.add(init.fsubstitute())

    def set_finitized_axioms(self):
        self.axioms = set()
        for axiom in self.infinite_system.axioms:
            self.axioms.add(axiom.fsubstitute())

    def set_finitized_actions(self):
        self.actions = list()
        for action in self.infinite_system.actions:
            fin_action = []
            fin_action.append(action[0].fsubstitute())
            fin_action.append(action[1])
            fin_action.append(action[2].fsubstitute())
            self.actions.append(fin_action)

    def set_finitized_invariant_properties(self):
        self.invar_props = set()
        for invar_prop in self.infinite_system.invar_props:
            self.invar_props.add(invar_prop.fsubstitute())

    def set_finitized_definitions(self):
        self.definitions = dict()
        for defn_name, fmla in self.infinite_system.definitions.items():
            self.definitions[defn_name] = fmla.fsubstitute()

    def set_finitized_states(self):
        self.states = set()
        for state in self.infinite_system.states:
            self.states.add(state.fsubstitute())
    
    def set_finitized_next_states(self):
        self.next_states = set()
        for next_state in self.infinite_system.next_states:
            self.next_states.add(next_state.fsubstitute())

    def set_finitized_symbols(self):
        self.symbols = set()
        for sym in self.infinite_system.symbols:
            self.symbols.add(sym.fsubstitute())

    def set_finitized_non_state_symbols(self):
        self.non_state_symbols = set()
        for sym in self.infinite_system.non_state_symbols:
            self.non_state_symbols.add(sym.fsubstitute())
    
    def set_finitized_global_symbols(self):
        self.global_symbols = set()
        for symbol in self.infinite_system.global_symbols:
            self.global_symbols.add(symbol.fsubstitute())

    def set_finitized_leq_symbols(self):
        self.leq_symbols = set()
        for symbol in self.infinite_system.leq_symbols:
            self.leq_symbols.add(symbol.fsubstitute())

    def set_finitized_prev_to_next(self):
        self.prev2next = dict()
        for prev_sym, next_sym in self.infinite_system.prev2next.items():
            self.prev2next[prev_sym.fsubstitute()] = next_sym.fsubstitute()

    def set_finitized_next_to_prev(self):
        self.next2prev = dict()
        for next_sym, prev_sym in self.infinite_system.next2prev.items():
            self.next2prev[next_sym.fsubstitute()] = prev_sym.fsubstitute()