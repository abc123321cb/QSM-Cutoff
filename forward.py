
import os
import subprocess
from typing import List
from frontend.fr import *
from frontend.problem import *
from util import FormulaPrinter as printer 
from util import QrmOptions
from vmt_parser import TransitionSystem
import repycudd

class AccessAction():
    def __init__(self, symbol, param_types, return_type):
        self.symbol      = symbol
        self.param_types = param_types 
        self.return_type = return_type

        self._symbol_name     = str(symbol)
        self._action_name     = f'get_{str(symbol)}'
        self._param_types_str = [f'{str(ptype)}_{pid}: {str(ptype)}' for pid, ptype in enumerate(param_types)]
        self._params_list     = [f'{str(ptype)}_{pid}' for pid, ptype in enumerate(param_types)]
        self._return_type_str = 'bool' if return_type.is_bool_type() else str(return_type)

    def _get_action_header(self):
        line  = f'action {self._action_name}'
        if len(self.param_types):
            line += f'({', '.join(self._param_types_str)})'
        line += f' returns(x: {self._return_type_str}) = ' 
        line += '{\n'
        return line

    def _get_action_body(self):
        line = '    x := '
        line += f'{self._symbol_name}'
        if len(self.param_types):
            line += f'({', '.join(self._params_list)})'
        line += '\n'
        return line

    def _get_action_end(self):
        return '}\n'

    def _get_export_action(self):
        line  = f'export {self._action_name}'
        line += '\n'
        return line

    def get_action_lines(self):
        lines = []
        lines.append(self._get_action_header())
        lines.append(self._get_action_body())
        lines.append(self._get_action_end())
        lines.append(self._get_export_action())
        return lines

class FiniteIvy():
    # static datas
    tran_sys : TransitionSystem
    options  : QrmOptions
    finite_ivy_name     = ''
    lines               = []
    var2access_action = {}

    @staticmethod
    def _reset():
        FiniteIvy.finite_ivy_name = FiniteIvy.options.instance_name + '.' + FiniteIvy.options.instance_suffix + '.finite.ivy'
        FiniteIvy.lines           = []

    def _get_finite_sort_line(line, sort_name):
        sort_elems = FiniteIvy.tran_sys.get_pretty_elements_of_sort(sort_name)
        line = line + ' = {' + ', '.join(sort_elems) + '}\n'
        return line

    def _set_lines_from_source_ivy():
        source_ivy = open(FiniteIvy.options.ivy_filename, 'r')
        for line in source_ivy.readlines():
            if line.startswith('type'): # type sort
                line = line.strip('\n')
                sort = line.split(' ')[1]
                line = FiniteIvy._get_finite_sort_line(line, sort)
            FiniteIvy.lines.append(line)
        source_ivy.close()

    def _add_comment_lines():
        FiniteIvy.lines.append('\n')
        FiniteIvy.lines.append('### For DFS reachability ###\n')

    def _add_dependent_sort_axiom_lines():
        FiniteIvy.lines.append('\n')
        FiniteIvy.lines.append('## Dependent relation axioms ##\n')
        axioms = DfsStates.tran_sys.get_dependent_axioms()
        for axiom in axioms:
            FiniteIvy.lines.append('axiom ' +axiom+'\n')

    def _add_access_action_lines():
        FiniteIvy.lines.append('\n')
        FiniteIvy.lines.append('## Access actions ##\n')
        for access_action in FiniteIvy.var2access_action.values():
            for line in access_action.get_action_lines():
                FiniteIvy.lines.append(line)
            FiniteIvy.lines.append('\n')

    def _write_lines_to_finite_ivy():
        finite_ivy = open(FiniteIvy.finite_ivy_name, 'w')
        for line in FiniteIvy.lines:
            finite_ivy.write(line)
        finite_ivy.close()

    def set_transition_system(tran_sys : TransitionSystem):
        FiniteIvy.tran_sys = tran_sys

    def set_options(options : QrmOptions):
        FiniteIvy.options  = options

    def set_state_var_to_access_action(var2access_action):
        FiniteIvy.var2access_action = var2access_action

    def write_ivy():
        FiniteIvy._reset()
        FiniteIvy._set_lines_from_source_ivy()
        FiniteIvy._add_comment_lines()
        FiniteIvy._add_dependent_sort_axiom_lines()
        FiniteIvy._add_access_action_lines()
        FiniteIvy._write_lines_to_finite_ivy()

class DfsStates():
    # static datas
    tran_sys : TransitionSystem
    options  : QrmOptions

    def __init__(self):
        self.var2access_action = {} # state variable symbol to access action meta type
        
    def _set_access_actions(self):
        state_vars = DfsStates.tran_sys.get_state_variables()
        for var in state_vars:
            param_types = []
            return_type = None
            var_type = var.symbol_type()
            if not var_type.is_function_type():
                # case1: (start_node = n0)
                # case2: bool type, no parameters
                return_type = var_type 
            else: 
                # case3: predicate
                # case 4: function (predicate is a function with return type bool)
                param_types = list(var_type._param_types)
                return_type = var_type._return_type
            access_action = AccessAction(var, param_types, return_type)
            self.var2access_action[var] = access_action

    def _write_finite_ivy(self):
        FiniteIvy.set_transition_system(DfsStates.tran_sys)
        FiniteIvy.set_options(DfsStates.options)
        FiniteIvy.set_state_var_to_access_action(self.var2access_action)
        FiniteIvy.write_ivy()

    def initialize(self):
        self._set_access_actions()
        self._write_finite_ivy()

    def solve_reachability(self):
        self.initialize()

    @staticmethod
    def setup(tran_sys : TransitionSystem, options : QrmOptions):
        DfsStates.tran_sys = tran_sys
        DfsStates.options  = options

class Reachability():
    def __init__(self, atoms, states) -> None:
        self.atoms  = atoms     # type : List[formula] 
        self.states = states    # type : List[str] 
                                # each state in states is string consisting of '0', '1', '-' 
        self.stvars = []        # type: List[str]
        for atom in self.atoms:
            self.stvars.append(printer.pretty_print_str(atom).replace(' ',''))

def get_forward_reachability(tran_sys_orig, tran_sys, options:QrmOptions) -> FR:
    # dfs
    DfsStates.setup(tran_sys, options)
    dfs = DfsStates()
    dfs.solve_reachability()
    # forward reachability
    fr_solver = FR(tran_sys_orig)
    set_problem(fr_solver)
    (atoms, states) = fr_solver.solve_reachability()
    reach = Reachability(atoms, states)
    fr_solver.reset() 
    return reach