
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

        self._symbol_name = str(symbol)
        self._action_name = f'get_{str(symbol)}'
        self._param_types_str = [f'{str(ptype)}_{pid}: {str(ptype)}' for pid, ptype in enumerate(param_types)]
        self._params_list     = [f'{str(ptype)}_{pid}' for pid, ptype in enumerate(param_types)]
        self._return_type_str = 'bool' if return_type.is_bool_type() else str(return_type)

    def get_header(self):
        line  = f'action {self._action_name}'
        line += f'({', '.join(self._param_types_str)})'
        line += f' returns(x: {self._return_type_str}) = ' 
        line += '{\n'
        return line

    def get_body(self):
        line = '    x := '
        line += f'{self._symbol_name}'
        if len(self.param_types):
            line += f'({', '.join(self._params_list)})'
        line += '\n'
        return line

    def get_export(self):
        line  = f'export {self._action_name}'
        line += '\n'
        return line

    def get_lines(self):
        lines = []
        lines.append(self.get_header())
        lines.append(self.get_body())
        lines.append('}\n')
        lines.append(self.get_export())
        return lines
        
class DfsStates():
    # static datas
    tran_sys : TransitionSystem
    options  : QrmOptions

    def __init__(self):
        self.finite_ivy_name = DfsStates.options.instance_name + '.' + DfsStates.options.instance_suffix + '.finite.ivy'
        self.access_actions  = {} # symbol to access action meta type
        self.lines           = []

    def _get_finite_sort_line(self, line, sort_name):
        sort_elems = DfsStates.tran_sys.get_finite_sort_elements_str(sort_name)
        line = line + ' = {' + ', '.join(sort_elems) + '}\n'
        return line

    def _read_source_ivy(self):
        source_ivy = open(DfsStates.options.ivy_filename, 'r')
        for line in source_ivy.readlines():
            if line.startswith('type'): # type sort
                line = line.strip('\n')
                sort = line.split(' ')[1]
                line = self._get_finite_sort_line(line, sort)
            self.lines.append(line)
        source_ivy.close()

    def _set_access_actions(self):
        symbols = DfsStates.tran_sys.get_predicates()
        for symbol in symbols:
            param_types = []
            return_type = None
            sym_type = symbol.symbol_type()
            if not sym_type.is_function_type():
                # case1: (start_node = n0)
                # case2: bool type, no parameters
                return_type = sym_type
            else: 
                # case3: predicate
                # case 4: function (predicate is a function with return type bool)
                param_types = list(sym_type._param_types)
                return_type = sym_type._return_type
            access_action = AccessAction(symbol, param_types, return_type)
            self.access_actions[symbol] = access_action

    def _append_comments(self):
        self.lines.append('\n')
        self.lines.append('### For DFS reachability ###\n')

    def _append_dep_axiom_lines(self):
        self.lines.append('\n')
        self.lines.append('## Dependent relation axioms ##\n')
        axioms = DfsStates.tran_sys.get_dep_axioms()
        for axiom in axioms:
            self.lines.append('axiom ' +axiom+'\n')

    def _append_access_action_lines(self):
        self.lines.append('\n')
        self.lines.append('## Access actions ##\n')
        for access_action in self.access_actions.values():
            for line in access_action.get_lines():
                self.lines.append(line)
            self.lines.append('\n')

    def _write_finite_ivy(self):
        finite_ivy = open(self.finite_ivy_name, 'w')
        for line in self.lines:
            finite_ivy.write(line)
        finite_ivy.close()

    def initialize(self):
        self._read_source_ivy()
        self._set_access_actions()
        self._append_comments()
        self._append_dep_axiom_lines()
        self._append_access_action_lines()
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