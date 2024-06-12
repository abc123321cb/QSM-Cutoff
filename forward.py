
import os
import subprocess
from typing import List
from frontend.fr import *
from frontend.problem import *
from util import FormulaPrinter as printer 
from util import QrmOptions
from vmt_parser import TransitionSystem
from protocol import Protocol, Reachability
from verbose import *
from finite_ivy import IvyAccessAction, FiniteIvy
import repycudd

class DfsStates():
    def __init__(self,  tran_sys : TransitionSystem, options : QrmOptions):
        self.var2access_action = {} # state variable symbol to access action meta type
        self.tran_sys = tran_sys
        self.options  = options
        self.protocol = None
        self.state_vars    = []
        self.global_vars   = []
        self.ivy_exec_name = ''
        
    def _init_access_actions(self):
        state_vars = self.tran_sys.get_state_variables()
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
            access_action = IvyAccessAction(var, param_types, return_type)
            self.var2access_action[var] = access_action

    def _init_state_variables(self):
        self.state_vars  = self.tran_sys.get_pretty_filtered_atoms(var_filter='non-global')
        self.global_vars = self.tran_sys.get_pretty_filtered_atoms(var_filter='global')

    def _init_protocol(self):
        self.protocol = Protocol(self.options)                
        self.protocol.initialize_from_transition_system(self.tran_sys, self.state_vars)

    def _init_finite_ivy(self):
        FiniteIvy.set_transition_system(self.tran_sys)
        FiniteIvy.set_options(self.options)
        FiniteIvy.set_path_and_file_names()
        FiniteIvy.set_state_var_to_access_action(self.var2access_action)
        FiniteIvy.write_ivy()
        FiniteIvy.compile_finite_ivy_to_cpp()
        FiniteIvy.relocate_compilation_results()
        self.ivy_exec_name = FiniteIvy.executable_name

    def initialize(self):
        self._init_access_actions()
        self._init_state_variables()
        self._init_protocol()
        self._init_finite_ivy()

    def solve_reachability(self):
        self.initialize()

    def get_protocol(self):
        return self.protocol

def get_forward_reachability(tran_sys_orig, tran_sys, options:QrmOptions) -> FR:
    # dfs
    dfs = DfsStates(tran_sys, options)
    dfs.solve_reachability()

    # forward reachability
    fr_solver = FR(tran_sys_orig)
    set_problem(fr_solver)
    (atoms, states) = fr_solver.solve_reachability()
    subst = tran_sys.get_pretty_set_substitution_map()
    reach = Reachability(atoms, states, subst)
    fr_solver.reset() 
    return reach