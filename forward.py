
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
from finite_ivy import FiniteIvyGenerator, FiniteIvyExecutor
import repycudd

class DfsStates():
    def __init__(self,  tran_sys : TransitionSystem, options : QrmOptions):
        self.tran_sys = tran_sys
        self.options  = options

        self.dfs_state_vars  = []
        self.dfs_global_vars = []
        self.ivy_actions     = []
        self.ivy_state_vars  = []

        self.protocol        = None
        self.ivy_executor    = None

        self.global_state    = []
        self.sym_reduced_reachable_states = set()
        
    def _init_state_variables(self):
        self.dfs_state_vars  = self.tran_sys.get_pretty_filtered_atoms(var_filter='non-global')
        self.dfs_global_vars = self.tran_sys.get_pretty_filtered_atoms(var_filter='global')
        self.ivy_state_vars  = self.tran_sys.get_pretty_ivy_variables()
        self.ivy_actions = self.tran_sys.get_pretty_parameterized_actions()

    def _init_protocol(self):
        self.protocol = Protocol(self.options)                
        self.protocol.initialize_from_transition_system(self.tran_sys, self.dfs_state_vars)

    def _init_finite_ivy_generator(self):
        FiniteIvyGenerator.set_transition_system(self.tran_sys)
        FiniteIvyGenerator.set_options(self.options)
        FiniteIvyGenerator.set_path_and_file_names()
        FiniteIvyGenerator.set_state_var_to_access_action()
        FiniteIvyGenerator.set_state_variables(self.protocol.element_Name2Id, self.ivy_state_vars)
        FiniteIvyGenerator.write_ivy()
        FiniteIvyGenerator.compile_finite_ivy_to_cpp()
        FiniteIvyGenerator.build_ivy_exec_python_module()

    def initialize(self):
        self._init_state_variables()
        self._init_protocol()
        self._init_finite_ivy_generator() 

    def _add_new_reachable_state_orbit(self, state):
        # TODO: symmetric oribt
        self.sym_reduced_reachable_states.add(state)

    def symmetry_aware_depth_first_search_reachability(self):
        self.ivy_executor = FiniteIvyExecutor(self.dfs_state_vars, self.dfs_global_vars, self.ivy_state_vars) 
        self.global_state = self.ivy_executor.get_dfs_global_state()
        initial_state     = self.ivy_executor.get_dfs_state()
        self._add_new_reachable_state(initial_state)

    def clean(self):
        FiniteIvyGenerator.clean()

    def solve_reachability(self):
        self.initialize()
        self.symmetry_aware_depth_first_search_reachability()
        self.clean()

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