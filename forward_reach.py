from typing import Type
from util import QrmOptions
from transition_system import TransitionSystem
from protocol import Protocol
from finite_ivy_instantiate import FiniteIvyInstantiator
from finite_ivy_gen import FiniteIvyGenerator
from finite_ivy_exec import FiniteIvyExecutor, IVY_ACTION_COMPLETE, IVY_ACTION_INCOMPLETE 
from verbose import *

class DfsNode():
    def __init__(self, dfs_state, ivy_state):
        self.dfs_state = dfs_state
        self.ivy_state = ivy_state

class ForwardReachability():
    #------------------------------------------------------------
    # ForwardReachability: initializations
    #------------------------------------------------------------
    def __init__(self,  tran_sys : TransitionSystem, instantiator : FiniteIvyInstantiator, options : QrmOptions):
        self.tran_sys     = tran_sys
        self.instantiator = instantiator 
        self.options      = options
        # utils
        self.instantiator    = instantiator
        self.ivy_actions     = []
        self.protocol        = None
        self.ivy_executor    = None
        # dfs data structures
        self.dfs_explored_states = set()
        self.dfs_repr_states     = set()
        self.dfs_max_depth       = 0

    def _init_ivy_actions(self):
        self.ivy_actions = self.instantiator.ivy_actions

    def _init_protocol(self):
        self.protocol = Protocol(self.options)                
        self.protocol.init_sort(self.tran_sys)
        self.protocol.init_dependent_sort(self.tran_sys)
        self.protocol.init_predicate(self.tran_sys)
        self.protocol.init_atoms(self.instantiator.protocol_atoms, self.instantiator.protocol_atoms_fmlas)
        self.protocol.init_sorts_permutations(self.tran_sys)

    def _init_finite_ivy_generator(self):
        FiniteIvyGenerator.set_transition_system(self.tran_sys)
        FiniteIvyGenerator.set_instantiator(self.instantiator)
        FiniteIvyGenerator.set_options(self.options)
        FiniteIvyGenerator.set_path_and_file_names()
        FiniteIvyGenerator.set_state_var_to_access_action()
        FiniteIvyGenerator.set_state_variables(self.protocol.constant_Name2Id)
        FiniteIvyGenerator.set_non_bool_state_variables(self.protocol.constant_Name2Id)
        FiniteIvyGenerator.write_ivy()
        FiniteIvyGenerator.compile_finite_ivy_to_cpp()
        FiniteIvyGenerator.build_ivy_exec_python_module()

    def _initialize(self):
        self._init_ivy_actions()
        self._init_protocol()
        self._init_finite_ivy_generator() 
        self.ivy_executor = FiniteIvyExecutor(self.options, self.instantiator) 

    #------------------------------------------------------------
    # ForwardReachability: core depth first search algorthm
    #------------------------------------------------------------
    def _create_dfs_node(self):
        dfs_state = self.ivy_executor.get_dfs_state()
        ivy_state = self.ivy_executor.backup_ivy_state()
        node      = DfsNode(dfs_state, ivy_state)
        return node 

    def _add_dfs_explored_state(self, node):
        self.dfs_repr_states.add(node.dfs_state)
        values = node.dfs_state.split(',')
        for nvalues in self.protocol.all_permutations(values):
            nstate = ','.join(nvalues)
            self.dfs_explored_states.add(nstate)
        # use this line instead if disabling symmetry aware
        # self.dfs_explored_states.add(node.dfs_state) 

    def _restore_ivy_state(self, node):
        self.ivy_executor.restore_ivy_state(node.ivy_state)

    def _can_dfs_recur_node(self, node):
        return node.dfs_state not in self.dfs_explored_states

    def _expand_nondeterministic_successors(self, action):
        ivy_result       = self.ivy_executor.execute_ivy_action(action)
        pending_children = []
        while ivy_result == IVY_ACTION_INCOMPLETE:
            child_node = self._create_dfs_node()
            if self._can_dfs_recur_node(child_node):
                self._add_dfs_explored_state(child_node)     
                pending_children.append(child_node)
            ivy_result = self.ivy_executor.execute_ivy_action(action)
        if ivy_result == IVY_ACTION_COMPLETE:
            child_node = self._create_dfs_node()
            if self._can_dfs_recur_node(child_node):
                self._add_dfs_explored_state(child_node)     
                pending_children.append(child_node)
        return pending_children

    def _symmetry_aware_depth_first_search_recur_node(self, node, level=0):
        # vprint_title(self.options, f'level {level}', 5)
        # vprint(self.options, node.dfs_state, 5)
        self.dfs_max_depth = max(level, self.dfs_max_depth)
        for action in self.ivy_actions:
            self._restore_ivy_state(node) 
            pending_children = self._expand_nondeterministic_successors(action)
            for child_node in pending_children:
                self._symmetry_aware_depth_first_search_recur_node(child_node, level+1)

    def _symmetry_aware_depth_first_search_reachability(self):
        self.dfs_repr_states  = set() 
        initial_nodes         = self._expand_nondeterministic_successors(action='QRM_INIT_PROTOCOL')
        for initial_node in initial_nodes:
            self._symmetry_aware_depth_first_search_recur_node(initial_node)

    def _update_protocol_states(self):
        protocol_states = [] 
        for dfs_state in self.dfs_explored_states:
            protocol_state = ''.join(dfs_state.split(','))
            protocol_states.append(protocol_state)
        self.protocol.init_reachable_states(protocol_states)

    def _write_protocol(self):
        if (self.options.writeReach):
            self.protocol.write_reachability()
        self.protocol.print_verbose(self.tran_sys)
        vprint(self.options, f'[FW NOTE]: dfs max depth: {self.dfs_max_depth}', 2)
        vprint(self.options, f'[FW NOTE]: number of total reachable states:        {len(self.dfs_explored_states)}', 2)
        vprint(self.options, f'[FW NOTE]: number of dfs representative states:     {len(self.dfs_repr_states)}', 2)
        vprint(self.options, f'[FW NOTE]: number of dfs non-representative states: {len(self.dfs_explored_states)- len(self.dfs_repr_states)}', 2)
    #------------------------------------------------------------
    # ForwardReachability: utils
    #------------------------------------------------------------

    def _clean(self):
        self.ivy_executor.execute_ivy_action('QRM_STOP_PROTOCOL')
        FiniteIvyGenerator.clean()

    #------------------------------------------------------------
    # ForwardReachability: public methods
    #------------------------------------------------------------

    def solve_reachability(self):
        self._initialize()
        self._symmetry_aware_depth_first_search_reachability()
        self._update_protocol_states()
        self._write_protocol()
        self._clean()

def get_protocol_forward_reachability(tran_sys : TransitionSystem, instantiator : FiniteIvyInstantiator, options:QrmOptions) -> Type[Protocol]:
    # dfs
    fr_solver = ForwardReachability(tran_sys, instantiator, options)
    fr_solver.solve_reachability()
    return fr_solver.protocol