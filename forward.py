from util import QrmOptions
from vmt_parser import TransitionSystem
from protocol import Protocol
from verbose import *
from finite_ivy_instantiate import FiniteIvyInstantiator
from finite_ivy_gen import FiniteIvyGenerator
from finite_ivy_exec import FiniteIvyExecutor

class DfsNode():
    def __init__(self, dfs_state, ivy_state):
        self.dfs_state = dfs_state
        self.ivy_state = ivy_state

class ForwardReachability():
    #------------------------------------------------------------
    # ForwardReachability: initializations
    #------------------------------------------------------------
    def __init__(self,  tran_sys : TransitionSystem, options : QrmOptions):
        self.tran_sys = tran_sys
        self.options  = options
        # utils
        self.instantiator    = None
        self.ivy_actions     = []
        self.protocol        = None
        self.ivy_executor    = None
        # dfs data structures
        self.dfs_global_state    = []
        self.dfs_explored_states = set()

    def _init_instantiator(self):
        self.instantiator = FiniteIvyInstantiator(self.tran_sys)
    
    def _init_ivy_actions(self):
        self.ivy_actions = self.instantiator.ivy_actions

    def _init_protocol(self):
        self.protocol = Protocol(self.options)                
        self.protocol.init_sort(self.tran_sys)
        self.protocol.init_dependent_sort(self.tran_sys)
        self.protocol.init_predicate(self.tran_sys)
        self.protocol.init_atoms(self.instantiator.protocol_atoms, self.instantiator.protocol_atoms_fmls)
        self.protocol.init_sorts_permutations()

    def _init_finite_ivy_generator(self):
        FiniteIvyGenerator.set_transition_system(self.tran_sys)
        FiniteIvyGenerator.set_options(self.options)
        FiniteIvyGenerator.set_path_and_file_names()
        FiniteIvyGenerator.set_state_var_to_access_action()
        FiniteIvyGenerator.set_state_variables(self.protocol.constant_Name2Id, self.instantiator.ivy_state_vars)
        FiniteIvyGenerator.write_ivy()
        FiniteIvyGenerator.compile_finite_ivy_to_cpp()
        FiniteIvyGenerator.build_ivy_exec_python_module()

    def _initialize(self):
        self._init_instantiator()
        self._init_ivy_actions()
        self._init_protocol()
        self._init_finite_ivy_generator() 

    #------------------------------------------------------------
    # ForwardReachability: core depth first search algorthm
    #------------------------------------------------------------
    def _create_dfs_node(self):
        dfs_state = self.ivy_executor.get_dfs_state()
        ivy_state = self.ivy_executor.backup_ivy_state()
        node      = DfsNode(dfs_state, ivy_state)
        return node 

    def _add_dfs_explored_state(self, node):
        # values = node.dfs_state.split(',')
        # for nvalues in self.protocol.all_permutations(values):
        #     nstate = ','.join(nvalues)
        #     self.dfs_explored_states.add(nstate)
        self.dfs_explored_states.add(node.dfs_state)

    def _restore_ivy_state(self, node):
        self.ivy_executor.restore_ivy_state(node.ivy_state)

    def _can_dfs_recur_node(self, node):
        return node.dfs_state not in self.dfs_explored_states

    def _symmetry_aware_depth_first_search_recur_node(self, node, level=0):
        vprint_title(self.options, f'level: {level}', 5)
        vprint(self.options, '\n'.join([str((self.instantiator.dfs_state_vars[i], val)) for i,val in enumerate(node.dfs_state.split(','))]), 5)
        self._add_dfs_explored_state(node)     
        for action in self.ivy_actions:
            self._restore_ivy_state(node) 
            has_change_state = self.ivy_executor.execute_ivy_action(action)
            if has_change_state:
                child_node = self._create_dfs_node()
                if self._can_dfs_recur_node(child_node):
                    vprint(self.options, action, 5)
                    self._symmetry_aware_depth_first_search_recur_node(child_node, level+1)

    def _symmetry_aware_depth_first_search_reachability(self):
        self.ivy_executor     = FiniteIvyExecutor(self.options, self.instantiator) 
        self.dfs_global_state = self.ivy_executor.get_dfs_global_state()
        vprint(self.options, '\n'.join([str((self.instantiator.dfs_global_vars[i], val)) for i,val in enumerate(self.dfs_global_state.split(','))]), 5)
        initial_node = self._create_dfs_node()
        self._symmetry_aware_depth_first_search_recur_node(initial_node)

    def _update_protocol_states(self):
        protocol_states = [] 
        for dfs_state in self.dfs_explored_states:
            protocol_state = ''.join(dfs_state.split(','))
            protocol_states.append(protocol_state)
        self.protocol.init_reachable_states(protocol_states)

        # write protocols
        if (self.options.writeReach):
            self.protocol.write_reachability()
        self.protocol.print_verbose()

    #------------------------------------------------------------
    # ForwardReachability: utils
    #------------------------------------------------------------

    def _clean(self):
        FiniteIvyGenerator.clean()

    #------------------------------------------------------------
    # ForwardReachability: public methods
    #------------------------------------------------------------

    def solve_reachability(self):
        self._initialize()
        self._symmetry_aware_depth_first_search_reachability()
        self._update_protocol_states()
        self._clean()

def get_forward_reachability(tran_sys : TransitionSystem, options:QrmOptions):
    # dfs
    fr_solver = ForwardReachability(tran_sys, options)
    fr_solver.solve_reachability()
    return fr_solver.protocol