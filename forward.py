from frontend.fr import *
from frontend.problem import *
from util import QrmOptions
from vmt_parser import TransitionSystem
from protocol import Protocol, Reachability
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
        self.protocol.initialize_from_transition_system(self.tran_sys, self.instantiator.protocol_atoms)

    def _init_finite_ivy_generator(self):
        FiniteIvyGenerator.set_transition_system(self.tran_sys)
        FiniteIvyGenerator.set_options(self.options)
        FiniteIvyGenerator.set_path_and_file_names()
        FiniteIvyGenerator.set_state_var_to_access_action()
        FiniteIvyGenerator.set_state_variables(self.protocol.element_Name2Id, self.instantiator.ivy_state_vars)
        FiniteIvyGenerator.write_ivy()
        FiniteIvyGenerator.compile_finite_ivy_to_cpp()
        FiniteIvyGenerator.build_ivy_exec_python_module()

    def initialize(self):
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
        values = node.dfs_state.split(',')
        for nvalues in self.protocol.all_permutations(values):
            nstate = ','.join(nvalues)
            self.dfs_explored_states.add(nstate)

    def _restore_ivy_state(self, node):
        self.ivy_executor.restore_ivy_state(node.ivy_state)

    def _can_dfs_recur_node(self, node):
        return node.dfs_state not in self.dfs_explored_states

    def _symmetry_aware_depth_first_search_recur_node(self, node):
        self._add_dfs_explored_state(node)     
        for action in self.ivy_actions:
            self._restore_ivy_state(node) 
            has_change_state = self.ivy_executor.execute_ivy_action(action)
            if has_change_state:
                child_node = self._create_dfs_node()
                if self._can_dfs_recur_node(child_node):
                    self._symmetry_aware_depth_first_search_recur_node(child_node)

    def symmetry_aware_depth_first_search_reachability(self):
        self.ivy_executor = FiniteIvyExecutor(self.instantiator) 
        self.dfs_global_state = self.ivy_executor.get_dfs_global_state()
        initial_node = self._create_dfs_node()
        self._symmetry_aware_depth_first_search_recur_node(initial_node)

    #------------------------------------------------------------
    # ForwardReachability: utilities
    #------------------------------------------------------------

    def clean(self):
        FiniteIvyGenerator.clean()

    #------------------------------------------------------------
    # ForwardReachability: public methods
    #------------------------------------------------------------

    def solve_reachability(self):
        self.initialize()
        self.symmetry_aware_depth_first_search_reachability()
        self.clean()

    def get_protocol(self):
        return self.protocol

def get_forward_reachability(tran_sys_orig, tran_sys, options:QrmOptions) -> FR:
    # dfs
    fr = ForwardReachability(tran_sys, options)
    fr.solve_reachability()

    # forward reachability
    fr_solver = FR(tran_sys_orig)
    set_problem(fr_solver)
    (atoms, states) = fr_solver.solve_reachability()
    subst = tran_sys.get_pretty_set_substitution_map()
    reach = Reachability(atoms, states, subst)
    fr_solver.reset() 
    return reach