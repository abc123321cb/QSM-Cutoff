from typing import Type, Set, List
from util import QrmOptions
from transition_system import TransitionSystem
from protocol import Protocol
from finite_ivy_instantiate import FiniteIvyInstantiator
from finite_ivy_gen import FiniteIvyGenerator
from finite_ivy_exec import FiniteIvyExecutor, IVY_ACTION_COMPLETE, IVY_ACTION_INCOMPLETE 
from verbose import *
from qutil import get_func_args
import numpy as np
from math import factorial as fact

class DfsNode():
    def __init__(self, dfs_state, ivy_state):
        self.dfs_state = dfs_state   # bit string: b0b1b2...
        self.ivy_state = ivy_state   # value string with delim ',': v0,v1,v2,...

class StateOrbit():
    def __init__(self, dfs_state, visit_id):
        self.repr_state = dfs_state # first visited state in this orbit
        self.visit_id   = visit_id 
        self.states     = set()
        self.repr_int   = 0

    def __str__(self) -> str:
        lines  = f'\n=== State Orbit {self.visit_id} =====================\n'
        lines += f'size : {len(self.states)}\n'
        lines += f'repr state: {self.repr_state}\n'
        lines += f'lex min decimal: {self.repr_int}\n'
        lines += f'states:\n'
        for state in self.states:
            lines += f'{state}\n'
        lines += '\n'
        return lines

class ForwardReachability():
    #------------------------------------------------------------
    # ForwardReachability: initializations
    #------------------------------------------------------------
    def __init__(self,  tran_sys : TransitionSystem, instantiator : FiniteIvyInstantiator, options : QrmOptions):
        self.tran_sys     = tran_sys
        self.instantiator = instantiator 
        self.options      = options
        # utils
        self.ivy_actions     = []
        self.protocol        = None
        self.ivy_executor    = None
        # dfs data structures
        self.dfs_explored_states : Set[str]  = set()  # state is represented as bit string
        self.dfs_repr_states     : List[int] = []     # representative state is the smallest decimal representation of all bit strings in orbit
        self.dfs_state_orbits    : List[StateOrbit] = []
        self.dfs_max_depth       = 0
        self.dfs_immutable_state = ''
        # equivalence quotient data structures
        self.atom2equivs      = {} 
        self.atom2complements = {}
        self.remove_atom_ids  = set()

    def _init_ivy_actions(self):
        self.ivy_actions = self.instantiator.ivy_actions

    def _init_protocol(self):
        self.protocol = Protocol(self.options)                
        self.protocol.init_sort(self.tran_sys)
        self.protocol.init_dependent_sort(self.tran_sys)
        self.protocol.init_predicate(self.tran_sys)
        self.protocol.init_atoms(self.instantiator.protocol_state_atoms, self.instantiator.protocol_state_atoms_fmlas,
                                 self.instantiator.protocol_interpreted_atoms, self.instantiator.protocol_interpreted_atoms_fmlas)
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
        state_orbit = StateOrbit(dfs_state=node.dfs_state, visit_id=len(self.dfs_state_orbits))
        values   = list(node.dfs_state)
        repr_int = int(node.dfs_state + self.dfs_immutable_state, 2)
        for nvalues in self.protocol.all_permutations(values):
            nstate   = ''.join(nvalues)
            repr_int = min(int(nstate + self.dfs_immutable_state, 2), repr_int)
            self.dfs_explored_states.add(nstate)
            state_orbit.states.add(nstate)
        self.dfs_repr_states.append(repr_int)
        state_orbit.repr_int = repr_int
        self.dfs_state_orbits.append(state_orbit)

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

    def _symmetric_quotient_depth_first_search_recur_node(self, node, level=0):
        # vprint_title(self.options, f'level {level}', 5)
        # vprint(self.options, node.dfs_state, 5)
        self.dfs_max_depth = max(level, self.dfs_max_depth)
        for action in self.ivy_actions:
            self._restore_ivy_state(node) 
            pending_children = self._expand_nondeterministic_successors(action)
            for child_node in pending_children:
                self._symmetric_quotient_depth_first_search_recur_node(child_node, level+1)

    def _symmetric_quotient_depth_first_search_reachability(self):
        self.dfs_immutable_state = self.ivy_executor.get_dfs_immutable_state()
        initial_nodes = self._expand_nondeterministic_successors(action='QRM_INIT_PROTOCOL')
        for initial_node in initial_nodes:
            self._symmetric_quotient_depth_first_search_recur_node(initial_node)
        
    #------------------------------------------------------------
    # ForwardReachability: utils
    #------------------------------------------------------------
    def _clean(self):
        self.ivy_executor.execute_ivy_action('QRM_STOP_PROTOCOL')
        FiniteIvyGenerator.clean()

    #------------------------------------------------------------
    # ForwardReachability: equivalence reduction 
    #------------------------------------------------------------
    def _get_state_array_from_state_list(self, state_list : List[str]):
        # Convert list of strings to a 2D numpy array
        return np.array([list(s) for s in state_list])

    def _set_equivalent_complement_atoms(self, state_array):
        atom_num = self.protocol.state_atom_num
        for i in range(atom_num-1):
            if i in self.remove_atom_ids:
                continue
            for j in range(i+1, atom_num):
                if j in self.remove_atom_ids:
                    continue
                atom_i = self.protocol.atoms_fmla[i] 
                atom_j = self.protocol.atoms_fmla[j]
                if get_func_args(atom_i) != get_func_args(atom_j):
                    continue
                if np.array_equal(state_array[:, i], state_array[:, j]):
                    if not atom_i in self.atom2equivs:
                        self.atom2equivs[atom_i] = []
                    self.atom2equivs[atom_i].append(atom_j)
                    self.remove_atom_ids.add(j)
                elif int(''.join(state_array[:, i]), 2) + int(''.join(state_array[:, j]), 2) == int('1'*atom_num, 2):  # complement
                    if not atom_i in self.atom2complements:
                        self.atom2complements[atom_i] = []
                    self.atom2complements[atom_i].append(atom_j)
                    self.remove_atom_ids.add(j)

    #------------------------------------------------------------
    # ForwardReachability: update protocol states
    #------------------------------------------------------------
    def _update_protocol_states(self):
        # reachable states
        protocol_states = list(self.dfs_explored_states)
        self.protocol.init_reachable_states(self.dfs_immutable_state, protocol_states)
        # representative states
        self.protocol.repr_states = self.dfs_repr_states

    def _reduce_equivalent_atoms(self):
        # equivalence reduced states (post-processing)
        state_array = self._get_state_array_from_state_list(self.protocol.reachable_states)
        self._set_equivalent_complement_atoms(state_array)
        self.protocol.set_quotient_reachabiliy(state_array, self.remove_atom_ids)
        self.tran_sys.set_atom_equivalence_constraints(self.atom2equivs, self.atom2complements)

    #------------------------------------------------------------
    # ForwardReachability: print methods
    #------------------------------------------------------------
    def _print_protocol_basic_info(self) -> None:
        sym_group_order = 1
        for sort_id, constants in enumerate(self.protocol.sort_constants):
            sort_name     = self.protocol.sorts[sort_id]
            if not self.tran_sys.get_finite_sort_from_sort_name(sort_name) in self.tran_sys.dep_types:
                sym_group_order *= fact(len(constants))
        vprint(self.options, f'[FW NOTE]: number of state atoms: {self.protocol.state_atom_num}', 2)
        vprint(self.options, f'[FW NOTE]: number of interpreted atoms (e.g. member,le): {self.protocol.interpreted_atom_num}', 2)
        vprint(self.options, f'[FW NOTE]: number of branching actions: {len(self.ivy_actions)}', 2)
        vprint(self.options, f'[FW NOTE]: symmetric group order: {sym_group_order}', 2)

    def _print_reachability(self) -> None:
        vprint_step_banner(self.options, f'[FW RESULT]: Forward Reachability on [{self.options.instance_name}: {self.options.size_str}]', 3)
        vprint(self.options, '\n'.join(self.protocol.header), 3)
        for state_orbit in self.dfs_state_orbits:
            vprint(self.options, str(state_orbit), 3) 

    def _print_dfs_statistics(self) -> None:
        vprint(self.options, f'[FW NOTE]: dfs max depth: {self.dfs_max_depth}', 2)
        vprint(self.options, f'[FW NOTE]: number of total reachable states:        {len(self.dfs_explored_states)}', 2)
        vprint(self.options, f'[FW NOTE]: number of dfs representative states:     {len(self.dfs_repr_states)}', 2)
        vprint(self.options, f'[FW NOTE]: number of dfs non-representative states: {len(self.dfs_explored_states)-len(self.dfs_repr_states)}', 2)

    def _print_equiv_reduction_info(self) -> None:
        vprint(self.options, f'[FW NOTE]: equivalent atoms', 2)
        for atom, equivs in self.atom2equivs.items():
            vprint(self.options, f'\t{str(atom)}: {[str(e) for e in equivs]}', 2)
        vprint(self.options, f'[FW NOTE]: complement atoms', 2)
        for atom, cmpls in self.atom2complements.items():
            vprint(self.options, f'\t{str(atom)}: {[str(c) for c in cmpls]}', 2)
        vprint(self.options, f'[FW NOTE]: remove_atom_ids: {self.remove_atom_ids}', 2)

    #------------------------------------------------------------
    # ForwardReachability: public methods
    #------------------------------------------------------------
    def setup(self):
        self._initialize()
        self._print_protocol_basic_info()

    def symmetric_quotient_depth_first_search_reachability(self):
        self._symmetric_quotient_depth_first_search_reachability()
        self._update_protocol_states()
        self._clean()
        self._print_dfs_statistics()
        if (self.options.writeReach):
            self.protocol.write_reachability()

    def reduce_equivalent_atoms(self):
        self._reduce_equivalent_atoms()
        self._print_equiv_reduction_info()

    def print_reachability(self):
        self._print_reachability()