from typing import Type, Set, List, Dict
from util import QrmOptions, ForwardMode
from transition_system import TransitionSystem
from protocol import Protocol
from finite_ivy_instantiate import FiniteIvyInstantiator
from finite_ivy_gen import FiniteIvyGenerator
from finite_ivy_exec import FiniteIvyExecutor, IVY_ACTION_COMPLETE, IVY_ACTION_INCOMPLETE 
from bdd import FormulaInitializer, Bdd
from verbose import *
from math import factorial as fact
import repycudd

class ForwardReachability():
    def __init__(self,  tran_sys : TransitionSystem, instantiator : FiniteIvyInstantiator, options : QrmOptions):
        self.tran_sys     = tran_sys
        self.instantiator = instantiator 
        self.options      = options
        self.protocol     = None

        self.setup()

    def _init_protocol(self):
        self.protocol = Protocol(self.options)                
        self.protocol.init_sort(self.tran_sys)
        self.protocol.init_dependent_sort(self.tran_sys)
        self.protocol.init_predicate(self.tran_sys)
        self.protocol.init_atoms(self.instantiator.protocol_state_atoms, self.instantiator.protocol_state_atoms_fmlas,
                                 self.instantiator.protocol_interpreted_atoms, self.instantiator.protocol_interpreted_atoms_fmlas)
        self.protocol.init_sorts_permutations(self.tran_sys)

    def _print_protocol_basic_info(self) -> None:
        sym_group_order = 1
        for sort_id, constants in enumerate(self.protocol.sort_constants):
            sort_name     = self.protocol.sorts[sort_id]
            if not self.tran_sys.get_finite_sort_from_sort_name(sort_name) in self.tran_sys.dep_types:
                sym_group_order *= fact(len(constants))
        vprint(self.options, f'[FW NOTE]: number of state atoms: {self.protocol.state_atom_num}', 2)
        vprint(self.options, f'[FW NOTE]: number of interpreted atoms (e.g. member,le): {self.protocol.interpreted_atom_num}', 2)
        vprint(self.options, f'[FW NOTE]: symmetric group order: {sym_group_order}', 2)

    def setup(self):
        self._init_protocol()
        self._print_protocol_basic_info()

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

class SymDFS(ForwardReachability):
    def __init__(self, tran_sys : TransitionSystem, instantiator : FiniteIvyInstantiator, options : QrmOptions):
        ForwardReachability.__init__(self, tran_sys, instantiator, options)
        # utils
        self.ivy_actions     = []
        self.ivy_executor    = None
        # dfs data structures
        self.dfs_explored_states : Set[str]  = set()  # state is represented as bit string
        self.dfs_repr_states     : List[int] = []     # representative state is the smallest decimal representation of all bit strings in orbit
        self.dfs_state_orbits    : List[StateOrbit] = []
        self.dfs_max_depth       = 0
        self.dfs_immutable_state = ''

        self._initialize_dfs()
    #------------------------------------------------------------
    # SymDFS: initialization 
    #------------------------------------------------------------
    def _init_ivy_actions(self):
        self.ivy_actions = self.instantiator.ivy_actions
        vprint(self.options, f'[FW NOTE]: number of branching actions: {len(self.ivy_actions)}', 2)

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

    def _initialize_dfs(self):
        self._init_ivy_actions()
        self._init_finite_ivy_generator() 
        self.ivy_executor = FiniteIvyExecutor(self.options, self.instantiator) 

    #------------------------------------------------------------
    # SymDFS: core depth first search algorthm
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
    # SymDFS: utils
    #------------------------------------------------------------
    def _clean(self):
        self.ivy_executor.execute_ivy_action('QRM_STOP_PROTOCOL')
        FiniteIvyGenerator.clean()

    #------------------------------------------------------------
    # SymDFS: update protocol states
    #------------------------------------------------------------
    def _update_protocol_states(self):
        # reachable states
        protocol_states = list(self.dfs_explored_states)
        self.protocol.init_reachable_states(self.dfs_immutable_state, protocol_states)
        # representative states
        self.protocol.init_representative_states(self.dfs_repr_states)

    #------------------------------------------------------------
    # SymDFS: print methods
    #------------------------------------------------------------
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

    #------------------------------------------------------------
    # SymDFS: public methods
    #------------------------------------------------------------
    def forward_reachability(self):
        self._symmetric_quotient_depth_first_search_reachability()
        self._update_protocol_states()
        self._clean()
        self._print_dfs_statistics()
        self._print_reachability()
        if (self.options.writeReach):
            self.protocol.write_reachability()

class BddSymbolic(ForwardReachability):
    def __init__(self, tran_sys : TransitionSystem, instantiator : FiniteIvyInstantiator, options : QrmOptions):
        ForwardReachability.__init__(self, tran_sys, instantiator, options)
        self.fmla  = FormulaInitializer(tran_sys, instantiator, options)
        self.reach = None
        self.cubes = []
        self.immutable_cube = ''

    def _symbolic_image_computation(self):
        self.bdd   = Bdd(self.fmla)
        reach = self.bdd.init_action
        frontier = [self.bdd.init_action]
        while (len(frontier) > 0):
            front = frontier.pop()
            if front == self.bdd.ddmanager.ReadLogicZero():
                continue
            not_reach = self.bdd.ddmanager.Not(reach)
            successors = []
            for action, action_bdds in self.bdd.exported_actions.items():
                succ = self.bdd.ddmanager.Zero()
                has_expanded = False
                for action_bdd in action_bdds:
                    image = self.bdd.ddmanager.AndAbstract(front, action_bdd, self.bdd.curr_atom_cube) # perform existential quantification on current atoms
                    if image == self.bdd.ddmanager.ReadLogicZero(): 
                        continue
                    image = self.bdd.ddmanager.SwapVariables(image, self.bdd.curr_DdArray, self.bdd.next_DdArray, self.bdd.state_atom_num) 
                    image = self.bdd.ddmanager.And(image, self.bdd.curr_axiom) 
                    if image == self.bdd.ddmanager.ReadLogicZero(): 
                        continue
                    expanded = self.bdd.ddmanager.And(image, not_reach)   
                    if expanded == self.bdd.ddmanager.ReadLogicZero(): 
                        continue
                    succ = self.bdd.ddmanager.Or(succ, expanded)
                    has_expanded = True
                if has_expanded:
                    successors.append(succ)
            
            for succ in successors:
                frontier.append(succ)
                reach = self.bdd.ddmanager.Or(reach, succ)
        self.reach = self.bdd.ddmanager.ExistAbstract(reach, self.bdd.next_atom_cube) # perform existential quantification on next atoms

    def _update_protocol_states(self):
        has_extract_immut_cube = False
        self.immutable_cube = ''
        immut_lits = ['']*self.protocol.interpreted_atom_num
        for cudd_cube in repycudd.ForeachCubeIterator(self.bdd.ddmanager, self.reach):
            state_lits = ['']*self.protocol.state_atom_num
            for cudd_id, val in enumerate(cudd_cube):
                if cudd_id in self.bdd.cudd_id2state_atom_id:
                    atom_id = self.bdd.cudd_id2state_atom_id[cudd_id] 
                    if val == 2:
                        state_lits[atom_id] = '-'
                    else:
                        state_lits[atom_id] = str(val)
                elif not has_extract_immut_cube and cudd_id in self.bdd.cudd_id2immut_atom_id:
                    atom_id = self.bdd.cudd_id2immut_atom_id[cudd_id] 
                    assert(val == 1 or val == 0)
                    assert(immut_lits[atom_id] == '')
                    immut_lits[atom_id] = str(val)
            state_cube = ''.join(state_lits)
            assert(len(state_cube) == self.protocol.state_atom_num)
            self.cubes.append(state_cube)
            if not has_extract_immut_cube:
                self.immutable_cube = ''.join(immut_lits)
                assert(len(self.immutable_cube) == self.protocol.interpreted_atom_num)
                has_extract_immut_cube = True
        self.protocol.init_reachable_states(self.immutable_cube, self.cubes)

    def _clean(self):
        self.bdd.clean()

    def _print_reachability(self) -> None:
        vprint_step_banner(self.options, f'[FW RESULT]: Forward Reachability on [{self.options.instance_name}: {self.options.size_str}]', 3)
        vprint(self.options, '\n'.join(self.protocol.header), 3)
        vprint(self.options, '\n'.join(self.cubes), 3)

    def _print_bdd_statistics(self) -> None:
        vprint(self.options, f'[FW NOTE]: number of reachable cubes: {len(self.cubes)}', 2)

    def forward_reachability(self):
        self._symbolic_image_computation()
        self._update_protocol_states()
        self._clean()
        self._print_bdd_statistics()
        self._print_reachability()
        if (self.options.writeReach):
            self.protocol.write_reachability()
        # TODO: mimization
        # TODO: update README.md for repycudd