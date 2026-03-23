from typing import Type, Set, List, Dict
import hashlib, colorsys
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
try:
    from graphviz import Digraph
except ImportError:
    Digraph = None
    pass # graphviz is an optional dependency but needed if --graph is used

import json
from pathlib import Path


class ForwardReachability():
    def __init__(self,  tran_sys : TransitionSystem, instantiator : FiniteIvyInstantiator, options : QrmOptions):
        self.tran_sys     = tran_sys
        self.instantiator = instantiator 
        self.options      = options
        self.protocol     = None

        self.setup()

    def _init_protocol(self) -> None:
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
    def __init__(self, dfs_state, visit_id, state_atoms, ivy_state, ivy_state_atoms, protocol, tran_sys, instantiator):
        self.repr_state = dfs_state # first visited state in this orbit (not actually important for the algorithm and for printing only) 
        self.repr_ivy_state = ivy_state
        self.visit_id   = visit_id 
        self.states     = []
        self.ivy_states = []
        self.repr_int   = 0         # the minimum value in the orbit
        self.state_atoms = state_atoms
        self.ivy_state_atoms = ivy_state_atoms
        self.protocol = protocol
        self.tran_sys = tran_sys
        self.instantiator = instantiator

    def __str__(self) -> str:
        lines  = f'\n=== State Orbit {self.visit_id} =====================\n'
        lines += f'size : {len(self.states)}\n'
        lines += f'repr state: {self.repr_state}\n'
        lines += f'lex min decimal: {hex(self.repr_int)}\n'
        lines += f'states:\n'
        for state in self.states:
            lines += f'{state}\n'
        # lines += '\n'
        # lines += f'hex states:\n'
        # for state in self.states:
        #     lines += f'{hex(int(state, 2))}\n'
        lines += '\n'
        for i, ivy_state in enumerate(self.ivy_states):
            lines+= f"State {i}:\n"
            ivy_state = ivy_state.split(',')
            for var_id, var_name in enumerate(self.instantiator._instantiated_indep_vars): # type: ignore
                var_func = self.protocol.get_function_symbol_from_atom(var_name)
                if var_func not in self.tran_sys.axiom_symbols:
                    if ivy_state[var_id] != '0':
                        lines+= f"{self.ivy_state_atoms[var_id]}: {ivy_state[var_id]}\n"
            lines+= "\n"
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
        self._state2repr: Dict[str, int] = {}
        self.collect_edges: bool = options.transition_reach or options.make_graph
        # self.dfs_explored_edges: set[tuple[int, int]] = set() \
        #     if self.collect_edges else None
        self.dfs_explored_edge_labels = {} if self.collect_edges else None

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
        self._init_finite_ivy_generator() # makes the c++ file to run it
        self.ivy_executor = FiniteIvyExecutor(self.options, self.instantiator) 

    #------------------------------------------------------------
    # SymDFS: core depth first search algorthm
    #------------------------------------------------------------

    def _register_state_orbit(self, node: DfsNode, repr_int: int) -> None:
        for bits in self.protocol.all_permutations(list(node.dfs_state)):
            self._state2repr[''.join(bits)] = repr_int

    def _create_dfs_node(self):
        dfs_state = self.ivy_executor.get_dfs_state()
        ivy_state = self.ivy_executor.backup_ivy_state()
        node      = DfsNode(dfs_state, ivy_state)
        return node 

    def _add_dfs_explored_state(self, node):
        state_orbit = StateOrbit(dfs_state=node.dfs_state, visit_id=len(self.dfs_state_orbits), 
                                 state_atoms=self.protocol.state_atoms, ivy_state=node.ivy_state,
                                 ivy_state_atoms=self.instantiator.ivy_state_vars,
                                 tran_sys=self.tran_sys, protocol=self.protocol,
                                 instantiator=self.instantiator)
        values   = list(node.dfs_state)
        repr_int = int(node.dfs_state + self.dfs_immutable_state, 2)

        for nvalues in self.protocol.all_permutations(values):
            nstate   = ''.join(nvalues)
            repr_int = min(int(nstate + self.dfs_immutable_state, 2), repr_int)
            self.dfs_explored_states.add(nstate)
            state_orbit.states.append(nstate)
            state_orbit.ivy_states.append(self.dfs_state_to_ivy_state(nstate))
        
        self._register_state_orbit(node, repr_int)
        self.dfs_repr_states.append(repr_int)
        state_orbit.repr_int = repr_int
        self.dfs_state_orbits.append(state_orbit)

    def _restore_ivy_state(self, node):
        self.ivy_executor.restore_ivy_state(node.ivy_state)

    def _can_dfs_recur_node(self, node):
        return node.dfs_state not in self.dfs_explored_states
    
    def _record_edge(self, parent_repr: int, child_repr: int, action: str) -> None:
        if self.collect_edges:
            self.dfs_explored_edge_labels[(parent_repr, child_repr)] = action

    def _register_state_orbit_bits(self, dfs_state_bits: str, repr_int: int) -> None:
        for bits in self.protocol.all_permutations(list(dfs_state_bits)):
            self._state2repr[''.join(bits)] = repr_int

    def _expand_nondeterministic_successors(self, action):
        """
        Execute `action`, enumerate every non-deterministic successor, register
        new orbits, record the (src_repr, dst_repr) edge, and return the list
        of *new* child nodes that must be explored recursively.
        """
        # 1. Snapshot the parent BEFORE mutating the IVy state
        parent_raw = self.ivy_executor.get_dfs_state()

        #    Ensure the parent orbit is registered
        if parent_raw not in self._state2repr:
            parent_repr_int = int(parent_raw + self.dfs_immutable_state, 2)
            self._register_state_orbit_bits(parent_raw, parent_repr_int)

        parent_repr = self._state2repr[parent_raw]

        pending_children = []

        # if action == "QRM_INIT_PROTOCOL":
        #     self._total_order_initialize()
            
        ivy_result       = self.ivy_executor.execute_ivy_action(action)

        # if action == "QRM_INIT_PROTOCOL":
        #     self._total_order_initialize()


        # 2. Handle the stream of INCOMPLETE successors 
        while ivy_result == IVY_ACTION_INCOMPLETE:
            child_node = self._create_dfs_node()

            is_new = self._can_dfs_recur_node(child_node)
            if is_new:                                         # register orbit
                self._add_dfs_explored_state(child_node)

            child_repr = self._state2repr[child_node.dfs_state]
            self._record_edge(parent_repr, child_repr, action)         # store edge

            if is_new:                                         # recurse later
                pending_children.append(child_node)

            ivy_result = self.ivy_executor.execute_ivy_action(action)

        if ivy_result == IVY_ACTION_COMPLETE:
            child_node = self._create_dfs_node()

            is_new = self._can_dfs_recur_node(child_node)
            if is_new:
                self._add_dfs_explored_state(child_node)

            child_repr = self._state2repr[child_node.dfs_state]
            self._record_edge(parent_repr, child_repr, action)

            if is_new:
                pending_children.append(child_node)

        return pending_children
    

    # Pseudocode:
    # Loop over every atom:
    #   If it's one of the totally-ordered ones (like le, zero, max),
    #   then initialize it manually:
    #       If it's le(epoch{i}, epoch{j}), set it to true iff i <= j
    #       If it's max = epoch{i}, set it to true iff i = n
    #       If it's zero = epoch{j}, set it to true iff j = 0


    def _total_order_initialize(self):
        assert(self.protocol is not None)
        node = self._create_dfs_node()
        ivy_state = node.ivy_state.split(',')
        for var_id, var_name in enumerate(self.instantiator._instantiated_indep_vars): # type: ignore
            var_func = self.protocol.get_function_symbol_from_atom(var_name)
            if var_func in self.tran_sys.axiom_symbols:
                var_func_name = var_func.name
                if var_func_name == "le":
                    first_arg = var_name.args[0]
                    second_arg = var_name.args[1]
                    first_arg_index = self.tran_sys.sort2consts[first_arg.sort].index(first_arg)
                    second_arg_index = self.tran_sys.sort2consts[second_arg.sort].index(second_arg)
                    ivy_state[var_id] = '1' if first_arg_index <= second_arg_index else '0'
                elif var_func_name == "firste":
                    first_const = self.tran_sys.sort2consts[var_name.sort][1]
                    ivy_state[var_id] = first_const.name
                elif var_func_name == "max":
                    max_const = self.tran_sys.sort2consts[var_name.sort][-1]
                    ivy_state[var_id] = max_const.name
                elif var_func_name == "zero":
                    zero_const = self.tran_sys.sort2consts[var_name.sort][0]
                    ivy_state[var_id] = zero_const.name
        node.ivy_state = ",".join(ivy_state)
        self._restore_ivy_state(node)
        


    
    def _symmetric_quotient_depth_first_search_recur_node(self, node, level=0):
        vprint_title(self.options, f'level {level}', 5)
        vprint(self.options, node.dfs_state, 5)
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
        

    def dfs_state_to_ivy_state(self, dfs_state_bits: str) -> str:
        """
        Convert a dfs_state bitstring (length == self.protocol.state_atom_num)
        into a comma-separated ivy_state string whose ordering matches
        self.instantiator._instantiated_indep_vars / self.instantiator.ivy_state_vars.

        Behavior:
        - For an equality atom like `f(a)=c`: if the bit is '1', set f(a) -> 'c'.
          (bits '0' mean "not that constant" and are ignored; only '1' sets a value.)
        - For predicate (boolean) atoms like `p(a)`: '1' -> 'true', '0' -> 'false',
          '-' -> '-'.
        - If no equality atom sets a non-boolean variable, the corresponding
          entry will be '-' (unknown / don't-care).
        """
        assert len(dfs_state_bits) == self.protocol.state_atom_num
        # map from var (string form of an independent var, e.g. "ep(n0)")
        # to its value (string)
        var_values = {}

        for atom_id, bit in enumerate(dfs_state_bits):
            sig = self.protocol.atom_sig[atom_id]  # e.g. ['ep=', 'n0', 'epoch0'] or ['held', 'n0']
            pred = sig[0]
            if pred.endswith('='):  # equality atom: last entry is RHS value
                func_name = pred[:-1]
                args = sig[1:-1]
                rhs = sig[-1]
                # var key matches str(term) produced in instantiator._instantiated_indep_vars
                if args:
                    var_key = func_name + '(' + ','.join(args) + ')'
                else:
                    var_key = func_name
                if bit == '1':
                    # equality true => set function application to RHS
                    var_values[var_key] = rhs
                # bit == '0' gives only negative information; skip
            else:
                # boolean predicate
                func_name = pred
                args = sig[1:]
                var_key = func_name + '(' + ','.join(args) + ')'
                if bit == '1':
                    var_values[var_key] = '1'
                elif bit == '0':
                    var_values[var_key] = '0'
                else:
                    var_values[var_key] = '-'

        # build ivy_state list in the order of instantiated_indep_vars
        ivy_state_vals = []
        for var_term in self.instantiator._instantiated_indep_vars:  # type: ignore
            key = str(var_term)
            # instantiator.ivy_state_vars are built from these values by .replace('.', '__'),
            # but we compare to raw str(var_term)
            val = var_values.get(key, '-')
            ivy_state_vals.append(val)
        return ','.join(ivy_state_vals)    
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
        # is equal to #reachable states >= #unreach states
        self.protocol.more_reach = bool(int(round(len(self.dfs_explored_states)/pow(2,len(protocol_states[0])))))

    #------------------------------------------------------------
    # SymDFS: print methods
    #------------------------------------------------------------
    def _print_reachability(self) -> None:
        vprint_step_banner(self.options, f'[FW RESULT]: Forward Reachability on [{self.options.ivy_filename}: {self.options.size_str}]', 3)
        vprint(self.options, '\n'.join(self.protocol.header), 3)
        for state_orbit in self.dfs_state_orbits:
            vprint(self.options, str(state_orbit), 3) 

    def _print_dfs_statistics(self) -> None:
        vprint(self.options, f'[FW NOTE]: dfs max depth: {self.dfs_max_depth}', 2)
        vprint(self.options, f'[FW NOTE]: number of total reachable states:        {len(self.dfs_explored_states)}', 2)
        vprint(self.options, f'[FW NOTE]: number of dfs representative states:     {len(self.dfs_repr_states)}', 2)
        vprint(self.options, f'[FW NOTE]: number of dfs non-representative states: {len(self.dfs_explored_states)-len(self.dfs_repr_states)}', 2)

    def _print_transition_edges(self):
        if not self.options.transition_reach:
            return
        vprint_step_banner(self.options, '[FW RESULT]: Transition Edges', 3)
        for src, dst in sorted(self.dfs_explored_edge_labels.keys()):
            vprint(self.options, f'{src} → {dst}', 3)

    def _render_state_orbit_graph(self) -> None:
        """
        Build a DOT graph where each node is a StateOrbit, labeled with its
        representative state and orbit size. Each directed edge is labeled
        with the IVy action(s) that produced it.
        Only runs if options.make_graph is True.
        """
        if not self.options.make_graph:
            return
        if Digraph is None:
            vprint(self.options, "[FW NOTE]: graphviz not installed. But --graph called skipping graph draw", 5)
            return

        # Map repr_int -> StateOrbit (for labels)
        repr2orbit = {orbit.repr_int: orbit for orbit in self.dfs_state_orbits}

        dot = Digraph("state_orbits", engine="dot")
        dot.attr("graph", rankdir="LR", splines="spline")
        dot.attr("node", shape="circle", fontsize="11", style="filled", fillcolor="#E8F0FE")
        dot.attr("edge", fontsize="10", arrowsize="0.8")

        # Nodes: show representative state and orbit size
        for repr_int, orbit in repr2orbit.items():
            label = f"{orbit.repr_state}\\norbit size: {len(orbit.states)}"
            dot.node(str(repr_int), label=label)

        # Edges: aggregate action names on each (src,dst)
        for (src, dst), label in sorted(self.dfs_explored_edge_labels.items()):
            if label.casefold() == "qrm_init_protocol":
                continue
            dot.edge(str(src), str(dst), label)

        out_file = self.options.instance_name + '.' + self.options.instance_suffix + '.graph'
        dot.render(out_file, format="svg", cleanup=True)

    def _export_state_orbit_graph_cx2(self) -> None:
        """
        Write the state-orbit graph as CX2 (.cx2) for Cytoscape Web/Desktop, with node labels.
        Uses ndex2.
        """
        if not self.options.make_graph:
            return

        from ndex2.cx2 import CX2Network  # pip install ndex2
        from pathlib import Path

        out_path = f"{self.options.instance_name}.{self.options.instance_suffix}.cx2"

        # ---- Build nodes/edges ----
        cx2_nodes = []
        for orbit in self.dfs_state_orbits:
            nid = int(orbit.repr_int)
            name = orbit.repr_state
            cx2_nodes.append({
                "id": nid,
                "v": {
                    "name": name + "\norbit size: " + str(len(orbit.states))
                }
            })

        IGNORE = {"qrm_init_protocol"}
        cx2_edges = []
        for eid, ((src, dst), act) in enumerate(sorted((self.dfs_explored_edge_labels or {}).items()), start=1):
            if str(act).casefold() in IGNORE:
                continue
            cx2_edges.append({"id": eid, "s": int(src), "t": int(dst), "v": {"label": str(act[0])}})

        network_name = f"{self.options.instance_name}.{self.options.instance_suffix}"

        # ---- Write CX2 via ndex2 ----
        net = CX2Network()
        for n in cx2_nodes:
            net.add_node(node_id=n["id"], attributes=n["v"])
        for e in cx2_edges:
            net.add_edge(edge_id=e["id"], source=e["s"], target=e["t"], attributes=e["v"])
        net.set_network_attributes({"name": network_name})

        def color_from_string(s: str, sat=0.7, light=0.5) -> str:
            """
            Deterministically map a string to a vivid HEX color.
            - hue: hash-based 0..360
            - saturation/lightness: fixed for readability
            """
            h = int(hashlib.sha1(s.encode("utf-8")).hexdigest(), 16)
            hue = (h % 360) / 360.0
            r, g, b = colorsys.hls_to_rgb(hue, light, sat)  # colorsys uses HLS (L before S)
            return f"#{int(r*255):02X}{int(g*255):02X}{int(b*255):02X}"

        def build_edge_color_mapping(cx2_edges, attr="label"):
            """
            Collect unique string values from edge attribute `attr`
            and return an 'edgeMapping' entry
            """
            vals = []
            for e in cx2_edges:
                v = e.get("v", {}).get(attr)
                if v is not None:
                    vals.append(str(v))
            unique_vals = sorted(set(vals))
            return {
                "EDGE_LINE_COLOR": {
                    "type": "DISCRETE",
                    "definition": {
                        "attribute": attr,
                        "type": "string",
                        "map": [{"v": v, "vp": color_from_string(v)} for v in unique_vals],
                        "default": "#7A7A7A"
                    }
                }
            }
        
        

        # Map node labels from the 'name' column; edge labels from 'label'
        vis = {
            "default": {
                "network": {"NETWORK_BACKGROUND_COLOR": "#FFFFFF"},
                "node":    {"NODE_SHAPE": "round-rectangle",
                            "NODE_WIDTH": 80.0,
                            "NODE_HEIGHT": 60.0,},
                "edge":    {
                    "EDGE_TARGET_ARROW_SHAPE": "triangle",
                    "EDGE_TARGET_ARROW_SIZE": 8.0,
                    "EDGE_SOURCE_ARROW_SHAPE": "none"
                }
            },

            "edge": {
                "EDGE_LABEL_POSITION": {
                    "JUSTIFICATION": "center",
                    "MARGIN_X": 0.0,
                    "MARGIN_Y": 8.0,
                    "EDGE_ANCHOR": "N",
                    "LABEL_ANCHOR": "S"
                },
                "EDGE_LABEL_BACKGROUND_SHAPE": "round-rectangle",
                "EDGE_LABEL_BACKGROUND_COLOR": "#FFFFFF",
                "EDGE_LABEL_BACKGROUND_OPACITY": 1.0
            },


            "nodeMapping": {
                "NODE_LABEL": {
                    "type": "PASSTHROUGH",
                    "definition": {"attribute": "name", "type": "string"}
                }
            },

            "edgeMapping": {
                "EDGE_LABEL": {
                    "type": "PASSTHROUGH",
                    "definition": {"attribute": "label", "type": "string"}
                }
            }
        }

        edge_color_map = build_edge_color_mapping(cx2_edges, attr="label")
        vis["edgeMapping"].update(edge_color_map)
        net.set_visual_properties(vis)

        net.write_as_raw_cx2(out_path)
        vprint(self.options, f"[FW NOTE]: wrote CX2 to {out_path}", 3)

    #------------------------------------------------------------
    # SymDFS: public methods
    #------------------------------------------------------------
    def forward_reachability(self):
        self._symmetric_quotient_depth_first_search_reachability()
        self._update_protocol_states()
        self._clean()
        self._print_dfs_statistics()
        self._print_reachability()
        self._print_transition_edges()
        self._render_state_orbit_graph()
        self._export_state_orbit_graph_cx2()
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
        self.bdd   = Bdd(self.options, self.fmla)
        vprint(self.options, 'start symbolic image computation', 5)
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
        vprint(self.options, 'start extracting cubes', 5)
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