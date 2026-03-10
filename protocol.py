import re
from typing import Dict,List,Set, Tuple
from itertools import permutations, product
from ivy import ivy_logic as il
from transition_system import TransitionSystem
from finite_ivy_instantiate import FiniteIvyInstantiator
from util import QrmOptions, SET_DELIM, SET_ELEM_DELIM, ForwardMode
from verbose import *
import numpy as np

# utils
def format_relational_atom(function: str, args: List[str]) -> str:
    return function + '(' + ','.join(args) + ')'

def format_equal_atom(function: str, args: List[str]) -> str:
    lhs    = function.strip('=')
    params = args[:-1]
    rhs    = args[-1]
    atom   = ''
    if len(params) > 0:
        atom = '(' + lhs + '(' + ','.join(params) + ')=' + rhs + ')'
    else:
        atom =  '(' + lhs + '=' + rhs + ')'
    return atom

def split_head_tail(line: str, head : int, delim=None) -> Tuple [str, List[str]]:
    lst = line.split(delim)
    return (lst[head], lst[head+1:])

def parse_set_constant(set_const: str) -> Tuple [str, List[str]]:
    lst = set_const.split(SET_DELIM)
    set_name   = lst[0]
    elems      = lst[1].split(SET_ELEM_DELIM)
    return (set_name, elems)

def new_insert(obj, obj_set: Set[str]) -> bool:
    key = str(obj)
    if not key in obj_set:
        obj_set.add(key)
        return True
    return False

def get_func_args(atom):
    args = None
    if il.is_eq(atom):
        lhs = atom.args[0]
        args = []
        if isinstance(lhs, il.App):
            args += list(lhs.args)
        args.append(atom.args[1])
        args = tuple(args)
    elif isinstance(atom, il.App) or il.is_boolean(atom):
        args = atom.args
    return args

class Protocol():
    # static data
    def __init__(self, options : QrmOptions) -> None:
        ## helper
        self.lines   = []
        self.header  = []
        self.options = options
        # member datas
        self.sorts            : List[str]            = [] # sort id -> sort name 
        self.sort_constants   : List[List[str]]      = [] # sort id -> constant names
        self.sort_Name2Id     : Dict[str,int]        = {} # sort name -> sort id
        self.constant_Name2Id : Dict[str,int]        = {} # const name -> const id
        self.predicates       : Dict[str,tuple[str, ...]]  = {} # (function/constant name, [argsort1, argsort2, ..])
        self.atom_num         : int                  = 0
        self.state_atom_num     : int                = 0  # = total amount of bits needed to repersent the state.
        self.interpreted_atom_num : int              = 0
        self.atoms            : List[str]            = [] # atom id -> atom name
        self.state_atoms                             = [] # atoms = state_atoms + interpreted_atoms
        self.interpreted_atoms                       = []
        self.atoms_fmla                              = [] # atoms_fmla = state_atoms_fmla + interpreted_atoms_fmla
        self.state_atoms_fmla                        = []
        self.interpreted_atoms_fmla                  = []
        self.interpreted_atoms_values                = {} 
        self.atom_Name2Id     : Dict[str,int]        = {} # atom name -> atom id
        self.atom_sig         : List[List[str]]      = [] # atom id -> [predname, arg1, arg2,..]
        self.set_name2elem_sort_id  : Dict[str, int] = {} # quorum name -> member sort id
        self._sorts_permutations  = []
        # reachability
        self.reachable_states : List[str] = [] 
        self.repr_states      : Set[int]  = set()
        self.bit_repr_states : Set[str] = set()
        # equivalence quotient data structures
        self.atom2equivs      = {} 
        self.atom2complements = {}
        self.remove_atom_ids  = set()
        self.quotient_reachable_states : List[str] = []
        # reachable states >= unreachable states
        self.more_reach : bool

    def init_sort(self, tran_sys : TransitionSystem) -> None:
        for sort in tran_sys.sort2consts.keys():
            sort_name   = tran_sys.get_sort_name_from_finite_sort(sort)
            consts_str  = tran_sys.get_sort_constants_str(sort)
            sort_id     = len(self.sorts)
            self.sorts.append(sort_name)
            self.sort_constants.append(consts_str)
            self.sort_Name2Id[sort_name] = sort_id
            for (const_id, const) in enumerate(consts_str):
                self.constant_Name2Id[const]=const_id
            if self.options.writeReach or self.options.verbosity > 3:
                self.header.append(f'sort: {sort_name}={consts_str}')

    def init_dependent_sort(self, tran_sys : TransitionSystem) -> None:
        for (set_sort, dep_type) in tran_sys.dep_types.items():
            elem_sort = tran_sys.get_dependent_element_sort(set_sort)
            elem_sort_name = tran_sys.get_sort_name_from_finite_sort(elem_sort)
            sets = []
            for set_id in range(len(dep_type.sets)):
                sets.append(tran_sys.get_set_label(set_sort, set_id))
            sort_id = self.sort_Name2Id[elem_sort_name]
            for name in sets:
                self.set_name2elem_sort_id[name] = sort_id

    def init_predicate(self, tran_sys : TransitionSystem) -> None:
        for var in tran_sys.symbols:
            pred_name  = str(var)
            param_list = []
            var_type = var.sort
            if not il.is_function_sort(var_type):
                if not il.is_boolean_sort(var_type): # case1: (start_node = n0)
                    param_list = [tran_sys.get_sort_name_from_finite_sort(var_type)]
                    pred_name += '='
                # else case2: bool type, no parameters 
            else: # case3: predicate/case 4: function (predicate is a function with return type bool)
                param_list =  [tran_sys.get_sort_name_from_finite_sort(sort) for sort in list(var_type.dom)]
            # case 4: general function (dst(p0) = n0)
            if (il.is_function_sort(var_type) and
               not il.is_boolean_sort(var_type.rng)): 
               pred_name += '='
               param_list.append(tran_sys.get_sort_name_from_finite_sort(var_type.rng))
            param_list = tuple(param_list) 
            self.predicates[pred_name] = param_list
            if self.options.writeReach or self.options.verbosity > 3:
                self.header.append(f'predicate: {pred_name}{param_list}')

    def init_atoms(self, state_atoms, state_atoms_fmla, interpreted_atoms, interpreted_atoms_fmla) -> None:
        atoms      = state_atoms + interpreted_atoms
        atoms_fmla = state_atoms_fmla + interpreted_atoms_fmla
        self.atom_num               = len(atoms)
        self.state_atom_num         = len(state_atoms)
        self.interpreted_atom_num   = len(interpreted_atoms)
        self.atoms_fmla             = atoms_fmla
        self.state_atoms_fmla       = state_atoms_fmla
        self.interpreted_atoms_fmla = interpreted_atoms_fmla
        for atom_id, atom in enumerate(atoms):
            predicate = '' 
            args     = []
            match_pred    = re.search(r'([\w.]+)\(([^)]+)\)',  atom)
            match_eq      = re.search(r'([\w.]+)\s*=\s*(\w+)', atom)
            match_func_eq = re.search(r'([\w.]+)\((\w+)\) = (\w+)', atom)
            if match_func_eq: # case 4: general function
                predicate = match_func_eq.group(1) + '='
                args      = match_func_eq.group(2).split(', ') + match_func_eq.group(3).split(', ')
            elif match_pred: # case 3: predicate 
                predicate = match_pred.group(1)
                args      = match_pred.group(2).split(',')
            elif match_eq: # case 1
                predicate = match_eq.group(1) + '='
                args      = match_eq.group(2).split(',')
            else: # case 2: bool
                predicate = atom.strip('( )')

            if match_func_eq or match_eq:
                atom = format_equal_atom(predicate, args)
            else:
                atom = format_relational_atom(predicate, args)
            self.atoms.append(atom)
            self.atom_Name2Id[atom] = atom_id
            signature = [predicate] + args
            self.atom_sig.append(signature)
        self.state_atoms          = self.atoms[:self.state_atom_num]
        self.interpreted_atoms    = self.atoms[self.state_atom_num:]

    def init_reachable_states(self, interpreted_state, states) -> None:
        self.interpreted_atoms_values = {atom:val for (atom,val) in zip(self.interpreted_atoms, interpreted_state)}
        for state in states:
            assert( len(state) == self.state_atom_num )
            self.reachable_states.append(state)
            if self.options.writeReach or self.options.verbosity > 3:
                self.lines.append(state)
        if self.options.writeReach or self.options.verbosity > 3:
            self.header.append(f'interpreted atoms: {self.interpreted_atoms_values}')
            self.header.append(f'state atoms: {self.state_atoms}')

    def init_representative_states(self, repr_states : List[int]) -> None:
        self.repr_states = set(repr_states)
        # Convert repr_states to bitstrings and truncate to only state atoms (from the left)
        self.bit_repr_states = {
            '{0:0{1}b}'.format(repr_int, self.atom_num)[:self.state_atom_num]
            for repr_int in repr_states
        }
        if self.options.writeReach or self.options.verbosity > 3:
            self.header.append(f'representative states : {', '.join([str(s) for s in repr_states])}')

    def init_sorts_permutations(self, tran_sys : TransitionSystem) -> None:
        all_sorts_permutations = []
        for sort_id, constants in enumerate(self.sort_constants):
            sort_name     = self.sorts[sort_id]
            const_id_list = tuple(range(len(constants)))
            if (tran_sys.get_finite_sort_from_sort_name(sort_name) in tran_sys.dep_types
                or sort_name in tran_sys.ordered_sorts):
                all_sorts_permutations.append([const_id_list])
            else:
                sort_permutations = permutations(const_id_list)
                all_sorts_permutations.append(sort_permutations)
        # cartesian product
        self._sorts_permutations = list(product(*all_sorts_permutations))

    def write_reachability(self) -> None:
        filename = self.options.instance_name + '.' + self.options.instance_suffix + '.reach'
        outF = open(filename, "w")
        for line in self.header:
            outF.write(line+'\n')
        for line in self.lines:
            outF.write(line+'\n')
        outF.close()

    def _get_renamed_arguments(self, permutation, sort_id, arguments) -> str:
        new_constant = []
        for const in arguments:
            old_constant_id = self.constant_Name2Id[const]
            new_constant_id = permutation[sort_id][old_constant_id]
            new_constant.append(self.sort_constants[sort_id][new_constant_id])
        new_constant.sort()
        return SET_ELEM_DELIM.join(new_constant)

    def _get_renamed_atom(self, permutation, atom_id) -> str:
        signature = self.atom_sig[atom_id]
        predicate = signature[0]
        args      = signature[1:]
        argsorts  = self.predicates[predicate]
        new_args  = []
        # get new arguements
        for (arg_id, arg) in enumerate(args):
            narg = ''
            if arg in self.set_name2elem_sort_id:
                (prefix, elements) = parse_set_constant(arg) 
                sort_id = self.set_name2elem_sort_id[arg]
                narg = (prefix + SET_DELIM)
                narg += self._get_renamed_arguments(permutation, sort_id, elements)
            else:
                sort    = argsorts[arg_id]
                sort_id = self.sort_Name2Id[sort]
                narg = self._get_renamed_arguments(permutation, sort_id, [arg])
            new_args.append(narg)       
        if predicate.endswith('='):
            return format_equal_atom(predicate, new_args)
        else: 
            return format_relational_atom(predicate, new_args)
    
    def _to_binary(self, x : int, size : int) -> str:
        s = ""
        while x > 0:
            s = s + str(int(x % 2))
            x = int(x / 2)
        while len(s) < size:
            s = s + "0"
        return s[::-1] # reverses the string

    # This is a very slow function because the unreachable states grows exponentianly
    def get_unreachable_states(self):
        size = len(self.reachable_states[0])
        l : List[str] = []
        for i in range(pow(2,size)):
            num = self._to_binary(i, size)
            if not (num in self.reachable_states):
                l.append(num)
        return l


    def _permute_values(self, permutation, values : List[str]) -> List[str]:
        # values is a list of '0', '1', '-'
        nvalues = ['-']*len(values)
        for (id, val) in enumerate(values):
            if val == '-': # don't care 
                continue
            atom = self._get_renamed_atom(permutation, id)
            if not atom in self.atom_Name2Id: # invalid permutation
                return []
            nid = self.atom_Name2Id[atom]
            assert(nid < self.state_atom_num)
            nvalues[nid] = val 
        return nvalues

    #------------------------------------------------------------
    # Protocol: equivalence reduction 
    #------------------------------------------------------------
    def _get_state_array_from_state_list(self):
        # Convert list of strings to a 2D numpy array
        state_list = self.reachable_states
        return np.array([list(s) for s in state_list])

    def _set_equivalent_complement_atoms(self, state_array):
        atom_num = self.state_atom_num
        for i in range(atom_num-1):
            if i in self.remove_atom_ids:
                continue
            for j in range(i+1, atom_num):
                if j in self.remove_atom_ids:
                    continue
                atom_i = self.atoms_fmla[i] 
                atom_j = self.atoms_fmla[j]
                if get_func_args(atom_i) != get_func_args(atom_j):
                    continue
                if np.array_equal(state_array[:, i], state_array[:, j]):
                    if not atom_i in self.atom2equivs:
                        self.atom2equivs[atom_i] = []
                    self.atom2equivs[atom_i].append(atom_j)
                    self.remove_atom_ids.add(j)
                else: 
                    str_i = ''.join(state_array[:, i])
                    str_j = ''.join(state_array[:, j])
                    if self.options.forward_mode == ForwardMode.BDD_Symbolic:
                        if '-' in str_i or '-' in str_j:
                            continue
                    if int(str_i, 2) + int(str_j, 2) == int('1'*atom_num, 2):  # complement
                        if not atom_i in self.atom2complements:
                            self.atom2complements[atom_i] = []
                        self.atom2complements[atom_i].append(atom_j)
                        self.remove_atom_ids.add(j)

    def _set_quotient_reachabiliy(self, state_array):
        if len(self.remove_atom_ids) == 0:
            self.quotient_reachable_states = self.reachable_states
        else:
            for atom_id in self.remove_atom_ids:
                state_array[:, atom_id] = '-'
            self.quotient_reachable_states = [''.join(row) for row in state_array.tolist()]

    def _reduce_equivalent_atoms(self, tran_sys : TransitionSystem):
        # equivalence reduced states (post-processing)
        state_array = self._get_state_array_from_state_list()
        self._set_equivalent_complement_atoms(state_array)
        self._set_quotient_reachabiliy(state_array)
        tran_sys.set_atom_equivalence_constraints(self.atom2equivs, self.atom2complements)

    def _print_equiv_reduction_info(self) -> None:
        vprint(self.options, f'[FW NOTE]: equivalent atoms', 2)
        for atom, equivs in self.atom2equivs.items():
            vprint(self.options, f'\t{str(atom)}: {[str(e) for e in equivs]}', 2)
        vprint(self.options, f'[FW NOTE]: complement atoms', 2)
        for atom, cmpls in self.atom2complements.items():
            vprint(self.options, f'\t{str(atom)}: {[str(c) for c in cmpls]}', 2)
        vprint(self.options, f'[FW NOTE]: remove_atom_ids: {self.remove_atom_ids}', 2)

    #------------------------------------------------------------
    # Protocol: public methods 
    #------------------------------------------------------------
    def init_protocol_from_file(self, tran_sys : TransitionSystem, instantiator : FiniteIvyInstantiator):
        vprint_title(self.options, 'Initializing reachability from file', 5)
        self.init_sort(tran_sys)
        self.init_dependent_sort(tran_sys)
        self.init_predicate(tran_sys)
        self.init_atoms(instantiator.protocol_state_atoms, instantiator.protocol_state_atoms_fmlas,
                        instantiator.protocol_interpreted_atoms, instantiator.protocol_interpreted_atoms_fmlas)
        self.init_sorts_permutations(tran_sys)
        filename = self.options.instance_name + '.' + self.options.instance_suffix + '.reach'
        with open(filename, 'r') as reach_file: 
            for line in reach_file:
                if (line.startswith('sort') or 
                    line.startswith('predicate') or 
                    line.startswith('interpreted atoms') or 
                    line.startswith('state atoms')):
                    continue
                elif line.startswith('representative states'):
                    repr_states_str  = line.strip().split(' : ')[1].split(', ')
                    repr_states_int  = [(int(t)) for t in repr_states_str]
                    self.repr_states = set(repr_states_int)
                else:
                    state = line.strip()
                    assert( len(state) == self.state_atom_num )
                    self.reachable_states.append(state)

        self.more_reach = bool(int(round(len(self.reachable_states)/pow(2,self.state_atom_num))))
        
        vprint(self.options, 'Reachability successfully initialized', 5)

    def reduce_equivalent_atoms(self, tran_sys : TransitionSystem):
        self._reduce_equivalent_atoms(tran_sys)
        self._print_equiv_reduction_info()

    def all_permutations(self, values : List[str]) -> List[List[str]]:
        # values is a list of '0', '1', '-'
        assert( len(values) == self.state_atom_num ) # only permute the mutable part
        values_list = [] 
        values_hash  = set() # avoid repeated insertion
        for perm in self._sorts_permutations:
            nvalues = self._permute_values(perm, values)
            if nvalues and new_insert(nvalues, values_hash):
                values_list.append(nvalues)
        return values_list 
    
    def get_function_symbol_from_atom(self, atom_fmla):
        if il.is_constant(atom_fmla):
            return atom_fmla
        elif il.is_eq(atom_fmla):
            return self.get_function_symbol_from_atom(atom_fmla.args[0])
        elif il.is_app(atom_fmla):
            return atom_fmla.func
        raise AssertionError(f"Couldn't get function symbol from atom {atom_fmla}")

    #------------------------------------------------------------
    # Protocol: curry methods 
    #------------------------------------------------------------
    
    def curry_ordered_sorts(self, tran_sys: TransitionSystem) -> 'Protocol':
        """
        Create a curried copy of this protocol with ordered sorts flattened.
        
        For atoms like voted(epoch, node):
        - voted(epoch0, node) → voted_epoch0(node)
        - voted(epoch1, node) → voted_epoch1(node)
        
        Returns a new Protocol with curried atom names. The original protocol is unchanged.
        
        Returns:
            Protocol: A new protocol with curried state atoms, or self if no currying needed.
        """
        if not tran_sys.ordered_sorts:
            vprint(self.options, "[CURRY]: No ordered sorts detected, skipping curry", 3)
            return self
        
        vprint_title(self.options, 'Currying Ordered Sorts', 3)
        
        # Step 1: Identify atoms to curry and build currying map
        curry_map = self._build_curry_map(tran_sys)
        
        if not curry_map:
            vprint(self.options, "[CURRY]: No atoms need currying", 3)
            return self
        
        # Step 2: Create a deep copy of the protocol
        curried = self._deep_copy()
        
        # Step 3: Update atom metadata with curried names in the copy
        curried._apply_curry_map(curry_map, tran_sys)
        
        vprint(self.options, f"[CURRY]: curried {len(curry_map)} atoms", 3)
        vprint(self.options, f"[CURRY]: curried state atoms: {curried.state_atoms}")
        
        return curried
    
    def _build_curry_map(self, tran_sys: TransitionSystem) -> Dict:
        """
        Build mapping from original atom_id to its curried form.
        
        Each atom maps to exactly one curried atom based on which epoch constant it contains.
        Example: transfer(epoch0, node0) → transfer_epoch0(node0)
        
        Returns:
            Dict[int, Tuple]: Maps atom_id -> (curried_atom_name, curried_pred, curried_args)
        """
        curry_map = {}
        ordered_sort_names = set(tran_sys.ordered_sorts.keys())
        
        for atom_id, atom_sig in enumerate(self.atom_sig):
            if atom_id >= self.state_atom_num:
                break  # Only curry state atoms, not interpreted atoms
            
            pred_name = atom_sig[0]
            args = atom_sig[1:]
            
            # Find ordered sort arguments
            ordered_arg_idx = None
            ordered_const = None
            
            for arg_idx, arg in enumerate(args):
                # Check if this argument is from an ordered sort
                for sort_name in ordered_sort_names:
                    sort_consts = self.sort_constants[self.sort_Name2Id[sort_name]]
                    if arg in sort_consts:
                        ordered_arg_idx = arg_idx
                        ordered_const = arg
                        break
                if ordered_const:
                    break
            
            # Only curry if atom has exactly one ordered-sort argument
            if ordered_const is not None and ordered_arg_idx is not None:
                # Create curried name: pred_epoch0, pred_epoch1, etc.
                # If the predicate is an equality, ensure the equal sign stays at the end.
                if pred_name[-1] == '=':
                    curried_pred = f"{pred_name[:-1]}_{ordered_const}"
                else:
                    curried_pred = f"{pred_name}_{ordered_const}"
                
                # Build curried args (remove ordered arg)
                curried_args = args[:ordered_arg_idx] + args[ordered_arg_idx+1:]
                
                # Create full curried atom name
                if curried_args:
                    curried_atom = curried_pred + '(' + ','.join(curried_args) + ')'
                else:
                    curried_atom = curried_pred
                
                curry_map[atom_id] = (curried_atom, curried_pred, curried_args)
        
        return curry_map
    
    def _apply_curry_map(self, curry_map: Dict, tran_sys: TransitionSystem):
        """
        Apply the curry map to update atom metadata with curried names.
        This modifies self in-place (used on a copy).
        """
        # Build new state atoms list and signature
        new_state_atoms = []
        new_atom_sig = []
        new_atom_Name2Id = {}
        new_predicates = self.predicates.copy()
        
        for atom_id in range(self.state_atom_num):
            if atom_id in curry_map:
                # This atom gets curried (renamed)
                curried_atom, curried_pred, curried_args = curry_map[atom_id]
                new_state_atoms.append(curried_atom)
                new_atom_sig.append([curried_pred] + curried_args)
                new_atom_Name2Id[curried_atom] = atom_id
                
                # Add curried predicate to predicates dict if not already there
                if curried_pred not in new_predicates:
                    # Get the argument sorts for the curried predicate (without the ordered sort)
                    orig_pred = self.atom_sig[atom_id][0]
                    if orig_pred in self.predicates:
                        orig_arg_sorts = self.predicates[orig_pred]
                        # Find which argument was the ordered sort and remove it
                        ordered_sort_names = set(tran_sys.ordered_sorts.keys())
                        curried_arg_sorts = []
                        for sort in orig_arg_sorts:
                            if sort not in ordered_sort_names:
                                curried_arg_sorts.append(sort)
                        new_predicates[curried_pred] = tuple(curried_arg_sorts)
            else:
                # This atom stays as-is
                new_state_atoms.append(self.state_atoms[atom_id])
                new_atom_sig.append(self.atom_sig[atom_id])
                new_atom_Name2Id[self.state_atoms[atom_id]] = atom_id
        
        # State strings remain unchanged - same number of atoms, just renamed
        # No need to modify reachable_states
        
        # Update protocol metadata
        self.state_atoms = new_state_atoms
        self.atom_sig = new_atom_sig + self.atom_sig[self.state_atom_num:]  # Keep interpreted atoms
        self.atom_Name2Id = new_atom_Name2Id
        self.predicates = new_predicates
        # state_atom_num stays the same
        
        # Update combined atom lists
        self.atoms = self.state_atoms + self.interpreted_atoms
        self.atoms_fmla = self.state_atoms_fmla + self.interpreted_atoms_fmla
        # atom_num stays the same
        
        # Rebuild state_atoms_fmla with curried predicates
        self._rebuild_curried_formulas(curry_map, tran_sys)
    
    def _rebuild_curried_formulas(self, curry_map: Dict, tran_sys: TransitionSystem):
        """
        Rebuild state_atoms_fmla to use curried predicates and arguments.
        This creates new Ivy formula objects that match the curried atom names.
        """
                
        new_state_atoms_fmla = []
        curried_symbols = {}  # Store curried symbols locally
        
        for atom_id in range(self.state_atom_num):
            orig_fmla = self.state_atoms_fmla[atom_id]
            
            if atom_id in curry_map:
                # This atom was curried - rebuild the formula
                curried_atom, curried_pred, curried_args = curry_map[atom_id]
                
                # Get or create the curried predicate symbol
                if curried_pred not in curried_symbols:
                    # Get the original symbol to determine the type
                    ordered_sort_names = set(tran_sys.ordered_sorts.keys())
                    is_equality_with_ordered_rhs = False
                    
                    if il.is_eq(orig_fmla):
                        # For equality formulas like f(x) = y
                        lhs = orig_fmla.args[0]
                        rhs = orig_fmla.args[1]
                        if isinstance(lhs, il.App):
                            orig_symbol = lhs.func
                        else:
                            orig_symbol = lhs
                        
                        # Check if RHS (return value) is an ordered sort being curried out
                        if hasattr(rhs, 'sort') and tran_sys.get_sort_name_from_finite_sort(rhs.sort) in ordered_sort_names:
                            is_equality_with_ordered_rhs = True
                    elif isinstance(orig_fmla, il.App):
                        orig_symbol = orig_fmla.func
                    else:
                        orig_symbol = orig_fmla
                    
                    # Determine the curried symbol's sort
                    if il.is_function_sort(orig_symbol.sort):
                        orig_dom = list(orig_symbol.sort.dom)
                        orig_rng = orig_symbol.sort.rng
                        
                        # Remove ordered sorts from domain
                        curried_dom = [s for s in orig_dom if tran_sys.get_sort_name_from_finite_sort(s) not in ordered_sort_names]
                        
                        # If the range is an ordered sort being curried, change to boolean
                        if is_equality_with_ordered_rhs:
                            curried_rng = il.BooleanSort()
                        else:
                            curried_rng = orig_rng
                        
                        if len(curried_dom) > 0:
                            curried_sort = il.FunctionSort(*(curried_dom + [curried_rng]))
                        else:
                            # All arguments removed - just the return type
                            curried_sort = curried_rng
                    else:
                        curried_sort = orig_symbol.sort
                    
                    curried_symbols[curried_pred] = il.Symbol(curried_pred, curried_sort)
                
                curried_symbol = curried_symbols[curried_pred]
                
                # Build the curried formula
                # Get the constant objects for the curried args
                curried_arg_consts = []
                for arg_name in curried_args:
                    # Find the constant in the transition system
                    found = False
                    for sort, consts in tran_sys.sort2consts.items():
                        for const in consts:
                            if str(const) == arg_name:
                                curried_arg_consts.append(const)
                                found = True
                                break
                        if found:
                            break
                
                # Construct the new formula
                # Check if this was an equality with ordered sort on RHS - now it's a boolean predicate
                orig_was_equality = il.is_eq(orig_fmla)
                ordered_sort_names = set(tran_sys.ordered_sorts.keys())
                rhs_was_ordered = False
                
                if orig_was_equality:
                    rhs = orig_fmla.args[1]
                    if hasattr(rhs, 'sort') and tran_sys.get_sort_name_from_finite_sort(rhs.sort) in ordered_sort_names:
                        rhs_was_ordered = True
                
                if curried_pred.endswith('=') and not rhs_was_ordered:
                    # Still an equality (ordered sort was in domain, not range)
                    if len(curried_arg_consts) > 1:
                        lhs = il.App(curried_symbol, *curried_arg_consts[:-1])
                    else:
                        lhs = curried_symbol
                    rhs = curried_arg_consts[-1]
                    new_fmla = il.Equals(lhs, rhs)
                elif len(curried_arg_consts) > 0:
                    # Function application or predicate (including former equalities with ordered RHS)
                    new_fmla = il.App(curried_symbol, *curried_arg_consts)
                else:
                    # Boolean constant
                    new_fmla = curried_symbol
                
                new_state_atoms_fmla.append(new_fmla)
            else:
                # This atom wasn't curried - keep original formula
                new_state_atoms_fmla.append(orig_fmla)
        
        # Update the formula lists
        self.state_atoms_fmla = new_state_atoms_fmla
        self.atoms_fmla = self.state_atoms_fmla + self.interpreted_atoms_fmla

    def _deep_copy(self):
        import copy
        saved_options = self.options
        self.options = None  # Temporarily remove to avoid deepcopy issues
        protocol_copy = copy.deepcopy(self)
        self.options = saved_options  # Restore
        protocol_copy.options = saved_options  # Share the same options (read-only)
        return protocol_copy