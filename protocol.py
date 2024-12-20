import re
from typing import Dict,List,Set, Tuple
from itertools import permutations, product
from ivy import ivy_logic as il
from transition_system import TransitionSystem
from util import QrmOptions, SET_DELIM, SET_ELEM_DELIM
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

class Protocol():
    # static data
    def __init__(self, options : QrmOptions) -> None:
        ## helper
        self.lines         = []
        self.header        = []
        # member datas
        self.sorts            : List[str]            = [] # sort id -> sort name 
        self.sort_constants   : List[List[str]]      = [] # sort id -> constant names
        self.sort_Name2Id     : Dict[str,int]        = {} # sort name -> sort id
        self.constant_Name2Id : Dict[str,int]        = {} # const name -> const id
        self.predicates       : Dict[str,List[str]]  = {} # (function/constant name, [argsort1, argsort2, ..])
        self.atom_num         : int                  = 0
        self.state_atom_num     : int                = 0
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
        self.reachable_states : List[str] = [] 
        self.repr_states      : Set[int]  = set()
        self.quotient_reachable_states : List[str] = [] 
        self._sorts_permutations  = []              
        self.options = options

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

    def init_sorts_permutations(self, tran_sys : TransitionSystem) -> None:
        all_sorts_permutations = []
        for sort_id, constants in enumerate(self.sort_constants):
            sort_name     = self.sorts[sort_id]
            const_id_list = tuple(range(len(constants)))
            if tran_sys.get_finite_sort_from_sort_name(sort_name) in tran_sys.dep_types:
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

    def set_quotient_reachabiliy(self, state_array, remove_atom_ids : Set[int]):
        if len(remove_atom_ids) == 0:
            self.quotient_reachable_states = self.reachable_states
        else:
            for atom_id in remove_atom_ids:
                state_array[:, atom_id] = '-'
            self.quotient_reachable_states = [''.join(row) for row in state_array.tolist()]