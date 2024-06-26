import re
from typing import Dict,List,Set, Tuple
from itertools import permutations, product
from transition import TransitionSystem
from util import QrmOptions, SET_DELIM
from verbose import *

# utils
set_delim = SET_DELIM
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

def new_insert(obj, obj_set: Set[str]) -> bool:
    key = str(obj)
    if not key in obj_set:
        obj_set.add(key)
        return True
    return False

class Protocol():
    # static data
    def __init__(self, options : QrmOptions, filename='') -> None:
        ## helper
        self.lines         = []
        # member datas
        self.sorts            : List[str]            = [] # sort id -> sort name 
        self.sort_constants   : List[List[str]]      = [] # sort id -> constant names
        self.sort_Name2Id     : Dict[str,int]        = {} # sort name -> sort id
        self.constant_Name2Id : Dict[str,int]        = {} # const name -> const id
        self.predicates       : Dict[str,List[str]]  = {} # (function/constant name, [argsort1, argsort2, ..])
        self.atom_num         : int                  = 0
        self.atoms            : List[str]            = [] # atom id -> atom name
        self.atoms_fmla                              = []
        self.atom_Name2Id     : Dict[str,int]        = {} # atom name -> atom id
        self.atom_sig         : List[List[str]]      = [] # atom id -> [predname, arg1, arg2,..]
        self.set_name2elem_sort_id  : Dict[str, int] = {} # quorum name -> member sort id
        self.reachable_states : List[str] = [] 
        self._sorts_permutations  = []              
        self.options = options

        # initialization 
        if filename != '':
            self.read(filename)
            self._init_sorts_permutations()

    def _read_sort(self, line : str) -> None:
        # read '.s [sort_name] [constant1] [constant2] ...'
        # .s node n1 n2
        sort_id     = len(self.sorts)
        (sort, constants) = split_head_tail(line, head=1)
        self.sorts.append(sort)
        self.sort_constants.append(constants)
        self.sort_Name2Id[sort] = sort_id
        for (id, e) in enumerate(constants):
            self.constant_Name2Id[e]=id

    def _read_dependent_sort(self, line : str) -> None:
        # read '.d [member sort] [quorum1] [quorum2] ...' 
        # .d node quorum-n1-n2 quorum-n1-n3 quorum-n2-n3 ...
        (sort, sets) = split_head_tail(line, head=1) 
        sort_id = self.sort_Name2Id[sort]
        for name in sets:
            self.set_name2elem_sort_id[name] = sort_id

    def _read_predicate(self, line : str) -> None:
        # read '.p [predicate_name] [argsort1] [argsort2] ...'
        # .p hold node
        (pred, arg_sorts) = split_head_tail(line, head=1)
        self.predicates[pred] = arg_sorts 

    def _read_atoms(self, line:str) -> None:
        # read '.a [atom1] [atom2] ...'
        # .a hold(n1) hold(n2)
        atoms = line.split()[1:] # remove '.a'
        self.atom_num = len(atoms)
        assert( len(atoms) == self.atom_num )
        for (id,atom) in enumerate(atoms):
            predicate = '' 
            args = []
            match_pred = re.search(r'(\w+)\(([^)]+)\)',  atom)
            match_eq   = re.search(r'\((\w+)=([^)]+)\)', atom)
            match_func_eq = re.search(r'\((\w+)\((\w+)\)=([^)]+)\)', atom)
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
            self.atom_Name2Id[atom]  = id
            signature = [predicate] + args
            self.atom_sig.append(signature)

    def _read_states(self, line:str, states=set()) -> None:
        # read '[reachable_state]'
        # 010-
        state = line.split()[0]
        assert( len(state) == self.atom_num )
        if not state in states:
            self.reachable_states.append(state)

    def read(self, filename: str) -> None:
        with open(filename, 'r') as file:
            states = set() # avoid reading repeated state
            for line in file:
                if line.startswith('.s'):
                    self._read_sort(line)
                if line.startswith('.d'):
                    self._read_dependent_sort(line)
                if line.startswith('.p'):
                    self._read_predicate(line)                    
                if line.startswith('.a'):
                    self._read_atoms(line)
                if not line.startswith('.') and not line.startswith('#'):
                    self._read_states(line, states)

    def init_sort(self, tran_sys : TransitionSystem) -> None:
        for (sort, sort_consts) in tran_sys.sort2consts.items():
            sort_name   = tran_sys.get_sort_name_from_finite_sort(sort)
            sort_consts = tran_sys.get_pretty_constants_of_sort(sort_name)
            line = '.s ' + sort_name + ' ' + ' '.join(sort_consts)
            self._read_sort(line) 
            if self.options.writeReach or self.options.verbosity > 3:
                self.lines.append(line)

    def init_dependent_sort(self, tran_sys : TransitionSystem) -> None:
        for (set_sort, dep_type) in tran_sys.dep_types.items():
            elem_sort = tran_sys.get_dependent_element_sort(set_sort)
            line = '.d ' +  tran_sys.get_sort_name_from_finite_sort(elem_sort)
            for set_id in range(len(dep_type.sets)):
                line  += ' ' + tran_sys.get_pretty_set(set_sort, set_id) 
            self._read_dependent_sort(line)
            if self.options.writeReach or self.options.verbosity > 3:
                self.lines.append(line) 

    def init_predicate(self, tran_sys : TransitionSystem) -> None:
        for var in tran_sys.get_state_variables():
            line  = '.p ' + str(var)
            eq_term    = ''
            param_list = []
            var_sym = var.symbol_type()
            if not var_sym.is_function_type():
                if not var.is_literal(): # case1: (start_node = n0)
                    param_list = [str(var_sym)]
                    eq_term    = '='
                # else case2: bool type, no parameters 
            else: # case3: predicate/case 4: function (predicate is a function with return type bool)
                param_list =  [str(s) for s in var_sym._param_types]
            # case 4: general function (dst(p0) = n0)
            if (var_sym.is_function_type() and
               not var_sym._return_type.is_bool_type()): 
               eq_term = '='
               param_list.append(str(var_sym._return_type))
            
            line += eq_term
            if len(param_list) > 0:
                line += ' ' + ' '.join(param_list)
            
            self._read_predicate(line)
            if self.options.writeReach or self.options.verbosity > 3:
                self.lines.append(line)

    def init_atoms(self, atoms, atoms_fmla) -> None:
        line = '.a'
        for atom in atoms:
            predicate = '' 
            args     = []
            match_pred    = re.search(r'(\w+)\(([^)]+)\)',  atom)
            match_eq      = re.search(r'\((\w+)\s*=\s*(\w+)\)', atom)
            match_func_eq = re.search(r'\((\w+)\((\w+)\)=(\w+)\)', atom)
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
            line +=  ' ' + atom
        self._read_atoms(line)
        self.atoms_fmla = atoms_fmla
        if self.options.writeReach or self.options.verbosity > 3:
            self.lines.append(line)

    def init_reachable_states(self, states) -> None:
        for state in states:
            self._read_states(state)
            if self.options.writeReach or self.options.verbosity > 3:
                self.lines.append(state)

    def init_sorts_permutations(self) -> None:
        all_sorts_permutations = []
        for constants in self.sort_constants:
            const_id_list = list(range(len(constants)))
            sort_permutations = permutations(const_id_list)
            all_sorts_permutations.append(sort_permutations)
        # cartesian product
        self._sorts_permutations = list(product(*all_sorts_permutations))

    def write_reachability(self) -> None:
        filename = self.options.instance_name + '.' + self.options.instance_suffix + '.pctl'
        outF = open(filename, "w")
        for line in self.lines:
            outF.write(line+'\n')
        outF.write('.e\n')
        outF.close()

    def print_verbose(self) -> None:
        vprint_step_banner(self.options, f'[FW RESULT]: Forward Reachability on [{self.options.instance_name}: {self.options.size_str}]', 3)
        vprint(self.options, '\n'.join(self.lines), 3)
        vprint(self.options, f'[FW NOTE]: number of variables: {self.atom_num}', 2)
        vprint(self.options, f'[FW NOTE]: number of reachable states: {len(self.reachable_states)}', 2)
    
    def _get_renamed_arguments(self, permutation, sort_id, arguments) -> str:
        new_constant = []
        for const in arguments:
            old_constant_id = self.constant_Name2Id[const]
            new_constant_id = permutation[sort_id][old_constant_id]
            new_constant.append(self.sort_constants[sort_id][new_constant_id])
        new_constant.sort()
        return set_delim.join(new_constant)

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
                (prefix, elements) = split_head_tail(arg, head=0, delim=set_delim) 
                sort_id = self.set_name2elem_sort_id[arg]
                narg = (prefix + set_delim)
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
            nvalues[nid] = val 
        return nvalues

    def all_permutations(self, values : List[str]) -> List[List[str]]:
        # values is a list of '0', '1', '-'
        assert( len(values) == self.atom_num )
        values_list = [] 
        values_hash  = set() # avoid repeated insertion
        for perm in self._sorts_permutations:
            nvalues = self._permute_values(perm, values)
            if nvalues and new_insert(nvalues, values_hash):
                values_list.append(nvalues)
        return values_list 