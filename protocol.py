import re
from typing import Dict,List,Set, Tuple
from itertools import permutations, product
from verbose import *
from util import *

# utils
def format_atom(predicate: str, args: List[str]) -> str:
    return predicate + '(' + ', '.join(args) + ')'

def split_head_tail1(line : str, delim='') -> Tuple [str, List[str]]:
    list = line.split(delim)
    return  (list[1], list[2:])

def split_head_tail0(line: str, delim='') -> Tuple [str, List[str]]:
    list = line.split(delim)
    return (list[0], list[1:])

def is_valid_and_new(toCheck : List[str], pool: Set[str]) -> bool:
    if toCheck:
        key = str(toCheck)
        if not key in pool:
            pool.add(key)
            return True
    return False

quorum_delim = '_'

class Protocol():
    def __init__(self, options : QrmOptions) -> None:
        # member datas
        self.sorts           : List[str]       = [] # sort id -> sort name 
        self.sort_elements   : List[List[str]] = [] # sort id -> elem names
        self.sort_Name2Id    : Dict[str,int]   = {} # sort name -> sort id
        self.element_Name2Id : Dict[str,int]   = {} # elem name -> elem id
        self.predicates    : Dict[str,List[str]] = {} # (predname, [argsort1, argsort2, ..])
        self.atom_num      : int                 = 0
        self.atoms         : List[str]           = [] # atom id -> atom name
        self.atom_Name2Id  : Dict[str,int]       = {} # atom name -> atom id
        self.atom_sig      : List[List[str]]     = [] # atom id -> [predname, arg1, arg2,..]
        self.quorums       : Dict[str, int]      = {} # quorum name -> member sort id
        self.reachable_states : List[str] = [] 
        self._sorts_permutations  = []              

        # initialization 
        self._read(options.filename)
        self._init_sorts_permutations()

    def _read_sort(self, line : str) -> None:
        # read '.s [sort_name] [element1] [element2] ...'
        sort_id     = len(self.sorts)
        (sort, elements) = split_head_tail1(line)
        self.sorts.append(sort)
        self.sort_elements.append(elements)
        self.sort_Name2Id[sort] = sort_id
        for (id, e) in enumerate(elements):
            self.element_Name2Id[e]=id

    def _read_quorums(self, line : str) -> None:
        # read '.q [sort] [quorum1] [quorum2] ...' 
        # quorum format q-n1-n2, q-n1-n3, q-n2-n3
        (sort, quorums) = split_head_tail1(line) 
        sort_id = self.sort_Name2Id[sort]
        for quorum in quorums:
            self.quorums[quorum] = sort_id

    def _read_predicate(self, line : str) -> None:
        # read '.p [predicate_name] [argsort1] [argsort2] ...'
        (pred, arg_sorts) = split_head_tail1(line)
        self.predicates[pred] = arg_sorts 

    def _read_atoms(self, line:str) -> None:
        # read '.a [atom1] [atom2] ...'
        atoms = line.split()[1:] # remove '.a'
        self.atom_num = len(atoms)
        assert( len(atoms) == self.atom_num )
        for (id,atom) in enumerate(atoms):
            match = re.search(r'(\w+)\(([^)]+)\)', atom)
            assert(match)
            predicate = match.group(1)
            args      = match.group(2).split(',')
            atom      = format_atom(predicate,args)
            self.atoms.append(atom)
            self.atom_Name2Id[atom]  = id
            signature = [predicate] + args
            self.atom_sig.append(signature)

    def _read_states(self, line:str, states: Set[str]) -> None:
        # read '[reachable_state]'
        state = line.split()[0]
        assert( len(state) == self.atom_num )
        if not state in states:
            self.reachable_states.append(state)

    def _read(self, filename: str) -> None:
        with open(filename, 'r') as file:
            states = set() # avoid reading repeated state
            for line in file:
                if line.startswith('.s'):
                    self._read_sort(line)
                if line.startswoth('.q'):
                    self._read_quorums(line)
                if line.startswith('.p'):
                    self._read_predicate(line)                    
                if line.startswith('.a'):
                    self._read_atoms(line)
                if not line.startswith('.') and not line.startswith('#'):
                    self._read_states(line, states)

    def _init_sorts_permutations(self) -> None:
        all_sorts_permutations = []
        for elements in self.sort_elements:
            element_id_list = list(range(len(elements)))
            sort_permutations = permutations(element_id_list)
            all_sorts_permutations.append(sort_permutations)
        # cartesian product
        self._sorts_permutations = list(product(*all_sorts_permutations))
    
    def _permute_element(self, permutation, sort_id, element) -> str:
        new_element = []
        for e in element:
            old_element_id = self.element_Name2Id[e]
            new_element_id = permutation[sort_id][old_element_id]
            new_element.append(self.sort_elements[sort_id][new_element_id])
        new_element.sort()
        return quorum_delim.join(new_element)

    def _permute_atom(self, permutation, atom_id) -> str:
        signature = self.atom_sig[atom_id]
        predicate = signature[0]
        args      = signature[1:]
        argsorts  = self.predicates[predicate]
        new_args  = []
        # get new arguements
        for (arg_id, arg) in enumerate(args):
            narg = ''
            if arg in self.quorums:
                (prefix, elements) = split_head_tail0(arg, quorum_delim) 
                sort_id = self.quorum[arg]
                narg = (prefix + quorum_delim)
                narg += self._permute_element(permutation, sort_id, elements)
            else:
                sort    = argsorts[arg_id]
                sort_id = self.sort_Name2Id[sort]
                narg = self._permute_element(permutation, sort_id, [arg])
            new_args.append(narg)       
        return format_atom(predicate, new_args)

    def _permute_values(self, permutation, values : List[str]) -> List[str]:
        nvalues = ['-']*len(values)
        for (id, val) in enumerate(values):
            if val == '0' or '1':
                atom = self._permute_atom(permutation, id)
                if atom in self.atom_Name2Id:
                    nid = self.atom_Name2Id[atom]
                    nvalues[nid] = val 
                else:
                    return [] # invalid permutation
        return nvalues

    def permute(self, values : List[str]) -> List[List[str]]:
        # values is a list of '0', '1', '-'
        assert( len(values) == self.atom_num )
        values_list = [] 
        values_hash  = set() # avoid repeated insertion
        for perm in self._sorts_permutations:
            nvalues = self._permute_values(perm, values)
            if is_valid_and_new(toCheck=nvalues, pool=values_hash):
                values_list.append(nvalues)
        return values_list 
    

 