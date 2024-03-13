import sys
import re
from typing import Dict,Tuple,List,Optional,Set
from itertools import permutations, product

def atom_format(predicate: str, args: List[str]) -> str:
    return predicate + '(' + ', '.join(args) + ')'

class Protocol():
    def __init__(self, reach_filename: str) -> None:
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
        self.reachable_states : List[str] = [] 
        self._sorts_permutations  = []              

        # initialization 
        self._read(reach_filename)
        self._init_sorts_permutations()

    def __str__(self) -> str:
        lines = []
        lines.append(str(self.sorts              ))        
        lines.append(str(self.sort_elements      ))        
        lines.append(str(self.sort_Name2Id       ))        
        lines.append(str(self.element_Name2Id    ))        
        lines.append(str(self.predicates         ))        
        lines.append(str(self.atom_num           ))        
        lines.append(str(self.atoms              ))        
        lines.append(str(self.atom_Name2Id       ))        
        lines.append(str(self.atom_sig           ))        
        lines.append(str(self.reachable_states   ))        
        lines.append(str(self._sorts_permutations))        
        return '\n'.join(lines)
    
    def _read(self, reach_filename: str) -> None:
        with open(reach_filename, 'r') as reach_file:
            for line in reach_file:
                # read ".s [sort_name] [element1] [element2] ..."
                if line.startswith(".s"):
                    new_sort    = line.split()
                    sort_name   = new_sort[1]
                    elements    = new_sort[2:]
                    sort_id     = len(self.sorts)
                    self.sorts.append(sort_name)
                    self.sort_elements.append(elements)
                    self.sort_Name2Id[sort_name] = sort_id
                    for (id, e) in enumerate(elements):
                        self.element_Name2Id[e]=id

                # read ".p [predicate_name] [argsort1] [argsort2]"
                if line.startswith(".p"):
                    new_predicate = line.split()
                    self.predicates[new_predicate[1]] = new_predicate[2:]

                # read ".n [atom_num]"
                match = re.search(r'.n (\d+)', line)
                if match:
                    self.atom_num = int(match.group(1))

                # read ".a [atom1] [atom2] ..."
                if line.startswith(".a"):
                    atoms = line.split()
                    atoms = atoms[1:] # remove ".a"
                    assert( len(atoms) == self.atom_num )
                    for (id,atom) in enumerate(atoms):
                        match = re.search(r'(\w+)\(([^)]+)\)', atom)
                        if match:
                            predicate = match.group(1)
                            args      = match.group(2).split(',')
                            atom      = atom_format(predicate,args)
                            signature = [predicate] + args
                            self.atoms.append(atom)
                            self.atom_Name2Id[atom]  = id
                            self.atom_sig.append(signature)
                            
                # read "[reachable_state]"
                if not line.startswith(".") and not line.startswith("#"):
                    state = line.split()[0]
                    assert( len(state) == self.atom_num )
                    self.reachable_states.append(state)

    def _init_sorts_permutations(self) -> None:
        all_sorts_permutations = []
        for elements in self.sort_elements:
            element_id_list = list(range(len(elements)))
            sort_permutations = permutations(element_id_list)
            all_sorts_permutations.append(sort_permutations)
        # cartesian product
        self._sorts_permutations = list(product(*all_sorts_permutations))

    def permute(self, values : List[str]) -> List[List[str]]:
        # values is a list of '0', '1', '-'
        assert( len(values) == self.atom_num )
        permuted_val_list = [] 
        keys  = set()
        for permutation in self._sorts_permutations:
            new_values = ['-']*len(values)
            for (atom_id, val) in enumerate(values):
                if not val == '-':
                    assert( val == '0' or val == '1' )
                    atom      = self.atoms[atom_id]
                    signature = self.atom_sig[atom_id]
                    predicate = signature[0]
                    args      = signature[1:]
                    argsorts  = self.predicates[predicate]
                    new_args  = []
                    for (arg_id, arg) in enumerate(args):
                        sort    = argsorts[arg_id]
                        sort_id = self.sort_Name2Id[sort]
                        old_element_id = self.element_Name2Id[arg]
                        new_element_id = permutation[sort_id][old_element_id]
                        new_args.append(self.sort_elements[sort_id][new_element_id])
                    new_atom    = atom_format(predicate, new_args) 
                    new_atom_id = self.atom_Name2Id[new_atom]
                    new_values[new_atom_id] = val 
            new_key = str(new_values)
            if not new_key in keys:
                keys.add(new_key)
                permuted_val_list.append(new_values)
        return permuted_val_list
    