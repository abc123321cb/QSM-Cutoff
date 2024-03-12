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
        self.sorts_permutations  = []              

        self.predicates    : Dict[str,List[str]] = {} # (predname, [argsort1, argsort2, ..])
        self.atom_num      : int                 = 0
        self.atoms         : List[str]           = [] # atom id -> atom name
        self.atom_Name2Id  : Dict[str,int]       = {} # atom name -> atom id
        self.atom_sig      : List[List[str]]     = [] # atom id -> [predname, arg1, arg2,..]

        self.reachable_cubes : List[str] = [] 

        # initialize 
        self.read(reach_filename)
        self.init_sorts_permutations()
        

    def read(self, reach_filename: str) -> None:
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
                            
                # read "[reachable_cube]"
                if not line.startswith(".") and not line.startswith("#"):
                    cube = line.split()[0]
                    assert( len(cube) == self.atom_num )
                    self.reachable_cubes.append(cube)

    def init_sorts_permutations(self) -> None:
        all_sorts_permutations = []
        for elements in self.sort_elements:
            element_id_list = list(range(len(elements)))
            sort_permutations = permutations(element_id_list)
            all_sorts_permutations.append(sort_permutations)
        # cartesian product
        self.sorts_permutations = list(product(*all_sorts_permutations))
    
    def orbit_of_cube(self, cube: str) -> List[str]:
        # cube is a string of 0,1,-
        assert( len(cube) == self.atom_num )
        orbit : List[str] = []
        for permutation in self.sorts_permutations:
            new_cube = ['-']*len(cube)
            for (atom_id, bit) in enumerate(cube):
                if not bit == '-':
                    assert( bit == '0' or bit == '1' )
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
                    new_cube[new_atom_id] = bit 
            orbit.append(''.join(new_cube))
        return orbit


    def print_members(self) -> None:
         print("sorts: ", self.sorts)
         print("sort elements: ", self.sort_elements)
         print("sort name to id: ", self.sort_Name2Id)
         print("element name to id: ", self.element_Name2Id)
         print("predicates: ", self.predicates)
         print("atom number: ", self.atom_num)      
         print("atoms: ", self.atoms)
         print("atom name to id: ", self.atom_Name2Id)
         print("atom signature: ", self.atom_sig)
         print("reachable cubes: ", self.reachable_cubes)
         cube = "1---------" 
         print("orbit of ", cube, " : ", self.orbit_of_cube(cube) )
         cube = "-0--------" 
         print("orbit of ", cube, " : ", self.orbit_of_cube(cube) )
         cube = "10--------" 
         print("orbit of ", cube, " : ", self.orbit_of_cube(cube) )

