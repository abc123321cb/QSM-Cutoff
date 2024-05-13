import re
from typing import Dict,List,Set, Tuple
from itertools import permutations, product
from pysmt.fnode import FNode
from forward import Reachability
from frontend.vmt_parser import TransitionSystem
from frontend.utils import pretty_print_str
from util import QrmOptions 
from verbose import *

# utils
quorum_delim = '-'
def format_atom(predicate: str, args: List[str]) -> str:
    return predicate + '(' + ','.join(args) + ')'

def format_eq_atom(predicate: str, args: List[str]) -> str:
    return  '(' + predicate + ','.join(args) + ')'

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
    def __init__(self, options : QrmOptions, filename='') -> None:
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
        self.options = options

        # initialization 
        if filename != '':
            self.read(filename)
            self._init_sorts_permutations()

    def __str__(self) -> str:
        lines = f'sorts: {str(self.sorts)}\n'
        lines += f'sort elements: {str(self.sort_elements      )}\n' 
        lines += f'sort name to id: {str(self.sort_Name2Id       )}\n' 
        lines += f'element name to id: {str(self.element_Name2Id    )}\n' 
        lines += f'predicates: {str(self.predicates         )}\n' 
        lines += f'atom number: {str(self.atom_num           )}\n' 
        lines += f'atoms: {str(self.atoms              )}\n' 
        lines += f'atom name to id: {str(self.atom_Name2Id       )}\n' 
        lines += f'atom signature: {str(self.atom_sig           )}\n' 
        lines += f'quorum: {str(self.quorums            )}\n' 
        lines += f'reachable states: {str(self.reachable_states   )}\n' 
        lines += f'permutations: {str(self._sorts_permutations)}\n' 
        return lines

    def _read_sort(self, line : str) -> None:
        # read '.s [sort_name] [element1] [element2] ...'
        # .s node n1 n2
        sort_id     = len(self.sorts)
        (sort, elements) = split_head_tail(line, head=1)
        self.sorts.append(sort)
        self.sort_elements.append(elements)
        self.sort_Name2Id[sort] = sort_id
        for (id, e) in enumerate(elements):
            self.element_Name2Id[e]=id

    def _read_quorum_sort(self, line : str) -> None:
        # read '.q [member sort] [quorum1] [quorum2] ...' 
        # .q node q-n1-n2 q-n1-n3 q-n2-n3 ...
        (sort, quorums) = split_head_tail(line, head=1) 
        sort_id = self.sort_Name2Id[sort]
        for quorum in quorums:
            self.quorums[quorum] = sort_id

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
            match_eq   = re.search(r'\((\w+)\s*=\s*(\w+)\)', atom)
            if match_pred:
                predicate = match_pred.group(1)
                args      = match_pred.group(2).split(',')
            elif match_eq:
                predicate = match_eq.group(1) + '='
                args      = match_eq.group(2).split(',')
            else:
                predicate = atom.strip('( )')
            if match_eq:
                atom = format_eq_atom(predicate, args)
            else:
                atom = format_atom(predicate, args)
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
                if line.startswith('.q'):
                    self._read_quorum_sort(line)
                if line.startswith('.p'):
                    self._read_predicate(line)                    
                if line.startswith('.a'):
                    self._read_atoms(line)
                if not line.startswith('.') and not line.startswith('#'):
                    self._read_states(line, states)

    def _init_sort(self, tran_sys : TransitionSystem) -> None:
        for (sort, elements) in tran_sys._enumsorts.items():
            sort_line = '.s ' + str(tran_sys._enum2inf[sort])
            for e in elements:
                sort_line += ' ' + pretty_print_str(e)
            self._read_sort(sort_line) 
            if self.options.writeReach or self.options.verbosity > 3:
                self.lines.append(sort_line)

    def _init_quorum_sort(self, tran_sys : TransitionSystem) -> None:
        for (qsort, quorums) in tran_sys._quorums_consts.items():
            child_sort = (tran_sys._quorums_sorts[qsort])[1]
            quorum_elements = tran_sys._enumsorts[qsort] 
            child_elements  = tran_sys._enumsorts[child_sort]
            qsort_line = '.q ' + str(tran_sys._enum2inf[child_sort])
            for qidx, qset in quorums.items():
                elements = [str(tran_sys._enum2inf[qsort])[0]] 
                for e in qset:
                    elements.append(pretty_print_str(child_elements[e]))
                qstr_idx = pretty_print_str(quorum_elements[qidx])
                qstr_set = quorum_delim.join(elements)
                qsort_line += ' ' + qstr_set 
                self.qstr_map[qstr_idx]  = qstr_set
            self._read_quorum_sort(qsort_line)
            if self.options.writeReach or self.options.verbosity > 3:
                self.lines.append(qsort_line)

    def _init_predicate(self, tran_sys) -> None:
        for pred in tran_sys.orig._nexstates:
            pred_line = '.p ' + str(pred)
            param_list = []
            if not pred.symbol_type().is_function_type():
                if not pred.is_literal(): # case: individual [pred]: sort
                    param_list = [str(pred.symbol_type())]
                    pred_line += '='
                # else: bool type, no parameters
            else: # function
                param_list =  [str(s) for s in pred.symbol_type()._param_types]
            if len(param_list) > 0:
                pred_line += ' ' + ' '.join(param_list)
            self._read_predicate(pred_line)
            if self.options.writeReach or self.options.verbosity > 3:
                self.lines.append(pred_line)

    def _init_atoms(self, reachblty) -> None:
        atom_line = '.a'
        for atom in reachblty.stvars:
            predicate = '' 
            args     = []
            new_args = []
            match_pred = re.search(r'(\w+)\(([^)]+)\)',  atom)
            match_eq   = re.search(r'\((\w+)\s*=\s*(\w+)\)', atom)
            if match_pred:
                predicate = match_pred.group(1)
                args      = match_pred.group(2).split(',')
            elif match_eq:
                predicate = match_eq.group(1) + '='
                args      = match_eq.group(2).split(',')
            else:
                predicate = atom.strip('( )')

            for arg in args:
                if arg in self.qstr_map:
                    new_args.append(self.qstr_map[arg])
                else:
                    new_args.append(arg)
            if match_eq:
                atom = format_eq_atom(predicate, new_args)
            else:
                atom = format_atom(predicate,new_args)
            atom_line +=  ' ' + atom
        self._read_atoms(atom_line)
        if self.options.writeReach or self.options.verbosity > 3:
            self.lines.append(atom_line)

    def _init_reachable_states(self, reachblty) -> None:
        for state in reachblty.states:
            self._read_states(state)
            if self.options.writeReach or self.options.verbosity > 3:
                self.lines.append(state)

    def _write_reachability(self, filename) -> None:
        outF = open(filename, "w")
        for line in self.lines:
            outF.write(line+'\n')
        outF.write('.e\n')
        outF.close()

    def _init_sorts_permutations(self) -> None:
        all_sorts_permutations = []
        for elements in self.sort_elements:
            element_id_list = list(range(len(elements)))
            sort_permutations = permutations(element_id_list)
            all_sorts_permutations.append(sort_permutations)
        # cartesian product
        self._sorts_permutations = list(product(*all_sorts_permutations))

    def initialize(self, tran_sys : TransitionSystem, reachblty : Reachability) -> None:
        ## helper
        self.qstr_map  = {}
        self.lines     = []

        ## init
        self._init_sort(tran_sys)
        self._init_quorum_sort(tran_sys)
        self._init_predicate(tran_sys)
        self._init_atoms(reachblty)
        self._init_reachable_states(reachblty)
        self._init_sorts_permutations()

        # write protocols
        if (self.options.writeReach):
            R_filename   = self.options.instance_name + '.' + self.options.instance_suffix + '.pctl'
            self._write_reachability(R_filename)

        vprint_step_banner(self.options, '[FW RESULT]: Forward Reachability', 3)
        vprint(self.options, '\n'.join(self.lines), 3)
        vprint(self.options, f'[FW NOTE]: number of variables: {self.atom_num}', 2)
        vprint(self.options, f'[FW NOTE]: number of reachable states: {len(self.reachable_states)}', 2)
    
    def _get_renamed_element(self, permutation, sort_id, element) -> str:
        new_element = []
        for e in element:
            old_element_id = self.element_Name2Id[e]
            new_element_id = permutation[sort_id][old_element_id]
            new_element.append(self.sort_elements[sort_id][new_element_id])
        new_element.sort()
        return quorum_delim.join(new_element)

    def _get_renamed_atom(self, permutation, atom_id) -> str:
        signature = self.atom_sig[atom_id]
        predicate = signature[0]
        args      = signature[1:]
        argsorts  = self.predicates[predicate]
        new_args  = []
        # get new arguements
        for (arg_id, arg) in enumerate(args):
            narg = ''
            if arg in self.quorums:
                (prefix, elements) = split_head_tail(arg, head=0, delim=quorum_delim) 
                sort_id = self.quorums[arg]
                narg = (prefix + quorum_delim)
                narg += self._get_renamed_element(permutation, sort_id, elements)
            else:
                sort    = argsorts[arg_id]
                sort_id = self.sort_Name2Id[sort]
                narg = self._get_renamed_element(permutation, sort_id, [arg])
            new_args.append(narg)       
        if predicate.endswith('='):
            return format_eq_atom(predicate, new_args)
        else: 
            return format_atom(predicate, new_args)

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