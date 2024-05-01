from typing import Type, List, Dict
from frontend.vmt_parser import TransitionSystem, vmt_parse
from frontend.fr import *
from frontend.problem import *
from frontend.utils import *
from protocol import Protocol, quorum_delim, format_atom
from util import QrmOptions

import frontend.common as common
import re
import repycudd

class ProtocolInitializer():
    def __init__(self) -> None:
        ## helper
        self.qstr_map  = {}
        self.atomList  = []
        self.abvars    = set()

        ## protocol
        self.protocol  = Protocol()
        self.lines     = []

    def init_sort(self, tran_sys) -> None:
        for (sort, elements) in tran_sys._enumsorts.items():
            sort_line = '.s ' + str(tran_sys._enum2inf[sort])
            for e in elements:
                sort_line += ' ' + pretty_print_str(e)
            self.protocol.read_sort(sort_line) 
            self.lines.append(sort_line)

    def init_quorum_sort(self, tran_sys) -> None:
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
            self.protocol.read_quorum_sort(qsort_line)
            self.lines.append(qsort_line)

    def init_predicate(self, tran_sys) -> None:
        for pred in tran_sys.orig._nexstates:
            pred_line = '.p ' + str(pred)
            param_list =  [str(s) for s in pred.symbol_type()._param_types]
            if len(param_list) > 0:
                pred_line += ' ' + ' '.join(param_list)
            self.protocol.read_predicate(pred_line)
            self.lines.append(pred_line)

    def init_atoms(self, restricted, fr_solver) -> None:
        atom_line = '.a'
        atoms = []
        self.abvars = set(fr_solver.converter.var2atom.keys())
        for idx in range(fr_solver.numvars):
            var =  fr_solver.converter.idx2var[idx]
            atom = fr_solver.converter.var2atom[var]
            self.atomList.append(atom)
            if atom in restricted:
                atoms.append(atom)
                self.abvars.remove(var)
        for atom in atoms:
            atom_str = pretty_print_str(atom).replace(' ', '')
            predicate = '' 
            args     = []
            new_args = []
            match = re.search(r'(\w+)\(([^)]+)\)', atom_str)
            if match:
                predicate = match.group(1)
                args      = match.group(2).split(',')
            else:
                predicate = atom.strip('( )')

            for arg in args:
                if arg in self.qstr_map:
                    new_args.append(self.qstr_map[arg])
                else:
                    new_args.append(arg)
            atom_str = format_atom(predicate,new_args)
            atom_line +=  ' ' + atom_str
        self.protocol.read_atoms(atom_line)
        self.lines.append(atom_line)

    def init_reachable_states(self, reachability, restricted, fr_solver) -> None:
        abcube = fr_solver.converter.cube_from_var_list(list(self.abvars))
        bddnew = fr_solver.ddmanager.ExistAbstract(reachability, abcube)
        print("\t(printing reachability)")
        for cube_tup in repycudd.ForeachCubeIterator(fr_solver.ddmanager, bddnew):
            str_cube = '' 
            for idx, char in enumerate(cube_tup):
                if idx >= fr_solver.numvars:
                    break
                atom = self.atomList[idx]
                if atom in restricted:
                    if char == 2:
                        str_cube += '-'
                    else:
                        str_cube += str(char)
            self.protocol.read_states(str_cube)
            self.lines.append(str_cube)

    def init_permutations(self) -> None:
        self.protocol.init_sorts_permutations()

    def write_reachability(self, filename) -> None:
        outF =open(filename, "w")
        for line in self.lines:
            outF.write(line+'\n')
        outF.write('.e\n')
        outF.close()
    
def forward_reach(size_str : str, options : QrmOptions) -> Protocol:
    # frontend setup
    common.initialize() 
    common.gopts.size = size_str

    # parse vmt
    tran_sys : Type[TransitionSystem]
    tran_sys = vmt_parse(options.vmt_filename)
    tran_sys.gen = 'fe'

    # forward reachability
    fr_solver = FR(tran_sys)
    set_problem(fr_solver)
    (reachability, restricted) = fr_solver.solve_reachability()
    
    # initialize protocol
    pinit = ProtocolInitializer()
    pinit.init_sort(tran_sys)
    pinit.init_quorum_sort(tran_sys)
    pinit.init_predicate(tran_sys)
    pinit.init_atoms(restricted, fr_solver)
    pinit.init_reachable_states(reachability, restricted, fr_solver)
    pinit.init_permutations()

    # write protocols
    if (options.writeR):
        pinit.write_reachability(options.R_filename)
        eprint("\t(printed R in file %s)" % options.R_filename)
        print("\t(printed R in file %s)" % options.R_filename)

    return pinit.protocol


