from typing import List
from frontend.vmt_parser import TransitionSystem
from frontend.fr import *
from frontend.problem import *
from frontend.utils import *
import repycudd

class Reachability():
    def __init__(self, atoms, states) -> None:
        self.atoms  = atoms     # type : List[formula] 
        self.states = states    # type : List[str] 
                                # each state in states is string consisting of '0', '1', '-' 
        self.stvars = []        # type: List[str]
        for atom in self.atoms:
            self.stvars.append(pretty_print_str(atom).replace(' ',''))

def get_forward_reachability(tran_sys : TransitionSystem) -> FR:
    # forward reachability
    fr_solver = FR(tran_sys)
    set_problem(fr_solver)
    (atoms, states) = fr_solver.solve_reachability()
    reach = Reachability(atoms, states)
    fr_solver.reset() 
    return reach