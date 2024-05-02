from typing import List
from frontend.vmt_parser import TransitionSystem
from frontend.fr import *
from frontend.problem import *
from frontend.utils import *

class Reachability():
    def __init__(self, vars : List[str], states : List[str]) -> None:
        self.state_vars = vars
        self.states     = states

def forward_reach(tran_sys : TransitionSystem) -> FR:
    # forward reachability
    fr_solver = FR(tran_sys)
    set_problem(fr_solver)
    (stvars, states) = fr_solver.solve_reachability()
    return Reachability(stvars, states)