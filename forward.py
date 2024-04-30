from typing import Type
from pysmt.shortcuts import TRUE, And, Or, Not, EqualsOrIff, Exists, ForAll, is_sat, Function
from frontend.vmt_parser import TransitionSystem
from frontend.vmt_parser import vmt_parse 
import frontend.common as common
from frontend.fr import *
from frontend.problem import *

def forward_reach(input : str, output : str, size_str : str):
    common.initialize() # frontend setup
    common.gopts.size = size_str
    tran_sys : Type[TransitionSystem]
    tran_sys = vmt_parse(input)
    fr_solver = FR(tran_sys)
    set_problem(fr_solver)
    tran_sys.gen = "fe"
    inferences = fr_solver.solve_reachability(output)