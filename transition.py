from typing import Type
from frontend.vmt_parser import TransitionSystem, vmt_parse
import frontend.common as common

def get_transition_system(vmt_filename : str, size_str : str) -> TransitionSystem:
    # frontend setup
    common.initialize() 
    common.gopts.size = size_str

    # parse vmt
    tran_sys : Type[TransitionSystem]
    tran_sys = vmt_parse(vmt_filename)
    tran_sys.gen = 'fe'

    return tran_sys