from typing import Type
from frontend.vmt_parser import TransitionSystem, vmt_parse
import frontend.common as common

def get_transition_system(vmt_filename : str, sizes) -> TransitionSystem:
    # frontend setup
    common.initialize() 
    size_str_list = []
    for sort, size in sizes.items():
        size_str_list.append(f'{sort}={size}')
    size_str = ','.join(size_str_list)
    print(size_str)
    common.gopts.size = size_str

    # parse vmt
    tran_sys : Type[TransitionSystem]
    tran_sys = vmt_parse(vmt_filename)
    tran_sys.gen = 'fe' # forall-exist

    return tran_sys