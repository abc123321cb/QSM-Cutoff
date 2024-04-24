from typing import Type
from pysmt.shortcuts import TRUE, And, Or, Not, EqualsOrIff, Exists, ForAll, is_sat, Function
import ic3po.vmt_parser
import ic3po.common

def forward_reach(input : str, output : str):
    ic3po.common.initialize() # ic3po setup
    system : Type[ic3po.vmt_parser.TransitionSystem]
    ts = ic3po.vmt_parser.parse(input)
    print(ts._sorts    ) 
    print(ts._sort2fin ) 
    print(ts._enumsorts) 
    print(ts._enum2qvar) 
    print(ts._fin2sort ) 
    print(ts._enum2inf ) 