import ic3po.vmt_parser
import ic3po.common

def forward_reach(input : str, output : str):
    ic3po.common.initialize() # ic3po setup
    ic3po.vmt_parser.parse(input)