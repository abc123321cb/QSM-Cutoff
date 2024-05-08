import os
from typing import List
from ivy import ivy_check
from util import QrmOptions
from verbose import *


def run_ivy_check(invariants : List[str], options : QrmOptions):
    ivy_name = options.instance_name + '.' + options.instance_suffix + '.ivy'
    cmd = f'cp {options.ivy_filename} {ivy_name}'
    os.system(cmd)
    ivy_file = open(ivy_name, 'a')
    ivy_file.write('\n')
    for line in invariants:
        ivy_file.write(line+'\n')
    ivy_file.close()
    ivy_args = ['ivy_check','complete=fo', ivy_name]
    result = ''
    vprint_banner(options, 'Ivy Check')
    result = ivy_check.ivy_check(ivy_args)
    return result
