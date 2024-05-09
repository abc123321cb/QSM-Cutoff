import os
import subprocess
from typing import List
from ivy import ivy_utils as iu
from util import QrmOptions
from verbose import *

def run_ivy_check(invariants : List[str], options : QrmOptions):
    ivy_name = options.instance_name + '.' + options.instance_suffix + '.ivy'
    cp_cmd = f'cp {options.ivy_filename} {ivy_name}'
    os.system(cp_cmd)
    ivy_file = open(ivy_name, 'a')
    ivy_file.write('\n')
    for line in invariants:
        ivy_file.write(line+'\n')
    ivy_file.close()
    ivy_args = ['ivy_check', 'complete=fo', 'trace=true', ivy_name]
    ivy_cmd  = ' '.join(ivy_args)
    try:
        ivy_process = subprocess.run(ivy_args, check=True) 
    except subprocess.CalledProcessError:
        vprint(options, f'IVY RESULT: {ivy_cmd} ABORT')
        return False
    except iu.IvyError:
        vprint(options, f'IVY RESULT: {ivy_cmd} FAIL')
        return False
    vprint(options, f'IVY RESULT: {ivy_cmd} PASS')
    return True
