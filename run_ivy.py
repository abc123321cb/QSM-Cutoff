import os
import subprocess
from typing import List
from transition_system import TransitionSystem
from finite_ivy_instantiate import FiniteIvyInstantiator
from minimize import Minimizer
from mus import get_MUS
from util import QrmOptions
from transition_system import TransitionSystem
from verbose import *

def run_finite_ivy_check(options: QrmOptions, tran_sys : TransitionSystem, instantiator : FiniteIvyInstantiator):
    orig_ivy_name = options.ivy_filename
    try_ivy_name  = options.ivy_filename[:-4] + '.' + options.instance_suffix + '.ivy'
    cp_cmd = f'cp {orig_ivy_name} {try_ivy_name}'
    os.system(cp_cmd) 
    type_lines = []
    for sort, consts in tran_sys.sort2consts.items():
        constants = [str(c) for c in consts]
        type_lines.append(f'type {sort.name} = ' +  '{' + ', '.join(constants) + '}')
    comment_type_cmd = f"sed -i '/type/s/^/#/' {try_ivy_name}"
    os.system(comment_type_cmd) # comment out the original type 
    for line in type_lines:
        insert_type_cmd = f"sed -i '0,/type/{{/type/i\\\n{line}\n}}' {try_ivy_name}"
        os.system(insert_type_cmd) 
    axiom_lines = []
    for line in instantiator.dep_axioms_str:
        axiom_lines.append(f'axiom {line}')
    for line in axiom_lines:
        insert_axiom_cmd = f"sed -i '0,/after/{{/after/i\\\n{line}\n}}' {try_ivy_name}"
        os.system(insert_axiom_cmd) 
    ivy_args = ['ivy_check', 'complete=fo', try_ivy_name]
    ivy_cmd  = ' '.join(ivy_args)
    vprint(options, ivy_cmd)
    try:
        if options.writeLog:
            subprocess.run(ivy_args, text=True, check=True, stdout=options.log_fout, timeout=options.ivy_to) 
        else:
            subprocess.run(ivy_args, capture_output=True, text=True, check=True, timeout=options.ivy_to) 
    except subprocess.CalledProcessError as error:
        sys.stdout.flush()
        if error.returncode == 1:
            vprint(options, f'[FINITE_CHECK RESULT]: FAIL ... exit with return code {error.returncode}')
        else:
            vprint(options, f'[FINITE_CHECK RESULT]: ABORT ... exit with return code {error.returncode}')
        return False
    except subprocess.TimeoutExpired:
        sys.stdout.flush()
        vprint(options, f'[FINITE_CHECK TO]: Timeout after {options.ivy_to}')
        return False
    sys.stdout.flush()
    vprint(options, f'[FINITE_CHECK RESULT]: PASS')
    return True

def run_ivy_check(ivy_name, options : QrmOptions):
    vprint_step_banner(options, f'[IVY_CHECK]: Ivy check on [{ivy_name}]', 3)
    ivy_args = ['ivy_check', 'complete=fo', ivy_name]
    ivy_cmd  = ' '.join(ivy_args)
    vprint(options, ivy_cmd)
    try:
        if options.writeLog:
            subprocess.run(ivy_args, text=True, check=True, stdout=options.log_fout, timeout=options.ivy_to) 
        else:
            subprocess.run(ivy_args, capture_output=True, text=True, check=True, timeout=options.ivy_to) 
    except subprocess.CalledProcessError as error:
        sys.stdout.flush()
        if error.returncode == 1:
            vprint(options, f'[IVY_CHECK RESULT]: FAIL ... exit with return code {error.returncode}')
        else:
            vprint(options, f'[IVY_CHECK RESULT]: ABORT ... exit with return code {error.returncode}')
        return False
    except subprocess.TimeoutExpired:
        sys.stdout.flush()
        vprint(options, f'[IVY_CHECK TO]: Timeout after {options.ivy_to}')
        return False
    sys.stdout.flush()
    vprint(options, f'[IVY_CHECK RESULT]: PASS')
    return True

def compute_strengthening_assertion(ivy_name, rmin_invars, tran_sys: TransitionSystem, options : QrmOptions):
    vprint_step_banner(options, f'[MUS]: Extract strengthening assertion for on [{ivy_name}]', 3)
    get_MUS(rmin_invars, tran_sys, options)

def check_inductive_and_prove_property(tran_sys: TransitionSystem, minimizer : Minimizer, options: QrmOptions) -> bool:
    rmins    = minimizer.rmin
    has_true = False
    for rmin_id, rmin in enumerate(rmins):
        ivy_name = options.instance_name + '.' + options.instance_suffix + f'.{rmin_id}'+ '.ivy'
        result = run_ivy_check(ivy_name, options)
        if result:
            has_true = True
            compute_strengthening_assertion(ivy_name, rmin.invariants, tran_sys, options)
    return has_true