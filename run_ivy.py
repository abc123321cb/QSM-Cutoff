import os
import subprocess
from typing import List
from transition_system import TransitionSystem
from minimize import Minimizer, Rmin
from ivy import ivy_utils as iu
from ivy import ivy_logic as il
from ivy import ivy_logic_utils as ilu
from ivy import ivy_solver as slv
from util import QrmOptions
from verbose import *

def run_ivy_check(rmin_id : int, invariants : List[str], options : QrmOptions):
    ivy_name = options.instance_name + '.' + options.instance_suffix + f'.{rmin_id}'+ '.ivy'
    cp_cmd = f'cp {options.ivy_filename} {ivy_name}'
    os.system(cp_cmd)
    comment_invar_cmd = f"sed -i '/invariant/s/^/#/' {ivy_name}"
    os.system(comment_invar_cmd) # comment out the existing invariants, including safety property
    ivy_file = open(ivy_name, 'a')
    ivy_file.write('\n')
    for line in invariants:
        ivy_file.write(line+'\n')
    ivy_file.close()
    ivy_args = ['ivy_check', 'complete=fo', ivy_name]
    ivy_cmd  = ' '.join(ivy_args)
    vprint(options, ivy_cmd)
    try:
        if options.write_log:
            subprocess.run(ivy_args, text=True, check=True, stdout=options.log_fout, timeout=options.ivy_to) 
        else:
            subprocess.run(ivy_args, capture_output=True, text=True, check=True, timeout=options.ivy_to) 
        sys.stdout.flush()
    except subprocess.CalledProcessError as error:
        if error.returncode == 1:
            vprint(options, f'[IVY_CHECK RESULT]: FAIL ... exit with return code {error.returncode}')
        else:
            vprint(options, f'[IVY_CHECK RESULT]: ABORT ... exit with return code {error.returncode}')
        return False
    except subprocess.TimeoutExpired:
        vprint(options, f'[IVY_CHECK TO]: Timeout after {options.ivy_to}')
        return False
    vprint(options, f'[IVY_CHECK RESULT]: PASS')
    return True

def unsat_core(tran_sys: TransitionSystem, rmin_invars, options : QrmOptions):
    defns =  [ilu.resort_ast(defn,  tran_sys.sort_fin2inf) for defn  in Rmin.definitions.values()]
    fmlas =  [ilu.resort_ast(equiv, tran_sys.sort_fin2inf) for equiv in Rmin.eq_relations]
    fmlas += [ilu.resort_ast(invar, tran_sys.sort_fin2inf) for invar in rmin_invars]
    clauses1      = ilu.Clauses(fmlas, defns)
    empty_clauses = ilu.Clauses([])
    clauses2      = ilu.Clauses(tran_sys.safety_properties)
    unsat_core    = slv.unsat_core(clauses1, empty_clauses, implies=clauses2, unlikely=lambda x:True)
    core_invar    = unsat_core.to_formula()
    vprint(options, f'[UNSAT CORE]: {str(core_invar)}')

def check_inductive_and_prove_property(tran_sys: TransitionSystem, minimizer : Minimizer, options: QrmOptions) -> bool:
    rmins    = minimizer.rmin
    has_true = False
    for i, rmin in enumerate(rmins):
        invariants = Rmin.def_lines + Rmin.eq_lines + rmin.invar_lines
        result = run_ivy_check(i, invariants, options)
        if result:
            has_true = True
            unsat_core(tran_sys, rmin.invariants, options)
    return has_true

