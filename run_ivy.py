import os
import subprocess
from typing import List
from transition_system import TransitionSystem
from minimize import Minimizer
from ivy import ivy_utils as iu
from ivy import ivy_logic as il
from ivy import ivy_logic_utils as ilu
from ivy import ivy_solver as slv
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

def get_unsat_core(tran_sys: TransitionSystem, minimizer : Minimizer):
    defns =  [ilu.resort_ast(defn,  tran_sys.sort_fin2inf) for defn  in tran_sys.definitions.values()]
    fmlas =  [ilu.resort_ast(equiv, tran_sys.sort_fin2inf) for equiv in tran_sys.closed_atom_equivalence_constraints]
    fmlas += [ilu.resort_ast(invar, tran_sys.sort_fin2inf) for invar in minimizer.rmin]
    clauses1      = ilu.Clauses(fmlas, defns)
    empty_clauses = ilu.Clauses([])
    clauses2      = ilu.Clauses(tran_sys.safety_properties)
    unsat_core    = slv.unsat_core(clauses1, empty_clauses, implies=clauses2, unlikely=lambda x:True)
    core_invar    = unsat_core.to_formula()
    return core_invar 

