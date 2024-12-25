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

def run_finite_ivy_check(options: QrmOptions):
    orig_ivy_name = options.instance_name + '.' + options.instance_suffix + '.0.ivy'
    orig_sizes = options.sizes.copy()
    if 'quorum' in orig_sizes:
        del orig_sizes['quorum'] 
    next_sizes = orig_sizes.copy()
    has_increase = False
    for sort, size in orig_sizes.items():
        try_sizes = [f'{s}_{sz+1}' if s==sort else f'{s}_{sz}' for s,sz in orig_sizes.items()]
        try_size_str = '_'.join(try_sizes)
        try_ivy_name = options.instance_name + '.' + options.instance_suffix + '.0.' + try_size_str + '.ivy'
        cp_cmd = f'cp {orig_ivy_name} {try_ivy_name}'
        os.system(cp_cmd) 
        try_size_constants = ['type quorum'] if 'quorum' in options.sizes else []
        for s, sz in orig_sizes.items():
            sz = sz + 1 if s == sort else sz
            constants = [f'{s}{i}' for i in range(sz)]
            try_size_constants.append(f'type {s} = ' +  '{' + ', '.join(constants) + '}')
        comment_type_cmd = f"sed -i '/type/s/^/#/' {try_ivy_name}"
        os.system(comment_type_cmd) # comment out the original type 
        for line in try_size_constants:
            insert_type_cmd = f"sed -i '0,/type/{{/type/i\\\n{line}\n}}' {try_ivy_name}"
            os.system(insert_type_cmd) 
        ivy_args = ['ivy_check', 'complete=fo', try_ivy_name]
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
                vprint(options, f'[FINITE_CHECK RESULT]: FAIL ... exit with return code {error.returncode}')
            else:
                vprint(options, f'[FINITE_CHECK RESULT]: ABORT ... exit with return code {error.returncode}')
            next_sizes[sort] = size +1
            has_increase = True
            continue
        except subprocess.TimeoutExpired:
            vprint(options, f'[FINITE_CHECK TO]: Timeout after {options.ivy_to}')
            next_sizes[sort] = size +1
            has_increase = True
            continue
        vprint(options, f'[FINITE_CHECK RESULT]: PASS')
    if not has_increase:
        for sort,size in next_sizes.keys():
            next_sizes[sort] = next_sizes[sort] + 1
    next_size_str = ','.join([f'{s}={sz}' for s,sz in next_sizes.items()])
    vprint(options, f'next size: {next_size_str}')
    next_size_file = open('next_size', 'w')
    next_size_file.write(next_size_str+'\n')
    next_size_file.close()

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
    fmlas += [ilu.resort_ast(tran_sys.axiom_fmla, tran_sys.sort_fin2inf)]
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
    if not has_true:
        run_finite_ivy_check(options)
    return has_true

