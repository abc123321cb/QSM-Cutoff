import os
import subprocess
from util import QrmOptions
from transition_system import TransitionSystem
from minimize import Rmin
from ivy import ivy_logic as il
from ivy import ivy_logic_utils as ilu
from ivy import ivy_solver as slv
from verbose import *

def unsat_core(tran_sys: TransitionSystem, rmin_invars, options : QrmOptions):
    defns        =  [defn for defn  in Rmin.definitions.values()]
    next_defns   =  []
    for defn in defns:
        args = [il.substitute(a, tran_sys.curr2next) for a in defn.args]
        new_defn = il.Definition(*args)
        next_defns.append(new_defn)
    defns         = [ilu.resort_ast(defn,  tran_sys.sort_fin2inf) for defn  in defns]
    next_defns    = [ilu.resort_ast(defn,  tran_sys.sort_fin2inf) for defn  in next_defns]

    R_fmlas      = [equiv for equiv in Rmin.eq_relations]
    R_fmlas     += [invar for invar in rmin_invars]
    next_R_fmlas = [il.substitute(f, tran_sys.curr2next) for f in R_fmlas]
    R_fmlas      = [ilu.resort_ast(invar, tran_sys.sort_fin2inf) for invar in R_fmlas]
    next_R_fmlas = [ilu.resort_ast(invar, tran_sys.sort_fin2inf) for invar in next_R_fmlas]

    safety_fmlas      = [p for p in tran_sys.safety_properties]
    next_safety_fmlas = [il.substitute(f, tran_sys.curr2next) for f in safety_fmlas]
    safety_fmlas      = [ilu.resort_ast(f, tran_sys.sort_fin2inf) for f in safety_fmlas]
    next_safety_fmlas = [ilu.resort_ast(f, tran_sys.sort_fin2inf) for f in next_safety_fmlas]

    axiom_fmlas       = [ilu.resort_ast(tran_sys.axiom_fmla, tran_sys.sort_fin2inf)]
    transition_fmlas  = [ilu.resort_ast(tran_sys.transition_relation, tran_sys.sort_fin2inf)] 

    soft_clauses =  ilu.Clauses(R_fmlas, defns)
    hard_fmlas   = safety_fmlas + axiom_fmlas + transition_fmlas
    hard_clauses = ilu.Clauses(hard_fmlas, defns + next_defns)
    imply_fmlas  = next_safety_fmlas + next_R_fmlas
    implies      = ilu.Clauses(imply_fmlas, next_defns) 

    slv.clear() # changing from finite signature (qpi) to uninterpreted signature
    unsat_core    = slv.unsat_core(soft_clauses, hard_clauses, implies=implies, unlikely=lambda x:True)
    if unsat_core == None:
        vprint(options, f'[(R & P) & T & ~(R\' & P\')]: satifiable')
    else:
        core_invar    = unsat_core.to_formula()
        vprint(options, f'[(R & P) & T & ~(R\' & P\')]: unsatisfiable')
        vprint(options, f'[Strengthening Assertion]: {str(core_invar)}')

def get_MUS_smt2(rmin_invars, tran_sys: TransitionSystem):
    # definitions
    defns        =  [defn for defn  in Rmin.definitions.values()]
    next_defns   =  []
    for defn in defns:
        args = [il.substitute(a, tran_sys.curr2next) for a in defn.args]
        new_defn = il.Definition(*args)
        next_defns.append(new_defn)
    defns         = [ilu.resort_ast(defn,  tran_sys.sort_fin2inf) for defn  in defns]
    next_defns    = [ilu.resort_ast(defn,  tran_sys.sort_fin2inf) for defn  in next_defns]
    # R
    R_fmlas      = [equiv for equiv in Rmin.eq_relations]
    R_fmlas     += [invar for invar in rmin_invars]
    next_R_fmlas = [il.substitute(f, tran_sys.curr2next) for f in R_fmlas]
    R_fmlas      = [ilu.resort_ast(invar, tran_sys.sort_fin2inf) for invar in R_fmlas]
    next_R_fmlas = [ilu.resort_ast(invar, tran_sys.sort_fin2inf) for invar in next_R_fmlas]
    # safety
    safety_fmlas      = [p for p in tran_sys.safety_properties]
    next_safety_fmlas = [il.substitute(f, tran_sys.curr2next) for f in safety_fmlas]
    safety_fmlas      = [ilu.resort_ast(f, tran_sys.sort_fin2inf) for f in safety_fmlas]
    next_safety_fmlas = [ilu.resort_ast(f, tran_sys.sort_fin2inf) for f in next_safety_fmlas]
    # axiom, transition
    axiom_fmlas       = [ilu.resort_ast(tran_sys.axiom_fmla, tran_sys.sort_fin2inf)]
    transition_fmlas  = [ilu.resort_ast(tran_sys.transition_relation, tran_sys.sort_fin2inf)] 
    # soft/hard fmlas
    soft_fmlas        = R_fmlas
    hard_fmlas        = safety_fmlas + axiom_fmlas + transition_fmlas + [il.Not(il.And(*next_safety_fmlas + next_R_fmlas))]
    # solver
    slv.clear() # changing from finite signature (qpi) to uninterpreted signature
    solver = slv.z3.Solver()
    hard_clauses = ilu.Clauses(hard_fmlas, defns + next_defns)
    solver.add(slv.clauses_to_z3(hard_clauses))
    for soft_fmla in soft_fmlas:
        solver.add(slv.clauses_to_z3(ilu.Clauses([soft_fmla], defns)))
    return solver.to_smt2()

def get_MUS(rmin_invars, tran_sys: TransitionSystem, options : QrmOptions):
    mus_smt2 = get_MUS_smt2(rmin_invars, tran_sys)
    # print & write
    smt_filename = options.instance_name + '.smt2'
    smt_file = open(smt_filename, "w")
    smt_file.write(mus_smt2)
    smt_file.close()
    # MARCO
    mus_filename = options.instance_name + '.mus'
    mus_file = open(mus_filename, 'w')
    marco_args = ['./MARCO/marco.py', smt_filename, '-v']
    try:
        subprocess.run(marco_args, text=True, check=True, stdout=mus_file, timeout=options.qrm_to) 
    except subprocess.CalledProcessError as error:
        sys.stdout.flush()
        if error.returncode == 1:
            vprint(options, f'[MARCO RESULT]: FAIL ... exit with return code {error.returncode}')
        else:
            vprint(options, f'[MARCO RESULT]: ABORT ... exit with return code {error.returncode}')
        return False
    except subprocess.TimeoutExpired:
        sys.stdout.flush()
        vprint(options, f'[MARCO TO]: Timeout after {options.qrm_to}')
        return False
    sys.stdout.flush()
    mus_file.close()
    # parse mus file
    min_mus = None 
    with open(mus_filename, 'r') as mus_file: 
        for line in mus_file:
            if line.startswith('U'):
                mus = line.strip().split()[1:]
                if min_mus == None:
                    min_mus = mus
                elif len(mus) < len(min_mus):
                    min_mus = mus
    min_mus = set([int(i) for i in min_mus])
    fmlas   = []
    fmla_id = 2
    for equiv in Rmin.eq_relations:
        if fmla_id in min_mus:
            fmlas.append(equiv)
        fmla_id += 1
    for invar in rmin_invars:
        if fmla_id in min_mus:
            fmlas.append(invar)
        fmla_id += 1
    vprint(options, f'[MUS NOTE]: number of strengthening assertions: {len(fmlas)}')
    return fmlas 