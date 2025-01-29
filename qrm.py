import faulthandler
import sys
import getopt
import datetime
import tracemalloc
import os
from transition_system import get_transition_system
from finite_ivy_instantiate import FiniteIvyInstantiator
from protocol import Protocol
from forward_reach import ForwardReachability, SymDFS, BddSymbolic
from prime import PrimeOrbits
from minimize import Minimizer
from run_ivy import check_inductive_and_prove_property, run_finite_ivy_check
from reach_check import ReachCheck 
from util import * 
from verbose import *

faulthandler.enable()

def usage ():
    print('Usage:   python3 qrm.py FILE.ivy -s SORT_SIZE [options]')
    print('         read ivy file and check with the given sort size') 
    print('         (SORT_SIZE format: -s [sort1=size1,sort2=size2 ...])')
    print('')
    print('Flow modes:')
    print('-f 0|1|2|3   flow: 0. Synthesize Rmin and ivy_check (default)')
    print('                   1. Synthesize Rmin')               
    print('                   2. Read Rmin from invariants and do reachability check')               
    print('                   3. Read Rmin from invariants and do finite ivy check')               
    print('')
    print('Options:')
    print('-r           read reachability from .reach file instead of doing forward reachability (default: off)')
    print('-b           use bdd-based symbolic image computation to compute reachable states (default: off)')
    print('-t           early termination for reachability check (default: off)')
    print('-a           disable find all minimal solutions (default: on)')
    print('-m           disable suborbits (default: on)')
    print('-k           enalbe sanity checks for quantifier inference and minimization (default: off)')
    print('-p 1|2|3     prime generation: 1. ilp 2. binary search ilp 3. enumerate (default: 1)')
    print('-c sat | mc  use sat solver or exact model counter for coverage estimation (default: sat)')
    print('-v LEVEL     set verbose level (defult:0, max: 5)')
    print('-l LOG       write verbose info to LOG (default: off)')
    print('-w           write .reach, .pis, .qpis (default: off)')
    print('             write reachable states to FILE.reach')
    print('             write prime orbits to FILE.pis')
    print('             write quantified prime orbits to FILE.qpis')
    print('-h           usage')

def usage_and_exit():
    usage()
    sys.exit(2)

def file_exist(filename) -> bool:
    if not os.path.isfile(filename):
        print(f'Cannot find file: {filename}')
        usage_and_exit ()
    return True

def get_options(ivy_name, args):
    try:
        opts, args = getopt.getopt(args, "s:bf:rtamkp:c:v:l:whg")
    except getopt.GetoptError as err:
        print(err)
        usage_and_exit()

    options = QrmOptions()
    if file_exist(ivy_name):
        options.set_files_name(ivy_name)
    for (optc, optv) in opts:
        if optc == '-s':
            options.set_sizes(optv)
        elif optc == '-f':
            if optv == '0':
                options.flow_mode = FlowMode.Rmin_Ivy # Synthesize_Rmin + ivy_check 
            elif optv == '1':
                options.flow_mode = FlowMode.Synthesize_Rmin 
            elif optv == '2':
                options.flow_mode = FlowMode.Check_Reachability 
            elif optv == '3':
                options.flow_mode = FlowMode.Check_Finite_Inductive 
            else:
                usage_and_exit()
        elif optc == '-r':
            options.readReach = True
        elif optc == '-b':
            options.forward_mode = ForwardMode.BDD_Symbolic
        elif optc == '-t':
            options.early_terminate_reach = True
        elif optc == '-a':
            options.all_solutions   = False 
        elif optc == '-m':
            options.merge_suborbits = False 
        elif optc == '-k':
            options.sanity_check    = True 
        elif optc == '-p':
            if optv == '1':
                options.prime_gen = PrimeGen.ilp
            elif optv == '2':
                options.prime_gen = PrimeGen.binary
            elif optv == '3':
                options.prime_gen = PrimeGen.enumerate
            else:
                usage_and_exit()
        elif optc == '-c':
            if optv == 'sat' or optv == 'mc':
                options.useMC = optv
            else:
                usage_and_exit()
        elif optc == '-v':
            options.verbosity = int(optv)
            if options.verbosity < 0 or options.verbosity > 5:
                usage_and_exit()
        elif optc == '-l':
            options.writeLog   = True
            options.log_name   = optv 
        elif optc == '-w':
            options.writeReach = True
            options.writePrime = True
            options.writeQI    = True
        elif optc == '-g': # NOTE: not for user, used when doing convergence
            options.convergence_check = True
        else:
            usage_and_exit()
    if options.writeLog:
        if options.convergence_check:
            options.append_log()
        else:
            options.open_log()
    return options

def instance_start(options : QrmOptions, ivy_name):
    if not options.convergence_check:
        vprint_instance_banner(options, f'[QRM]: {ivy_name}', 0)
    options.print_time()


def instance_end(options: QrmOptions, ivy_name, qrm_result):
    if not options.convergence_check:
        vprint_instance_banner(options, f'[QRM]: {ivy_name}', 0, options.convergence_check)
        if qrm_result:
            vprint(options, '[QRM RESULT]: PASS', 0, options.convergence_check)
        else:
            vprint(options, '[QRM RESULT]: FAIL', 0, options.convergence_check)

def can_skip_forward_reachability(options) -> bool:
    reach_filename = options.instance_name + '.' + options.instance_suffix + '.reach'
    return os.path.isfile(reach_filename)

def qrm(ivy_name, args):
    # start
    options    = get_options(ivy_name, args)
    qrm_result = True
    instance_start(options, ivy_name)
    tran_sys     = get_transition_system(options, options.ivy_filename)
    instantiator = FiniteIvyInstantiator(tran_sys)
    if options.flow_mode == FlowMode.Check_Finite_Inductive: 
        options.step_start(f'[FINITE_CHECK]: Finite Ivy Check for Rmin on [{options.instance_name}: {options.size_str}]')
        finite_result = check_inductive_and_prove_property(tran_sys, options)
        options.step_end()
        if options.convergence_check:
            try:
                if finite_result:
                    sys.exit(0)
                else:
                    raise QrmFail()
            except QrmFail:
                sys.stderr.write('QrmFail')
                sys.exit(1) 
        else:
            sys.exit(0)

    # get reachability
    protocol     = None
    if options.readReach and can_skip_forward_reachability(options): # read reachability
        protocol = Protocol(options)
        protocol.init_protocol_from_file(tran_sys, instantiator)
    else: # forward reachability
        options.step_start(f'[FW]: Forward Reachability on [{options.instance_name}: {options.size_str}]')
        options.step_start('Set up for forward reachability')
        fr_solver = SymDFS(tran_sys, instantiator, options) if options.forward_mode == ForwardMode.Sym_DFS else BddSymbolic(tran_sys, instantiator, options)
        options.step_end()
        options.step_start('Forward reachability')
        fr_solver.forward_reachability()
        options.step_end()
        protocol = fr_solver.protocol

    if options.flow_mode == FlowMode.Check_Reachability:
        # check reachability converges
        options.step_start(f'[REACH_CHECK]: Reachability Convergence Check for Rmin on [{options.instance_name}: {options.size_str}]')
        reach_checker = ReachCheck(options, tran_sys, instantiator, protocol)
        reach_result  = reach_checker.is_rmin_matching_reachability()
        options.step_end()
        if options.convergence_check:
            try:
                if reach_result:
                    sys.exit(0)
                else:
                    raise QrmFail()
            except QrmFail:
                sys.stderr.write('QrmFail')
                sys.exit(1) 
        else:
            sys.exit(0)
    else:
        options.step_start('Reduce Equivalent Atoms')
        protocol.reduce_equivalent_atoms(tran_sys) 
        options.step_end()

    # generate prime orbits
    options.step_start(f'[PRIME]: Prime Orbit Generatation on [{options.instance_name}: {options.size_str}]')
    prime_orbits = PrimeOrbits(options) 
    prime_orbits.symmetry_aware_enumerate(protocol)               
    options.step_end()

    # reduction
    options.step_start(f'[RED]: PRIME REDUCTION on [{options.instance_name}: {options.size_str}]')
    minimizer    = Minimizer(options, tran_sys, instantiator, prime_orbits.orbits)
    minimizer.reduce_redundant_prime_orbits()
    options.step_end()

    # quantifier inference
    options.step_start(f'[QI]: Quantifier Inference on [{options.instance_name}: {options.size_str}]')
    minimizer.quantifier_inference(instantiator, protocol.state_atoms_fmla)
    options.step_end()

    # minimization
    options.step_start(f'[MIN]: Minimization on [{options.instance_name}: {options.size_str}]')
    minimizer.solve_rmin()
    options.step_end()

    # minimization sanity check
    if options.sanity_check:
        options.step_start(f'[MIN_CHECK] Minimization Sanity Check on [{options.instance_name}: {options.size_str}]')
        sanity_result = minimizer.minimization_check(protocol)
        qrm_result    = qrm_result and sanity_result
        options.step_end()

    # ivy_check
    if options.flow_mode == FlowMode.Rmin_Ivy:
        options.step_start(f'[IVY_CHECK]: Ivy Check on [{options.instance_name}: {options.size_str}]')
        ivy_result = check_inductive_and_prove_property(tran_sys, minimizer, options)
        qrm_result = qrm_result and ivy_result 
        options.step_end()

    # end
    instance_end(options, ivy_name, qrm_result)
    if options.convergence_check:
        try:
            if qrm_result:
                sys.exit(0)
            else:
                raise QrmFail() 
        except QrmFail:
            sys.stderr.write('QrmFail')
            sys.exit(1)

if __name__ == '__main__':
    qrm(sys.argv[1], sys.argv[2:])
