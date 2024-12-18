import faulthandler
import sys
import getopt
import datetime
import tracemalloc
import os

from transition_system import get_transition_system
from finite_ivy_instantiate import FiniteIvyInstantiator
from forward_reach import ForwardReachability 
from prime import PrimeOrbits
from minimize import Minimizer
from run_ivy import check_inductive_and_prove_property 
from util import * 
from verbose import *

faulthandler.enable()

def usage ():
    print('Usage:   python3 qrm.py FILE.ivy -s SORT_SIZE [options]')
    print('         read ivy file and check with the given sort size') 
    print('         (SORT_SIZE format: -s [sort1=size1,sort2=size2 ...])')
    print('')
    print('Options:')
    print('-a           disable find all minimal solutions (default: on)')
    print('-m           disable suborbits (default: on)')
    print('-k           enable checking quantifier inference (default: off)')
    print('-p 1|2|3     prime generation: 1. ilp, 2. binary search ilp 3. enumerate (default: 1)')
    print('-c sat | mc  use sat solver or exact model counter for coverage estimation (default: sat)')
    print('-v LEVEL     set verbose level (defult:0, max: 5)')
    print('-l LOG       append verbose info to LOG (default: off)')
    print('-w           write .reach, .pis, .qpis (default: off)')
    print('             write reachable states to FILE.reach')
    print('             write prime orbits to FILE.pis')
    print('             write quantified prime orbits to FILE.qpis')
    print('-h           usage')

def usage_and_exit():
    usage()
    sys.exit(1)

def file_exist(filename) -> bool:
    if not os.path.isfile(filename):
        print(f'Cannot find file: {filename}')
        usage_and_exit ()
    return True

def get_time(options, time_start=None, time_stamp=None):
    new_time_stamp  = datetime.datetime.now()
    if time_start != None and time_stamp != None:
        delta   = new_time_stamp - time_start 
        seconds = delta.seconds + 1e-6 * delta.microseconds
        vprint(options, "[QRM NOTE]: Time elapsed since start: %.3f seconds" % (seconds), 1)
        delta   = new_time_stamp - time_stamp 
        seconds = delta.seconds + 1e-6 * delta.microseconds
        vprint(options, "[QRM NOTE]: Time elapsed since last: %.3f seconds" % (seconds), 1)
    return new_time_stamp

def get_peak_memory_and_reset(options):
    (_, peak) = tracemalloc.get_traced_memory()
    vprint(options, f'[QRM NOTE]: Peak memory: {peak} bytes', 1)
    tracemalloc.reset_peak()    

def get_options(ivy_name, args):
    try:
        opts, args = getopt.getopt(args, "s:amkp:c:v:l:whd")
    except getopt.GetoptError as err:
        print(err)
        usage_and_exit()

    options = QrmOptions()
    options.mode = Mode.ivy
    if file_exist(ivy_name):
        options.ivy_filename = ivy_name
    for (optc, optv) in opts:
        if optc == '-s':
            options.set_sizes(optv)
        elif optc == '-a':
            options.all_solutions   = False 
        elif optc == '-m':
            options.merge_suborbits = False 
        elif optc == '-k':
            options.check_qi        = True 
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
            options.open_log()
        elif optc == '-w':
            options.writeReach = True
            options.writePrime = True
            options.writeQI    = True
        elif optc == '-d': # FIXME: not for user
            options.disable_print = True
        else:
            usage_and_exit()
    return options

def instance_start(options, ivy_name):
    vprint_instance_banner(options, f'[QRM]: {ivy_name}', 0, options.disable_print)
    time_start = get_time(options)
    options.set_files_name(ivy_name)
    return time_start

def step_start(options, verbose_string):
    vprint_step_banner(options, verbose_string)
    tracemalloc.start()

def step_end(options, time_start, time_stamp):
    time_stamp = get_time(options, time_start, time_stamp)
    get_peak_memory_and_reset(options)
    return time_stamp

def instance_end(options, ivy_name, qrm_result):
    vprint_instance_banner(options, f'[QRM]: {ivy_name}', 0, options.disable_print)
    if qrm_result:
        vprint(options, '[QRM RESULT]: PASS', 0, options.disable_print)
    else:
        vprint(options, '[QRM RESULT]: FAIL', 0, options.disable_print)

def qrm(ivy_name, args):
    # start
    options    = get_options(ivy_name, args)
    qrm_result = False
    time_start = instance_start(options, ivy_name)
    time_stamp = time_start

    # generate reachability
    step_start(options, f'[FW]: Forward Reachability on [{options.instance_name}: {options.size_str}]')
    step_start(options, 'Set up for forward reachability')
    tran_sys     = get_transition_system(options, options.ivy_filename)
    instantiator = FiniteIvyInstantiator(tran_sys)
    fr_solver    = ForwardReachability(tran_sys, instantiator, options)
    fr_solver.setup()
    time_stamp   = step_end(options, time_start, time_stamp)
    step_start(options, 'Symmetric Quotient DFS')
    fr_solver.symmetric_quotient_depth_first_search_reachability()
    time_stamp   = step_end(options, time_start, time_stamp)
    step_start(options, 'Reduce Equivalent Atoms')
    fr_solver.reduce_equivalent_atoms()
    time_stamp   = step_end(options, time_start, time_stamp)
    fr_solver.print_reachability()
    time_stamp   = step_end(options, time_start, time_stamp)

    # generate prime orbits
    step_start(options, f'[PRIME]: Prime Orbit Generatation on [{options.instance_name}: {options.size_str}]')
    prime_orbits = PrimeOrbits(options) 
    prime_orbits.symmetry_aware_enumerate(fr_solver.protocol)               
    time_stamp = step_end(options, time_start, time_stamp)

    # reduction
    step_start(options, f'[RED]: PRIME REDUCTION on [{options.instance_name}: {options.size_str}]')
    minimizer    = Minimizer(options, tran_sys, instantiator, prime_orbits.orbits)
    minimizer.reduce_redundant_prime_orbits()
    time_stamp   = step_end(options, time_start, time_stamp)

    # quantifier inference
    step_start(options, f'[QI]: Quantifier Inference on [{options.instance_name}: {options.size_str}]')
    minimizer.quantifier_inference(fr_solver.protocol.state_atoms_fmla)
    time_stamp = step_end(options, time_start, time_stamp)

    # minimization
    step_start(options, f'[MIN]: Minimization on [{options.instance_name}: {options.size_str}]')
    minimizer.solve_rmin()
    time_stamp = step_end(options, time_start, time_stamp)

    # minimization sanity check
    step_start(options, f'[MIN_CHECK] Minimization Sanity Check on [{options.instance_name}: {options.size_str}]')
    sanity_result = minimizer.minimization_check(fr_solver.protocol)
    time_stamp    = step_end(options, time_start, time_stamp)

    # ivy_check
    step_start(options, f'[IVY_CHECK]: Ivy Check on [{options.instance_name}: {options.size_str}]')
    ivy_result = check_inductive_and_prove_property(tran_sys, minimizer, options)
    qrm_result = sanity_result and ivy_result
    time_stamp = step_end(options, time_start, time_stamp)

    # end
    instance_end(options, ivy_name, qrm_result)
    if not qrm_result:
        sys.exit(1)

if __name__ == '__main__':
    qrm(sys.argv[1], sys.argv[2:])
