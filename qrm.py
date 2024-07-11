import faulthandler
import sys
import getopt
import datetime
import tracemalloc
import os

from ivy2vmt import compile_ivy2vmt
from transition import get_transition_system 
from forward_reach import get_protocol_forward_reachability
from prime import PrimeOrbits
from minimize import Minimizer
from run_ivy import run_ivy_check
from util import * 
from verbose import *

faulthandler.enable()

def usage ():
    print('Usage:')
    print('python3 qrm.py -i FILE.ivy -s SORT_SIZE -t PYHON_INCLUDE_PATH [options]')
    print('python3 qrm.py -y FILE.yaml             -t PYHON_INCLUDE_PATH [options]')
    print('-i FILE.ivy -s SORT_SIZE  read ivy file and check with the given sort size')
    print('                          (format: -s [sort1=size1,sort2=size2 ...])')
    print('-y FILE.yaml              check all cases in the given yaml file')
    print('-t PYTHON_INCLUDE_PATH    set python include path (e.g. /usr/include/python3.XX)') #FIXME!!!!!
    print('')
    print('Options:')
    print('-v LEVEL     set verbose level (defult:0, max: 5)')
    print('-l LOG       append verbose info to LOG (default: off)')
    print('-c sat | mc  use sat solver or approximate model counter for coverage estimation (default: sat)')
    print('-r           write reachable states to FILE.ptcl (default: off)')
    print('-p           write prime orbits to FILE.pis (default: off)')
    print('-q           write quantified prime orbits to FILE.qpis (default: off)')
    print('-w           write .ptcl, .pis, .qpis, equivalent to options -r -p -q (default: off)')
    print('-a           find all minimal solutions (default: off)')
    print('-m           merge suborbits (default: off)')
    print('-h           usage')

def usage_and_exit():
    usage()
    sys.exit(1)

def file_exist(filename) -> bool:
    if not os.path.isfile(filename):
        print(f'Cannot find file: {filename}')
        usage_and_exit ()
    return True

def rm_log_file_if_exist(filename) -> bool:
    if os.path.isfile(filename):
        os.system(f'rm {filename}')

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

def get_options(args):
    try:
        opts, args = getopt.getopt(args, "i:s:y:t:v:l:c:rpqwamhd")
    except getopt.GetoptError as err:
        print(err)
        usage_and_exit()

    options = QrmOptions()
    disable_print = False
    for (optc, optv) in opts:
        if optc == '-i':
            options.mode = Mode.ivy
            if file_exist(optv):
                options.ivy_filename = optv
        elif optc == '-s':
            options.size_str = optv 
        elif optc == '-y':
            options.mode = Mode.yaml
            if file_exist(optv):
                options.yaml_filename = optv
        elif optc == '-t':
            options.python_include_path = optv
        elif optc == '-v':
            options.verbosity = int(optv)
            if options.verbosity < 0 or options.verbosity > 5:
                usage_and_exit()
        elif optc == '-l':
            options.writeLog   = True
            options.log_name   = optv 
            options.open_log()
        elif optc == '-c':
            if optv == 'sat' or optv == 'mc':
                options.useMC = optv
            else:
                usage_and_exit()
        elif optc == '-r':
            options.writeReach = True
        elif optc == '-p':
            options.writPrime  = True
        elif optc == '-q':
            options.writeQI    = True
        elif optc == '-w':
            options.writeReach = True
            options.writePrime = True
            options.writeQI    = True
        elif optc == '-a':
            options.all_solutions   = True
        elif optc == '-m':
            options.merge_suborbits = True
        elif optc == '-d': # FIXME 
            options.disable_print   = True
        else:
            usage_and_exit()
    return options

def get_instances(options: QrmOptions):
    instances = {} 
    if options.mode == Mode.ivy:
        instances[options.ivy_filename] = [options.size_str]
    else:
        instances = get_instances_from_yaml(options.yaml_filename)
    return instances

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

def qrm(args):
    options    = get_options(args)
    instances  = get_instances(options)
    pass_count = 0
    for ivy_name, sizes in instances.items():
        qrm_result = False
        time_start = instance_start(options, ivy_name)
        # step 0: compile ivy
        step_start(options, '[CPL]: Compile Ivy')
        compile_ivy2vmt(options, options.ivy_filename, options.vmt_filename)
        time_stamp = step_end(options, time_start, time_start)
        for size_str in sizes:
            # size initialization
            options.set_sizes(size_str)
            # step1: generate reachability
            step_start(options, f'[FW]: Forward Reachability on [{options.instance_name}: {size_str}]')
            tran_sys   = get_transition_system(options, options.vmt_filename)
            protocol   = get_protocol_forward_reachability(tran_sys, options) 
            time_stamp = step_end(options, time_start, time_stamp)

            # step2: generate prime orbits
            step_start(options, f'[PRIME]: Prime Orbit Generatation on [{options.instance_name}: {size_str}]')
            prime_orbits = PrimeOrbits(options) 
            prime_orbits.symmetry_aware_enumerate(protocol)               
            time_stamp = step_end(options, time_start, time_stamp)

            # step3: quantifier inference
            step_start(options, f'[QI]: Quantifier Inference on [{options.instance_name}: {size_str}]')
            prime_orbits.quantifier_inference(protocol.atoms_fmla, tran_sys)
            time_stamp = step_end(options, time_start, time_stamp)

            # step4: minimization
            step_start(options, f'[MIN]: Minimization on [{options.instance_name}: {size_str}]')
            minimizer  = Minimizer(prime_orbits.orbits, options)
            invariants = minimizer.get_minimal_invariants()
            time_stamp = step_end(options, time_start, time_stamp)

            # step5: ivy_check
            step_start(options, f'[IVY_CHECK]: Ivy Check on [{options.instance_name}: {size_str}]')
            ivy_result = run_ivy_check(invariants, options)
            qrm_result = ivy_result
            time_stamp = step_end(options, time_start, time_stamp)

        instance_end(options, ivy_name, qrm_result)
        if qrm_result:
            pass_count += 1

    if pass_count != len(instances):
        sys.exit(1)

if __name__ == '__main__':
    qrm(sys.argv[1:])
