import faulthandler
import sys
import getopt
import datetime
import time
from os import path
from ivy2vmt import compile_ivy2vmt
from vmt_parser import vmt_parse
from transition import get_transition_system
from verbose import *
from util import * 
from forward import *
from protocol import Protocol 
from prime import PrimeOrbits, PrimeOrbit
from minimize import Minimizer
from run_ivy import *
import tracemalloc

faulthandler.enable()

def usage ():
    print('Usage:')
    print('python3 qrm.py -i FILE.ivy -s SORT_SIZE [options]')
    print('python3 qrm.py -y FILE.yaml [options]')
    print('-i FILE.ivy -s SORT_SIZE  read ivy file and check with the given sort size')
    print('                          (format: -s [sort1=size1,sort2=size2 ...])')
    print('-y FILE.yaml              check all cases in the given yaml file')
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
    if not path.isfile(filename):
        print(f'Cannot find file: {filename}')
        usage_and_exit ()
    return True

def rm_log_file_if_exist(filename) -> bool:
    if path.isfile(filename):
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

def qrm(args):
    try:
        opts, args = getopt.getopt(args, "i:s:y:v:l:c:rpqwamhd")
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
        elif optc == '-d': # not for user
            disable_print      = True
        else:
            usage_and_exit()

    instances = {} 
    if options.mode == Mode.ivy:
        instances[options.ivy_filename] = [options.size_str]
    else:
        instances = get_instances_from_yaml(options.yaml_filename)

    pass_count = 0
    for ivy_name, sizes in instances.items():
        time_start = get_time(options)
        vprint_instance_banner(options, f'[QRM]: {ivy_name}', 0, disable_print)
        vprint_step_banner(options, '[CPL]: Compile Ivy')
        options.ivy_filename  = ivy_name
        options.instance_name = ivy_name.split('.')[0]
        options.vmt_filename  = options.instance_name + '.vmt'
        # step 0: compile ivy
        compile_ivy2vmt(options, options.ivy_filename, options.vmt_filename)
        qrm_result = False
        time_stamp = get_time(options, time_start, time_start)
        for size_str in sizes:
            # step1: generate reachability
            tracemalloc.start()
            vprint_step_banner(options, f'[FW]: Forward Reachability on [{options.instance_name}: {size_str}]')
            options.set_sizes(size_str)
            tran_sys  = vmt_parse(options, options.vmt_filename)
            tran_sys_orig  = get_transition_system(options.vmt_filename, options.sizes) # orig
            reachblty = get_forward_reachability(tran_sys_orig, tran_sys, options) #FIXME
            protocol  = Protocol(options)
            protocol.initialize(tran_sys, reachblty)
            time_stamp = get_time(options, time_start, time_stamp)
            get_peak_memory_and_reset(options)

            # step2: generate prime orbits
            tracemalloc.start()
            vprint_step_banner(options, f'[PRIME]: Prime Orbit Generatation on [{options.instance_name}: {size_str}]')
            prime_orbits = PrimeOrbits(options) 
            prime_orbits.symmetry_aware_enumerate(protocol)               
            time_stamp = get_time(options, time_start, time_stamp)
            get_peak_memory_and_reset(options)

            # step3: quantifier inference
            tracemalloc.start()
            vprint_step_banner(options, f'[QI]: Quantifier Inference on [{options.instance_name}: {size_str}]')
            prime_orbits.quantifier_inference(reachblty.atoms, tran_sys) # FIXME 
            time_stamp = get_time(options, time_start, time_stamp)
            get_peak_memory_and_reset(options)             

            # step4: minimization
            tracemalloc.start()
            vprint_step_banner(options, f'[MIN]: Minimization on [{options.instance_name}: {size_str}]')
            minimizer  = Minimizer(prime_orbits.orbits, options)
            invariants = minimizer.get_minimal_invariants()
            time_stamp = get_time(options, time_start, time_stamp)
            get_peak_memory_and_reset(options)

            # step5: ivy_check
            tracemalloc.start()
            vprint_step_banner(options, f'[IVY_CHECK]: Ivy Check on [{options.instance_name}: {size_str}]')
            ivy_result = run_ivy_check(invariants, options)
            qrm_result = ivy_result
            time_stamp = get_time(options, time_start, time_stamp)
            get_peak_memory_and_reset(options)

        vprint_instance_banner(options, f'[QRM]: {ivy_name}', 0, disable_print)
        if qrm_result:
            vprint(options, '[QRM RESULT]: PASS', 0, disable_print)
            pass_count += 1
        else:
            vprint(options, '[QRM RESULT]: FAIL', 0, disable_print)

    if pass_count != len(instances):
        sys.exit(1)

if __name__ == '__main__':
    qrm(sys.argv[1:])
