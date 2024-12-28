import sys
import os
from os import path
import subprocess
import getopt
from util import *
from verbose import *
from typing import Dict

def usage ():
    print('Usage:   python3 run_all.py FILE.ivy -s SORT_SIZE [options]')
    print('         read ivy file and start with the given sort size, incremeting size until deriving inductive invariant') 
    print('         (SORT_SIZE format: -s [sort1=size1,sort2=size2 ...])')
    print('')
    print('Options:')
    print('-a           disable find all minimal solutions (default: on)')
    print('-m           disable suborbits (default: on)')
    print('-k           enalbe quantifier inference (default: off)')
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
    sys.exit(2)

def file_exist(filename) -> bool:
    if not path.isfile(filename):
        print(f'Cannot find file: {filename}')
        usage_and_exit ()
    return True

def get_options(ivy_name, args, sys_args) -> QrmOptions:
    try:
        opts, args = getopt.getopt(args, "s:amkp:c:v:l:wh")
    except getopt.GetoptError as err:
        print(err)
        usage_and_exit()

    options = QrmOptions()
    if file_exist(ivy_name):
        options.set_files_name(ivy_name)
    for (optc, optv) in opts:
        if optc == '-v':
            options.verbosity = int(optv)
            if options.verbosity < 0 or options.verbosity > 5:
                usage_and_exit()
        elif optc == '-l':
            options.writeLog   = True
            options.log_name   = optv 
            options.open_log()
        elif optc == '-s':
            options.set_sizes(optv)
            sys_args.remove(optc)
            sys_args.remove(optv)
    return options

def synthesize_Rmin_and_ivy_check(options : QrmOptions, sys_args) -> bool:
    qrm_args    = ['python3', 'qrm.py', options.ivy_filename, '-s', options.size_str, '-f', '1', '-d'] + sys_args
    rmin_result = True 
    try:
        subprocess.run(qrm_args, stderr=subprocess.PIPE, text=True, check=True, timeout=options.qrm_to) 
        sys.stdout.flush()
    except subprocess.CalledProcessError as error:
        if 'QrmFail' == error.stderr:
            rmin_result = False
        else:
            vprint(options, error.stderr)
            vprint(options, f'[QRM NOTE]: Exit with return code {error.returncode}')
            sys.exit(1)
    except subprocess.TimeoutExpired:
        vprint(options, f'[QRM NOTE]: Timeout after {options.qrm_to}')
        sys.exit(1)
    return rmin_result 

def get_original_sizes(options) -> Dict[str, int]:
    orig_sizes = options.sizes.copy()
    if 'quorum' in orig_sizes:
        del orig_sizes['quorum'] 
    return orig_sizes

def get_try_increase_sort_size_string(sort, orig_sizes) -> str:
    try_sizes = [f'{s}={sz+1}' if s==sort else f'{s}_{sz}' for s,sz in orig_sizes.items()]
    try_size_str = ','.join(try_sizes)
    return try_size_str

def get_next_size_string(next_sizes) -> str:
    next_size_str = ','.join([f'{s}={sz}' for s,sz in next_sizes.items()])
    return next_size_str

def reachability_convergence_check(options : QrmOptions, sys_args) -> bool:
    orig_ivy_name = options.instance_name + '.' + options.instance_suffix + '.0.ivy'
    orig_sizes    = get_original_sizes(options) 
    next_sizes    = orig_sizes.copy()
    has_converge  = True 
    for sort, size in orig_sizes.items():
        try_size_str = get_try_increase_sort_size_string(sort, orig_sizes)
        qrm_args     = ['python3', 'qrm.py', orig_ivy_name, '-s', try_size_str, '-f', '2', '-d'] + sys_args
        try_result   = True 
        try:
            subprocess.run(qrm_args, stderr=subprocess.PIPE, text=True, check=True, timeout=options.qrm_to) 
            sys.stdout.flush()
        except subprocess.CalledProcessError as error:
            if error.stderr == 'QrmFail':
                try_result = False
            else:
                vprint(options, error.stderr)
                vprint(options, f'[QRM NOTE]: Exit with return code {error.returncode}')
                sys.exit(1)
        except subprocess.TimeoutExpired:
            vprint(options, f'[QRM NOTE]: Timeout after {options.qrm_to}')
            sys.exit(1)
        if not try_result:
            next_sizes[sort] = size +1
            has_converge = False
    next_size_str = get_next_size_string(next_sizes)
    vprint(options, f'next size: {next_size_str}')
    return has_converge, next_size_str

def run_all(ivy_name, args):
    sys_args = args.copy()
    options  = get_options(ivy_name, args, sys_args)

    vprint_instance_banner(options, f'[QRM]: {ivy_name}')
    qrm_result = False
    while not qrm_result:
        rmin_result = synthesize_Rmin_and_ivy_check(options, sys_args)
        converge_result, next_size_str = reachability_convergence_check(options, sys_args)
        assert(not converge_result or rmin_result) # asserting converge -> rmin is inductive
        if rmin_result and converge_result:
            qrm_result = True
        else:
            assert(options.size_str != next_size_str) 
            options = options.get_new_size_copy(next_size_str)

    vprint_instance_banner(options, f'[QRM]: {ivy_name}')
    if qrm_result:
        vprint(options, '[QRM RESULT]: PASS')
    else:
        vprint(options, '[QRM RESULT]: FAIL')

if __name__ == '__main__':
    run_all(sys.argv[1], sys.argv[2:])