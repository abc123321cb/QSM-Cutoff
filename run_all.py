import sys
import os
from os import path
import subprocess
import getopt
from typing import List
from util import *
from run_ivy import run_ivy_check
from verbose import *
from typing import Dict

def usage ():
    print('Usage:   python3 run_all.py FILE.ivy -s SORT_SIZE [options]')
    print('         read ivy file and start with the given sort size, incremeting size until deriving inductive invariant') 
    print('         (SORT_SIZE format: -s [sort1=size1,sort2=size2 ...])')
    print('')
    print('Options:')
    print('-r           read reachability from .reach file instead of doing forward reachability (default: off)')
    print('-t           early termination for reachability check (default: off)')
    print('-a           disable find all minimal solutions (default: on)')
    print('-m           disable suborbits (default: on)')
    print('-k           enalbe sanity checks for quantifier inference and minimization (default: off)')
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
        opts, args = getopt.getopt(args, "s:artmkp:c:v:l:wh")
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
    vprint_instance_banner(options, f'[Synthesize Rmin]: {options.instance_name}: {options.size_str}', 0)
    qrm_args    = ['python3', 'qrm.py', options.ivy_filename, '-s', options.size_str, '-f', '1', '-g', '-w', '-r'] + sys_args
    rmin_result = True 
    try:
        vprint(options, ' '.join(qrm_args))
        options.close_log_if_exists()
        subprocess.run(qrm_args, stderr=subprocess.PIPE, text=True, check=True, timeout=options.qrm_to) 
        options.append_log_if_exists()
    except subprocess.CalledProcessError as error:
        options.append_log_if_exists()
        if 'QrmFail' == error.stderr:
            rmin_result = False
        else:
            vprint(options, error.stderr)
            vprint(options, f'[QRM NOTE]: Exit with return code {error.returncode}')
            vprint(options, '[QRM RESULT]: FAIL')
            options.print_time()
            sys.exit(1)
    except subprocess.TimeoutExpired:
        options.append_log_if_exists()
        vprint(options, f'[QRM NOTE]: Timeout after {options.qrm_to}')
        vprint(options, '[QRM RESULT]: FAIL')
        options.print_time()
        sys.exit(1)
    return rmin_result 

def get_original_sizes(options) -> Dict[str, int]:
    orig_sizes = options.sizes.copy()
    if 'quorum' in orig_sizes:
        del orig_sizes['quorum'] 
    return orig_sizes

def get_try_increase_sort_size_string(options : QrmOptions, sort, orig_sizes, increase_size) -> str:
    try_sizes = [f'{s}={sz+increase_size}' if s==sort else f'{s}={sz}' for s,sz in orig_sizes.items()]
    try_size_str = ','.join(try_sizes)
    return try_size_str

def get_next_size_string(next_sizes) -> str:
    next_size_str = ','.join([f'{s}={sz}' for s,sz in next_sizes.items()])
    return next_size_str

def reachability_convergence_check(sol_id, options : QrmOptions, sys_args, increase_size) -> bool:
    vprint_instance_banner(options, f'[Reachability Convergence Check]: {options.instance_name}: {options.size_str}', 0)
    orig_ivy_name = options.instance_name + '.' + options.instance_suffix + f'.{sol_id}.ivy'
    orig_sizes    = get_original_sizes(options) 
    next_sizes    = orig_sizes.copy()
    has_converge  = True 
    for sort, size in orig_sizes.items():
        try_size_str = get_try_increase_sort_size_string(options, sort, orig_sizes, increase_size)
        qrm_args     = ['python3', 'qrm.py', orig_ivy_name, '-s', try_size_str, '-f', '2', '-g', '-w', '-r'] + sys_args
        try_result   = True 
        try:
            vprint(options, ' '.join(qrm_args))
            options.close_log_if_exists()
            subprocess.run(qrm_args, stderr=subprocess.PIPE, text=True, check=True, timeout=options.qrm_to) 
            options.append_log_if_exists()
        except subprocess.CalledProcessError as error:
            options.append_log_if_exists()
            if error.stderr == 'QrmFail':
                try_result = False
            else:
                vprint(options, error.stderr)
                vprint(options, f'[QRM NOTE]: Exit with return code {error.returncode}')
                vprint(options, '[QRM RESULT]: FAIL')
                options.print_time()
                sys.exit(1)
        except subprocess.TimeoutExpired:
            options.append_log_if_exists()
            vprint(options, f'[QRM NOTE]: Timeout after {options.qrm_to}')
            vprint(options, '[QRM RESULT]: FAIL')
            options.print_time()
            sys.exit(1)
        if not try_result:
            next_sizes[sort] = size + increase_size
            has_converge = False
    if has_converge:
        cutoff_size_str = options.size_str
        return has_converge, cutoff_size_str 
    else:
        next_size_str = get_next_size_string(next_sizes)
        vprint(options, f'next size: {next_size_str}')
        return has_converge, next_size_str

def finite_ivy_check(options : QrmOptions, sys_args, increase_size) -> bool:
    vprint_instance_banner(options, f'[Finite Inductive Check]: {options.instance_name}: {options.size_str}', 0)
    orig_ivy_name = options.instance_name + '.' + options.instance_suffix + '.0.ivy'
    orig_sizes    = get_original_sizes(options) 
    next_sizes    = orig_sizes.copy()
    has_converge  = True 
    for sort, size in orig_sizes.items():
        try_size_str = get_try_increase_sort_size_string(options, sort, orig_sizes, increase_size)
        qrm_args     = ['python3', 'qrm.py', orig_ivy_name, '-s', try_size_str, '-f', '3', '-g'] + sys_args
        try_result   = True 
        try:
            vprint(options, ' '.join(qrm_args))
            options.close_log_if_exists()
            subprocess.run(qrm_args, stderr=subprocess.PIPE, text=True, check=True, timeout=options.qrm_to) 
            options.append_log_if_exists()
        except subprocess.CalledProcessError as error:
            options.append_log_if_exists()
            if error.stderr == 'QrmFail':
                try_result = False
            else:
                vprint(options, error.stderr)
                vprint(options, f'[QRM NOTE]: Exit with return code {error.returncode}')
                vprint(options, '[QRM RESULT]: FAIL')
                options.print_time()
                sys.exit(1)
        except subprocess.TimeoutExpired:
            options.append_log_if_exists()
            vprint(options, f'[QRM NOTE]: Timeout after {options.qrm_to}')
            vprint(options, '[QRM RESULT]: FAIL')
            options.print_time()
            sys.exit(1)
        if not try_result:
            next_sizes[sort] = size + increase_size
            has_converge = False
    if has_converge:
        cutoff_size_str = options.size_str
        return has_converge, cutoff_size_str 
    else:
        next_size_str = get_next_size_string(next_sizes)
        vprint(options, f'next size: {next_size_str}')
        return has_converge, next_size_str

def get_number_of_Rmin_solutions(options : QrmOptions) -> int:
    num = 0
    ivy_name = options.instance_name + '.' + options.instance_suffix + f'.{num}.ivy'
    while path.isfile(ivy_name):
        num += 1
        ivy_name = options.instance_name + '.' + options.instance_suffix + f'.{num}.ivy'
    return num

def get_min_next_size_str(sizes_str : List[str]) -> str:
    next_sizes = {}
    for size_str in sizes_str:
        sort_sizes_str = size_str.split(',')
        for sort_size_str in sort_sizes_str:
            pair = sort_size_str.split('=') 
            sort = pair[0]
            size = int(pair[1])
            if not sort in next_sizes:
                next_sizes[sort] = size
            else:
                next_sizes[sort] = min(size, next_sizes[sort])
    return get_next_size_string(next_sizes)

def run_all(ivy_name, args):
    sys_args = args.copy()
    options  = get_options(ivy_name, args, sys_args)

    vprint_instance_banner(options, f'[QRM]: {ivy_name}')
    options.print_time()
    qrm_result      = False
    cutoff_size_str = ''
    Rmin_solutions  = []
    while not qrm_result:
        rmin_result  = synthesize_Rmin_and_ivy_check(options, sys_args)
        num_solution = get_number_of_Rmin_solutions(options)
        sizes_str = []
        increase_size = 0   
        while True:
            increase_size += 1
            pass_sol_ids = []
            fail_sol_ids = []
            for sol_id in range(num_solution):
                reach_result, size_str = reachability_convergence_check(sol_id, options, sys_args, increase_size)
                if reach_result:
                    pass_sol_ids.append(sol_id)
                else:
                    fail_sol_ids.append(sol_id)
                    sizes_str.append(size_str)
            if len(pass_sol_ids) == 1:
                ivy_result = run_ivy_check(pass_sol_ids[0], options)
                if ivy_result:
                    qrm_result = True
                    cutoff_size_str = size_str
                    Rmin_solutions.append(options.instance_name + '.' + options.instance_suffix + f'.{sol_id}'+ '.ivy')
                    break
                else:
                    vprint(options, '[QRM NOTE]: Reachability converge but Rmin not inductive')
                    vprint(options, '[QRM RESULT]: FAIL')
                    options.print_time()
                    sys.exit(1)
            elif len(fail_sol_ids) > 0:
                break

        # reachability not converged yet
        if not qrm_result:
            next_size_str = get_min_next_size_str(sizes_str)
            assert(options.size_str != next_size_str) 
            options = options.get_new_size_copy(next_size_str)

    vprint_instance_banner(options, f'[QRM]: {ivy_name}')
    if qrm_result:
        vprint(options, f'[RMIN NUM]: {len(Rmin_solutions)}')
        vprint(options, f'[RMIN RESULT]: {Rmin_solutions}')
        vprint(options, f'[CUTOFF]: {cutoff_size_str}')
        vprint(options, '[QRM RESULT]: PASS')
    else:
        vprint(options, '[QRM RESULT]: FAIL')
    options.print_time()

if __name__ == '__main__':
    run_all(sys.argv[1], sys.argv[2:])