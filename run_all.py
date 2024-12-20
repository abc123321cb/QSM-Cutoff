import sys
import os
from os import path
import subprocess
import getopt
from util import *
from verbose import *

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
    sys.exit(1)

def file_exist(filename) -> bool:
    if not path.isfile(filename):
        print(f'Cannot find file: {filename}')
        usage_and_exit ()
    return True

def rm_and_recreate_log_file_if_exist(filename):
    if path.isfile(filename):
        os.system(f'rm {filename}')
        os.system(f'touch {filename}')

def run_all(ivy_name, args):
    sys_args = args.copy()
    try:
        opts, args = getopt.getopt(args, "s:amkp:c:v:l:wh")
    except getopt.GetoptError as err:
        print(err)
        usage_and_exit()

    options = QrmOptions()
    if file_exist(ivy_name):
        options.ivy_filename = ivy_name
    for (optc, optv) in opts:
        if optc == '-v':
            options.verbosity = int(optv)
            if options.verbosity < 0 or options.verbosity > 5:
                usage_and_exit()
        elif optc == '-l':
            options.writeLog   = True
            options.log_name   = optv 
            rm_and_recreate_log_file_if_exist(options.log_name)
            options.open_log()
        elif optc == '-s':
            options.set_sizes(optv)
            sys_args.remove(optc)
            sys_args.remove(optv)

    vprint_instance_banner(options, f'[QRM]: {ivy_name}')
    qrm_result = False
    size_str   = options.size_str
    while not qrm_result:
        qrm_args = ['python3', 'qrm.py', ivy_name, '-s', size_str, '-d'] + sys_args
        result = True 
        try:
            subprocess.run(qrm_args, check=True, timeout=options.qrm_to) 
            sys.stdout.flush()
        except subprocess.CalledProcessError:
            result = False
            next_size_file = open('next_size', 'r')
            size_str = next_size_file.readline().strip()
            next_size_file.close() 
        except subprocess.TimeoutExpired:
            vprint(options, f'[QRM TO]: Timeout after {options.qrm_to}')
            result = False
            break
        qrm_result = result
    
    vprint_instance_banner(options, f'[QRM]: {ivy_name}')
    if qrm_result:
        vprint(options, '[QRM RESULT]: PASS')
    else:
        vprint(options, '[QRM RESULT]: FAIL')
    os.system('rm next_size')

if __name__ == '__main__':
    run_all(sys.argv[1], sys.argv[2:])