import sys
import os
from os import path
import subprocess
import getopt
from util import *
from verbose import *

def usage ():
    print('Usage:   python3 run_all.py FILE.yaml')
    print('         check all cases in the given yaml file')
    print('')
    print('Options:')
    print('-a           disable find all minimal solutions (default: on)')
    print('-m           disable suborbits (default: on)')
    print('-k           disable checking quantifier inference (default: on)')
    print('-c sat | mc  use sat solver or approximate model counter for coverage estimation (default: sat)')
    print('-v LEVEL     set verbose level (defult:0, max: 5)')
    print('-l LOG       append verbose info to LOG (default: off)')
    print('-r           write reachable states to FILE.reach (default: off)')
    print('-p           write prime orbits to FILE.pis (default: off)')
    print('-q           write quantified prime orbits to FILE.qpis (default: off)')
    print('-w           write .reach, .pis, .qpis, equivalent to options -r -p -q (default: off)')
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

def run_all(yaml_name, args):
    sys_args = args.copy()
    try:
        opts, args = getopt.getopt(args, "amkc:v:l:rpqwh")
    except getopt.GetoptError as err:
        print(err)
        usage_and_exit()

    options = QrmOptions()
    options.mode = Mode.yaml
    if file_exist(yaml_name):
        options.yaml_filename = yaml_name
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

    instances = get_instances_from_yaml(options.yaml_filename)
    for ivy_name, sizes in instances.items():
        vprint_instance_banner(options, f'[QRM]: {ivy_name}')
        qrm_result = False
        for size_str in sizes:
            qrm_args = ['python3', 'qrm.py', ivy_name, '-s', size_str, '-d'] + sys_args
            result = True 
            try:
                subprocess.run(qrm_args, check=True, timeout=options.qrm_to) 
                sys.stdout.flush()
            except subprocess.CalledProcessError:
                result = False
            except subprocess.TimeoutExpired:
                vprint(options, f'[QRM TO]: Timeout after {options.qrm_to}')
                result = False
            qrm_result = result
        
        vprint_instance_banner(options, f'[QRM]: {ivy_name}')
        if qrm_result:
            vprint(options, '[QRM RESULT]: PASS')
        else:
            vprint(options, '[QRM RESULT]: FAIL')

if __name__ == '__main__':
    run_all(sys.argv[1], sys.argv[2:])