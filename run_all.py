import sys
import os
from os import path
import subprocess
import getopt
from util import *
from verbose import *

def usage ():
    print('Usage:   python3 run_all.py FILE.yaml [options]')
    print('         check all cases in the given yaml file')
    print('')
    print('Options:')
    print('-v LEVEL     set verbose level (defult:0, max: 5)')
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

def run_all(yaml_name, args):
    try:
        opts, args = getopt.getopt(args, "v:c:rpqwamh")
    except getopt.GetoptError as err:
        print(err)
        usage_and_exit()

    options = QrmOptions()
    options.mode = Mode.yaml
    options.yaml_filename = yaml_name
    for (optc, optv) in opts:
        if optc == '-v':
            options.verbosity = int(optv)
            if options.verbosity < 0 or options.verbosity > 5:
                usage_and_exit()
        elif optc == '-c':
            if optv == 'sat' or optv == 'mc':
                options.useMC = optv
            else:
                usage_and_exit()
        elif optc == '-r':
            options.writeReach = True
        elif optc == '-p':
            options.writPrime = True
        elif optc == '-q':
            options.writeQI = True
        elif optc == '-w':
            options.writeReach = True
            options.writePrime = True
            options.writeQI    = True
        elif optc == '-a':
            options.all_solutions = True
        elif optc == '-m':
            options.merge_suborbits = True
        else:
            usage_and_exit()

    instances = get_instances_from_yaml(options.yaml_filename)
    for ivy_name, sizes in instances.items():
        vprint_instance_banner(options, f'QRM: {ivy_name}')
        qrm_result = False
        for size_str in sizes:
            qrm_args = ['python3', 'qrm.py', '-i', ivy_name, '-s', size_str, '-d'] + args
            ivy_result = True 
            try:
                subprocess.run(qrm_args, check=True) 
                sys.stdout.flush()
            except subprocess.CalledProcessError:
                ivy_result = False
            qrm_result = ivy_result
        
        vprint_instance_banner(options, f'QRM: {ivy_name}')
        if qrm_result:
            vprint(options, 'QRM RESULT: Pass')
        else:
            vprint(options, 'QRM RESULT: Fail')

if __name__ == '__main__':
    run_all(sys.argv[1], sys.argv[2:])