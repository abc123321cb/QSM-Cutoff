import sys
import getopt
from os import path
from frontend.ivy2vmt import compile_ivy2vmt
from verbose import *
from util import * 
from forward import *
from transition import *
from protocol import Protocol 
from prime import PrimeOrbits
from minimize import Minimizer

def usage ():
    print('Usage: python3 qrm.py [options]')
    print(' -h              usage')
    print(' -v LEVEL        set verbose level (defult:0, max: 5)')
    print(' -i FILE.ivy     read FILE.ivy file')
    print(' -s SORT_SIZE    pass sort size (format: -s [sort1=size1,sort2=size2 ...])')
    print(' -r              write reachable states to FILE.ptcl (default: do not write)')
    print(' -c sat | mc     use sat solver or approximate model counter for coverage estimation (default: sat)')
    print(' -a              find all minimal solutions (default: off)')

def usage_and_exit():
    usage()
    sys.exit(1)

def file_exist(filename) -> bool:
    if not path.isfile(filename):
        print(f'Cannot find file: {filename}')
        usage_and_exit ()
    return True

def qrm(args):
    try:
        opts, args = getopt.getopt(args, "hv:i:s:rm:c:a")
    except getopt.GetoptError as err:
        print(err)
        usage_and_exit()

    options = QrmOptions()
    size_str ='' ## temporary
    for (optc, optv) in opts:
        if optc == '-v':
            options.verbosity = int(optv)
            if options.verbosity < 0 or options.verbosity > 5:
                usage_and_exit()
        elif optc == '-i':
            if file_exist(optv):
                options.ivy_filename = optv
                options.vmt_filename = optv.split('.')[0] + '.vmt'
                options.R_filename   = optv.split('.')[0] + '.pctl'
        elif optc == '-s':
            size_str = optv 
        elif optc == '-r':
            options.writeR = True
        elif optc == '-c':
            if optv == 'sat' or optv == 'mc':
                options.useMC = optv
            else:
                usage_and_exit()
        elif optc == '-a':
            options.all_solutions = True
        else:
            usage_and_exit()

    # step1: generate reachability
    compile_ivy2vmt(options.ivy_filename, options.vmt_filename)
    tran_sys  = get_transition_system(options.vmt_filename, size_str)
    reachblty = get_forward_reachability(tran_sys)
    protocol  = Protocol(options)
    protocol.initialize(tran_sys, reachblty)

    # step2: generate prime orbits
    prime_orbits = PrimeOrbits(options) 
    prime_orbits.symmetry_aware_enumerate(protocol)               

    # step3: quantifier inference
    prime_orbits.quantifier_inference(reachblty.atoms, tran_sys, options)

    # step4: minimization
    minimizer = Minimizer(prime_orbits.orbits, options)
    minimizer.solve()

if __name__ == '__main__':
    qrm(sys.argv[1:])
