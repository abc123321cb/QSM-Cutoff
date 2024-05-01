import sys
import getopt
from os import path
from verbose import *
from util import * 
from forward import *
from protocol import Protocol 
from prime import PrimeOrbits
from minimize import Minimizer
from frontend.ivy2vmt import compile_ivy2vmt

def usage ():
    print('Usage: python3 qrm.py [options]')
    print(' -h              usage')
    print(' -v LEVEL        set verbose level (defult:0, max: 5)')
    print(' -i FILE.ivy     read FILE.ivy file')
    print(' -s SORT_SIZE    pass sort size (format: -s [sort1=size1,sort2=size2 ...])')
    print(' -r              write reachable states to FILE.ptcl (default: do not write)')
    print(' -m FILE.orb     minimize quantified prime orbits')
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
    size_str =''## temporary
    for (optc, optv) in opts:
        if optc == '-v':
            options.verbosity = int(optv)
            if options.verbosity < 0 or options.verbosity > 5:
                usage_and_exit()
        elif optc == '-i':
            options.mode = Mode.ivy
            if file_exist(optv):
                options.ivy_filename = optv
                options.vmt_filename = optv.split('.')[0] + '.vmt'
                options.R_filename   = optv.split('.')[0] + '.pctl'
        elif optc == '-s':
            size_str = optv 
        elif optc == '-r':
            options.writeR = True
        elif optc == '-m':
            options.mode = Mode.min
            if file_exist(optv):
                options.filename = optv
        elif optc == '-c':
            if optv == 'sat' or optv == 'mc':
                options.useMC = optv
            else:
                usage_and_exit()
        elif optc == '-a':
            options.all_solutions = True
        else:
            usage_and_exit()

    if options.mode == Mode.ivy:
        compile_ivy2vmt(options.ivy_filename, options.vmt_filename)
        protocol = forward_reach(size_str, options)
        prime_orbits = PrimeOrbits(options) 
        prime_orbits.symmetry_aware_enumerate(protocol)               

    elif options.mode == Mode.min:
        orbits = read_orbits(options.filename)
        minimizer = Minimizer(orbits, options)
        minimizer.solve()

if __name__ == '__main__':
    qrm(sys.argv[1:])
