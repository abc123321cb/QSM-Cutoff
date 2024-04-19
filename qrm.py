import sys
import getopt
from os import path
from verbose import *
from util import * 
from forward import *
from protocol import Protocol 
from prime import PrimeOrbits
from minimize import Minimizer
import ic3po.ivy2vmt

def usage ():
    print('Usage: python3 qrm.py [options]')
    print(' -h              usage')
    print(' -v LEVEL        set verbose level (defult:0, max: 5)')
    print(' -i FILE.ivy     read FILE.ivy file')
    print(' -o FILE.ptcl    produce prime orbits')
    print(' -q FILE.orb     quantify prime orbits')
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
        opts, args = getopt.getopt(args, "hv:i:o:q:m:c:a")
    except getopt.GetoptError as err:
        print(err)
        usage_and_exit()

    options = QrmOptions()
    for (optc, optv) in opts:
        if optc == '-v':
            options.verbosity = int(optv)
            if options.verbosity < 0 or options.verbosity > 5:
                usage_and_exit()
        elif optc == '-i':
            options.mode = Mode.ivy
            if file_exist(optv):
                options.filename = optv
        elif optc == '-o':
            options.mode = Mode.gen
            if file_exist(optv):
                options.filename = optv
        elif optc == '-q':
            options.mode = Mode.qfy
            if file_exist(optv):
                options.filename = optv
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
        ivy_filename  = options.filename
        vmt_filename  = ivy_filename.split('.')[0] + '.vmt'
        ptcl_filename = ivy_filename.split('.')[0] + '.pctl'
        ic3po.ivy2vmt.compile(ivy_filename, vmt_filename)
        forward_reach(input=vmt_filename, output=ptcl_filename)
    elif options.mode == Mode.gen:
        protocol = Protocol(options)
        prime_orbits = PrimeOrbits(options) 
        prime_orbits.symmetry_aware_enumerate(protocol)               

    elif options.mode == Mode.min:
        orbits = read_orbits(options.filename)
        minimizer = Minimizer(orbits, options)
        minimizer.solve()

if __name__ == '__main__':
    qrm(sys.argv[1:])
