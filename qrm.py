import sys
import getopt
from os import path
from protocol import Protocol 
from prime import PrimeOrbits 

def usage ():
    print("Usage: python3 qrm.py [options]")
    print(" -h              usage")
    print(" -v              verbose")
    print(" -o FILE.ptcl    produce prime orbits")
    print(" -q FILE.orb     quantify prime orbits")
    print(" -m FILE.orb     minimize quantified prime orbits")

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
        opts, args = getopt.getopt(args, "hvo:q:m:")
    except getopt.GetoptError as err:
        print(err)
        usage_and_exit()

    verbose  = False
    genPrime = False
    qfyPrime = False
    minPrime = False 
    filename = ''
    for (opt, file) in opts:
        if opt == '-v':
            verbose = True
        elif opt == '-o':
            genPrime = True
            if file_exist(file):
                filename = file
        elif opt == '-q':
            qfyPrime = True
            if file_exist(file):
                filename = file
        elif opt == '-m':
            minPrime = True
            if file_exist(file):
                filename = file
        else:
            usage_and_exit()

    prime_orbits = PrimeOrbits()
    if(genPrime):
        protocol = Protocol(filename)
        if (verbose):
            print(protocol)
        prime_orbits.symmetry_aware_enumerate(protocol)               
        print(prime_orbits)
    elif(qfyPrime):
        prime_orbits.read(filename)
        prime_orbits.quantifier_inference()
        print(prime_orbits)
    elif(minPrime):
        prime_orbits.read(filename)
        minimizer = Minimizer(prime_orbits.orbits)
        minimizer.solve()

if __name__ == '__main__':
    qrm(sys.argv[1:])
