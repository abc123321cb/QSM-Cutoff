import sys
from os import path
from protocol import Protocol 
from prime import PrimeOrbits 

def usage ():
    print("Usage: python3 qrm.py protocol.ptcl [options]")

def usage_and_exit ():
    usage()
    sys.exit(1)

if __name__ == '__main__':
    if len(sys.argv) < 2:
        usage_and_exit ()   

    if not path.isfile(sys.argv[1]):
        print("Cannot find file: {}".format(sys.argv[1]))
        usage_and_exit ()

    reach_filename = sys.argv[1]
    protocol = Protocol(reach_filename)
    # print(protocol)

    prime_orbits = PrimeOrbits()
    prime_orbits.symmetry_aware_enumerate(protocol)               
    print(prime_orbits)