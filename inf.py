import math
from qformula import QFormula
from prime import *
from verbose import *
from protocol import Protocol
import re
from typing import Iterable, List, Sequence
from itertools import product
from pyeda.inter import ttvars, truthtable
from pyeda.boolalg.minimization import espresso_tts
from ivy import ivy_logic as il
from ivy import ivy_logic_utils as ilu
from qutil import get_terms, get_qterms
from qinference import *
from util import FormulaUtility as futil

# To use this class first initilize it then call get_qclause to get a forall statement for a for_all statement
class Inference:
    
    def __init__(self, orbit: PrimeOrbit, options: QrmOptions, protocol: Protocol, is_dnf: bool):
        self.orbit   = orbit
        self.options = options
        self.protocol = protocol
        self.is_dnf  = is_dnf

        self.forall_clauses: List[QFormula] = []


    def get_qclause(self):

        print(self.orbit)

        restrictions = self.enumerate()
        return self._get_cnf_qclause(restrictions)
    

    #expand the clause out so a orbit like this at size =2
    # ['e(node0)', 'h(node1)', '~l(node1)']
    # becomes
    # ['e(N0)', 'H(N1)', '~l(N2)']
    # we are making every spot get its own quantifier.
    # then take this table change it into equality checks so over e01e02e12 for this case.
    # We make all the non bell satifiable possiabities don't care so e01,e02,~e12 would be one because N0=N1 & N0=N2 -> N1=N2
    # Then we have to mark all the valid substutions from the orbit as true and the rest as false
    # run espresso_tts to get the combinations and negate to cover reach instead of ~reach
    # Note all functions here until _get_cnf_qclauses are for enumerate
    # RETURNS: something like And(e01 OR(e12 e02)) note it should always be a and on the outer layer
    def enumerate(self):
        clause = self.orbit.repr_prime.literals_list
        for i in clause:
            print(i)
            print(type(i))
    

    # INPUT the expression from enumerate
    # we then convert e01 and so on into the right format for the rest of the code so the And(e01 OR(e12 e02))
    # turns into forall N0,N1,N2. (N0=N1 & (N1=N2 | N0=N2)) -> orbit stuff 

    def _get_cnf_qclause(self, expression):
        return
