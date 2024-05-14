
from __future__ import print_function
import copy

numN = 2
numE = 5

ZERO = 0

outFile = "out"
outF = None
def fprint(s):
    global outF
    outF.write(s + "\n")


class State():
    def __init__(self, state=None):
        if state == None:
            self.reset()
        else:
            self.copy(state)
    
    def copy(self, state):
        self.ep = copy.deepcopy(state.ep)
        self.held = copy.deepcopy(state.held)
        self.transfer = copy.deepcopy(state.transfer)
        self.locked = copy.deepcopy(state.locked)

    def __key(self):
        return (str(self.ep), str(self.held), str(self.transfer), str(self.locked))

    def __hash__(self):
        return hash(self.__key())

    def __eq__(self, other):
        return (self.__class__ == other.__class__ and
                self.ep == other.ep and
                self.held == other.held and
                self.transfer == other.transfer and
                self.locked == other.locked)

    def reset(self):
        self.ep = [ZERO for i in range(numN)]
        self.held = [False for i in range(numN)]
        self.transfer = [[False for j in range(numN)] for i in range(numE)]
        self.locked = [[False for j in range(numN)] for i in range(numE)]
    
    def update_init(self, first, e):
        assert(e != ZERO)
        self.reset()
        self.ep[first] = e
        self.held[first] = True
    
    def str(self, prefix="\t"):
        res = ""
        res += prefix + "held: "
        for n in range(numN):
            if self.held[n]:
                res += "N" + str(n) + "  "
        res += "\n"
        res += prefix + "ep: "
        for n in range(numN):
            res += "N" + str(n) + ":" + str(self.ep[n]) + "  "
        res += "\n"
        res += prefix + "transfer: "
        for e in range(numE):
            for n in range(numN):
                if self.transfer[e][n]:
                    res += "<" + str(e) + ",N" + str(n) + ">  "
        res += "\n"
        res += prefix + "locked: "
        for e in range(numE):
            for n in range(numN):
                if self.locked[e][n]:
                    res += "<" + str(e) + ",N" + str(n) + ">  "
        res += "\n"
        return res
    
    def str_header_espresso(self):
        res = ""
        for n in range(numN):
            res += "held(N%d) " % n
        for n in range(numN):
            for e in range(numE):
                res += "ep(N%d)=%d " % (n, e)
        for e in range(numE):
            for n in range(numN):
                res += "transfer(%d,N%d) " % (e, n)
        for e in range(numE):
            for n in range(numN):
                res += "locked(%d,N%d) " % (e, n)
        return res
        
    def str_espresso(self):
        res = ""
        for n in range(numN):
            res += "1 " if self.held[n] else "0 "
        for n in range(numN):
            for e in range(numE):
                res += "1 " if (self.ep[n] == e) else "0 "
        for e in range(numE):
            for n in range(numN):
                res += "1 " if self.transfer[e][n] else "0 "
        for e in range(numE):
            for n in range(numN):
                res += "1 " if self.locked[e][n] else "0 "
        return res
        

class System():
    def __init__(self):
        self.R = set()
        self.forwardReach()
            
    def grant(self, state, n1, n2, e):
        if not state.held[n1]:
            return False, state
        if e <= state.ep[n1]:
            return False, state
        
        dest = State(state)
        dest.transfer[e][n2] = True
        dest.held[n1] = False
        return True, dest
    
    def accept(self, state, n, e, nondet):
        if not state.transfer[e][n]:
            return False, state
        
        dest = State(state)
        dest.transfer[e][n] = nondet
        if e > state.ep[n]:
            dest.held[n] = True
            dest.ep[n] = e
            dest.locked[e][n] = True
        return True, dest
    
    def forwardReach(self):
        q = []

        print("adding init")
        for first in range(numN):
            e = 1
#             for e in range(numE):
#                 if e != ZERO:
            init_state = State()
            init_state.update_init(first, e)
            q.append(init_state)
            print("init: \n%s" % init_state.str())
        
        count = 0
        while len(q) != 0:
            count += 1
            curr = q.pop()
            if curr not in self.R:
                print("curr: \n%s" % curr.str())
                self.R.add(curr)
                for n1 in range(numN):
                    for n2 in range(numN):
                        for e in range(numE):
                            updated, dest = self.grant(curr, n1, n2, e)
                            if updated:
                                if dest not in self.R:
                                    q.append(dest)
                                    print("\tstep: grant(N%d,N%d,%d)" % (n1, n2, e))
                for n in range(numN):
                    for e in range(numE):
                        for nondet in [True, False]:
                            updated, dest = self.accept(curr, n, e, nondet)
                            if updated:
                                if dest not in self.R:
                                    q.append(dest)
                                    print("\tstep: accept(N%d,%d,%s)" % (n, e, nondet))
        
        print("#R = %d" % len(self.R))
        
    def print_R_espresso(self):
        global outF, outFile
        outFile = "toy_lock_%dN_%dE" % (numN, numE)
        
        numCol = numN + numN*numE*3

        outF = open("pla/"+outFile+".pla", 'w')
        fprint("# toy lock: %d nodes, %d epochs" % (numN, numE))
        fprint(".i %d" % numCol)
        fprint(".o 1")
        fprint(".ilb %s" % next(iter(self.R)).str_header_espresso())
        fprint(".ob notR")
        fprint(".phase 0")
        for state in self.R:
            fprint(state.str_espresso() + " 1")
        fprint(".e")
        fprint("")
        print("Now run espresso with the following command:")
        print("./espresso/espresso.linux -o eqntott pla/%s.pla > txt/%s.txt" % (outFile, outFile))
            

def main():
    s = System()
    print("OK")
    s.print_R_espresso()


if __name__ == "__main__":
    main()
