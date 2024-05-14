
from __future__ import print_function
import copy
import operator
import os

numN = 2
numE = 3

outFile = "out"
outF = None
def fprint(s):
    global outF
    outF.write(s + "\n")

# Python function to print permutations of a given list 
def permutation(lst): 
  
    # If lst is empty then there are no permutations 
    if len(lst) == 0: 
        return [] 
  
    # If there is only one element in lst then, only 
    # one permuatation is possible 
    if len(lst) == 1: 
        return [lst] 
  
    # Find the permutations for lst if there are 
    # more than 1 characters 
  
    l = [] # empty list that will store current permutation 
  
    # Iterate the input(lst) and calculate the permutation 
    for i in range(len(lst)): 
       m = lst[i] 
  
       # Extract lst[i] or m from the list.  remLst is 
       # remaining list 
       remLst = lst[:i] + lst[i+1:] 
  
       # Generating all permutations where m is first 
       # element 
       for p in permutation(remLst): 
           l.append([m] + p) 
    return l 

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
        self.le = copy.deepcopy(state.le)

    def __key(self):
        return (str(self.ep), str(self.held), str(self.transfer), str(self.locked), str(self.le))

    def __hash__(self):
        return hash(self.__key())

    def __eq__(self, other):
        return (self.__class__ == other.__class__ and
                self.ep == other.ep and
                self.held == other.held and
                self.transfer == other.transfer and
                self.locked == other.locked and
                self.le == other.le)

    def reset(self):
        self.ep = [0 for i in range(numN)]
        self.held = [False for i in range(numN)]
        self.transfer = [[False for j in range(numN)] for i in range(numE)]
        self.locked = [[False for j in range(numN)] for i in range(numE)]
        self.le = [[False for j in range(numE)] for i in range(numE)]
    
    def update_init(self, first, e, order):
        self.reset()
        self.ep = [order[0] for i in range(numN)]
        self.ep[first] = e
        self.held[first] = True
        for i in range(len(order)):
            ei = order[i]
            for j in range(i, len(order)):
                ej = order[j]
                self.le[ei][ej] = True
    
    def str(self, prefix="\t"):
        res = ""
        res += prefix + "held: "
        for n in range(numN):
            if self.held[n]:
                res += "N" + str(n) + "  "
        res += "\n"
        res += prefix + "ep: "
        for n in range(numN):
            res += "N" + str(n) + ":E" + str(self.ep[n]) + "  "
        res += "\n"
        res += prefix + "transfer: "
        for e in range(numE):
            for n in range(numN):
                if self.transfer[e][n]:
                    res += "<E" + str(e) + ",N" + str(n) + ">  "
        res += "\n"
        res += prefix + "locked: "
        for e in range(numE):
            for n in range(numN):
                if self.locked[e][n]:
                    res += "<E" + str(e) + ",N" + str(n) + ">  "
        res += "\n"
        res += prefix + "le: "
        ordering = {}
        for e in range(numE):
            ordering[e] = numE
        for e1 in range(numE):
            for e2 in range(numE):
                if self.le[e1][e2]:
                    ordering[e1] -= 1
        for e, v in sorted(ordering.items(), key=operator.itemgetter(1)):
            res += "E%d < " % e
        res += "\n"
        return res
    
    def str_header_espresso(self):
        res = ""
        for n in range(numN):
            res += "held(N%d) " % n
        for n in range(numN):
            for e in range(numE):
                res += "ep(N%d)=E%d " % (n, e)
        for e in range(numE):
            for n in range(numN):
                res += "transfer(E%d,N%d) " % (e, n)
        for e in range(numE):
            for n in range(numN):
                res += "locked(E%d,N%d) " % (e, n)
        for e1 in range(numE):
            for e2 in range(numE):
                res += "le(E%d,E%d) " % (e1, e2)
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
        for e1 in range(numE):
            for e2 in range(numE):
                res += "1 " if self.le[e1][e2] else "0 "
        return res
        

class System():
    def __init__(self):
        self.R = set()
        self.forwardReach()
            
    def grant(self, state, n1, n2, e):
        if not state.held[n1]:
            return False, state
        if state.le[e][state.ep[n1]]:
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
        if not state.le[e][state.ep[n]]:
            dest.held[n] = True
            dest.ep[n] = e
            dest.locked[e][n] = True
        return True, dest
    
    def forwardReach(self):
        q = []

        print("adding init")
        for first in range(numN):
            epochs = [i for i in range(numE)]
            for order in permutation(epochs):
                for nz in range(1, len(order)):
                    init_state = State()
                    init_state.update_init(first, order[nz], order)
                    q.append(init_state)
                    print("init: \n%s" % init_state.str())
#         assert(0)
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
        outFile = "toy_lock_le_%dN_%dE" % (numN, numE)
        
        numCol = numN + numN*numE*3 + numE*numE

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
        outF.close()
        
        print("Running espresso:")
#         cmd = "./espresso/espresso.linux -D exact -o eqntott pla/%s.pla" % (outFile)
        cmd = "./espresso/espresso.linux -o eqntott pla/%s.pla" % (outFile)
        print(cmd)
        os.system(cmd + " > espresso.txt")
        cmd = "cat espresso.txt | ./pp.sh > txt/%s.txt" % outFile
        os.system(cmd)
        print("Output generated in txt/%s.txt" % outFile)

def main():
    s = System()
    print("OK")
    s.print_R_espresso()


if __name__ == "__main__":
    main()
