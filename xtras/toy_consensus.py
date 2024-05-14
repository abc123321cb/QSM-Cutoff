
from __future__ import print_function
from math import comb, floor
import copy
from itertools import chain, combinations

numN = 3
numV = 2

def powerset(iterable):
    "powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)"
    s = list(iterable)
    return chain.from_iterable(combinations(s, r) for r in range(len(s)+1))

def majority():
    return floor(numN/2)+1

numQ = comb(numN, majority())

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
        self.vote = copy.deepcopy(state.vote)
        self.decision = copy.deepcopy(state.decision)
        self.member = copy.deepcopy(state.member)

    def __key(self):
        return (str(self.vote), str(self.decision), str(self.member))

    def __hash__(self):
        return hash(self.__key())

    def __eq__(self, other):
        return (self.__class__ == other.__class__ and
                self.vote == other.vote and
                self.decision == other.decision and
                self.member == other.member)

    def reset(self):
        self.vote = [[False for v in range(numV)] for n in range(numN)]
        self.decision = [False for v in range(numV)]
        self.member = [s for s in powerset([n for n in range(numN)]) if len(s)==majority()]
   
    def didNotVote(self, n):
        return all(not self.vote[n][v] for v in range(numV))
        
    def chosenAt(self, q, v):
        return all(self.vote[n][v] for n in self.member[q])
            
    def str(self, prefix="\t"):
        res = ""
        res += prefix + "member: "
        for q in range(numQ):
            res += f"q{q}: {self.member[q]}"
            res += "\t"
        res += "\n"
        res += prefix + "vote: "
        for n in range(numN):
            for v in range(numV):
                if self.vote[n][v]:
                    res += f"n{n}->v{v}"
        res += "\n"
        res += prefix + "decision: "
        for v in range(numV):
            if self.decision[v]:
                res += f"v{v}"
        return res
    
    def str_header_pla(self):
        res = ""
        for n in range(numN):
            for v in range(numV):
                res += f"vote(n{n},v{v}) "
        for v in range(numV):
            res += f"decision(v{v}) "
        for n in range(numN):
            res += f"didNotVote(n{n}) "
        for q in range(numQ):
            for v in range(numV):
                res += f"chosenAt(q{q},v{v}) "
        return res
        
    def str_pla(self):
        res = ""
        for n in range(numN):
            for v in range(numV):
                res += "1" if self.vote[n][v] else "0"
        res += " "
        for v in range(numV):
            res += "1" if self.decision[v] else "0"
        res += " "
        for n in range(numN):
            res += "1" if self.didNotVote(n) else "0"
        res += " "
        for q in range(numQ):
            for v in range(numV):
                res += "1" if self.chosenAt(q, v) else "0"
        return res
        

class System():
    def __init__(self):
        self.R = set()
        self.forwardReach()
    
    def cast_vote(self, state, n, v):
        if not state.didNotVote(n):
            return False, state

        dest = State(state)
        dest.vote[n][v] = True
        return True, dest
            
    def decide(self, state, v, q):
        if not state.chosenAt(q, v):
            return False, state

        dest = State(state)
        dest.decision[v] = True
        return True, dest
    
    def forwardReach(self):
        queue = []

        print("adding init")
        init_state = State()
        queue.append(init_state)
        
        count = 0
        while len(queue) != 0:
            count += 1
            curr = queue.pop()
            if curr not in self.R:
                print("curr: \n%s" % curr.str())
                self.R.add(curr)
                for n in range(numN):
                    for v in range(numV):
                        updated, dest = self.cast_vote(curr, n, v)
                        if updated:
                            if dest not in self.R:
                                queue.append(dest)
                                print(f"\tstep: cast_vote(n{n},v{v})")
                                # print("dest: \n%s" % dest.str())
                for v in range(numV):
                    for q in range(numQ):
                        updated, dest = self.decide(curr, v, q)
                        if updated:
                            if dest not in self.R:
                                queue.append(dest)
                                print(f"\tstep: decide(v{v},q{q})")
                                # print("dest: \n%s" % dest.str())
        print("#R = %d" % len(self.R))
        
    def print_R_pla(self):
        global outF, outFile
        outFile = f"toy_consensus_{numN}N_{numV}V"
        
        numCol = numN*numV + numV + numN + numQ*numV

        outF = open("pla/"+outFile+".pla", 'w')
        fprint(f"# toy_consensus: {numN} nodes, {numV} values")
        fprint(".i %d" % numCol)
        fprint(".o 1")
        fprint(".ilb %s" % next(iter(self.R)).str_header_pla())
        fprint(".ob notR")
        fprint(".phase 0")
        for state in self.R:
            fprint(state.str_pla() + " 1")
        fprint(".e")
        fprint("")            

def main():
    s = System()
    print("OK")
    s.print_R_pla()


if __name__ == "__main__":
    main()
