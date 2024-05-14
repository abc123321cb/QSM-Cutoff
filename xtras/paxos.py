#!/usr/bin/python2.7

from __future__ import print_function
import copy

numA = 3
numV = 2
numB = 2
numQ = 3

NONE = -1

outFile = "out.pla"
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
        self.maxBal = copy.deepcopy(state.maxBal)
        self.maxVBal = copy.deepcopy(state.maxVBal)
        self.maxVal = copy.deepcopy(state.maxVal)
        self.msgs = copy.deepcopy(state.msgs)
        self.member = copy.deepcopy(state.member)

    def __key(self):
        return (str(self.maxBal), str(self.maxVBal), str(self.maxVal), str(self.msgs))

    def __hash__(self):
        return hash(self.__key())

    def __eq__(self, other):
        return (self.__class__ == other.__class__ and
                self.maxBal == other.maxBal and
                self.maxVBal == other.maxVBal and
                self.maxVal == other.maxVal and
                self.msgs == other.msgs)

    def reset(self):
        self.maxBal = [-1 for i in range(numA)]
        self.maxVBal = [-1 for i in range(numA)]
        self.maxVal = [NONE for i in range(numA)]
        self.msgs = {
            "1a": [False for i in range(numB)],
            "1b": [[[[False for l in range(NONE, numV)] for k in range(-1, numB)] for j in range(numB)] for i in range(numA)],
            "2a": [[False for j in range(numV)] for i in range(numB)],
            "2b": [[[False for k in range(numV)] for j in range(numB)] for i in range(numA)],
        }
        self.member = [[False for j in range(numQ)] for i in range(numA)]
        self.member[0][0] = True
        self.member[1][0] = True
        self.member[0][1] = True
        self.member[2][1] = True
        self.member[1][2] = True
        self.member[2][2] = True

    def str(self, prefix="\t"):
        res = ""
        res += prefix + "maxBal:   "
        for i in range(numA):
            res += "A" + str(i) + ": " + str(self.maxBal[i]) + "  "
        res += "\n"
        res += prefix + "maxVBal:  "
        for i in range(numA):
            res += "A" + str(i) + ": " + str(self.maxVBal[i]) + "  "
        res += "\n"
        res += prefix + "maxVal:   "
        for i in range(numA):
            res += "A" + str(i) + ": " + (str(self.maxVal[i]) if self.maxVal[i] != NONE else "None") + "  "
        res += "\n"
        res += prefix + "msgs-1a:  "
        for i in range(numB):
            if self.msgs["1a"][i]:
                res += "(bal = " + str(i) + ")  "
        res += "\n"
        res += prefix + "msgs-1b:  "
        for i in range(numA):
            for j in range(numB):
                for k in range(-1, numB):
                    for l in range(NONE, numV):
                        if self.msgs["1b"][i][j][k][l]:
                            res += "(acc = " + str(i) + ", bal = " + str(j) + ", mbal = " + str(k) + ", mval = " + (str(l) if l != NONE else "None") + ")  "
        res += "\n"
        res += prefix + "msgs-2a:  "
        for i in range(numB):
            for j in range(numV):
                if self.msgs["2a"][i][j]:
                    res += "(bal = " + str(i) + ", val = " + (str(j) if j != NONE else "None") + ")  "
        res += "\n"
        res += prefix + "msgs-2b:  "
        for i in range(numA):
            for j in range(numB):
                for k in range(numV):
                    if self.msgs["2b"][i][j][k]:
                        res += "(acc = " + str(i) + ", bal = " + str(j) + ", val = " + (str(k) if l != NONE else "None") + ")  "
        res += "\n"
        return res

    def str_header_espresso(self):
        res = ""
        for a in range(numA):
            for b in range(-1, numB):
                res += "maxBal(A%d)=%d " % (a, b)
        res += " "
        for a in range(numA):
            for b in range(-1, numB):
                res += "maxVBal(A%d)=%d " % (a, b)
        res += " "
        for a in range(numA):
            for v in range(NONE, numV):
                res += "maxVal(A%d)=%s " % (a, str(v) if v != None else "None")
        res += " "
        for b in range(numB):
            res += "msgs-1a(bal=%d) " % (b)
        res += " "
        for a in range(numA):
            for b in range(numB):
                for mbal in range(-1, numB):
                    for mval in range(NONE, numV):
                        res += "msgs-1b(acc=%d,bal=%d,mbal=%d,mval=%s) " % (a, b, mbal, str(mval) if mval != None else "None")
        res += " "
        for b in range(numB):
            for v in range(numV):
                res += "msgs-2a(bal=%d,val=%d) " % (b, v)
        res += " "
        for a in range(numA):
            for b in range(numB):
                for v in range(numV):
                    res += "msgs-2b(acc=%d,bal=%d,val=%d) " % (a, b, v)
        res += " "
        return res

    def str_espresso(self):
        res = ""
        for a in range(numA):
            for b in range(-1, numB):
                if (self.maxBal[a] == b):
                    res += "1"
                else:
                    res += "0"
        res += " "
        for a in range(numA):
            for b in range(-1, numB):
                if (self.maxVBal[a] == b):
                    res += "1"
                else:
                    res += "0"
        res += " "
        for a in range(numA):
            for v in range(NONE, numV):
                if (self.maxVal[a] == v):
                    res += "1"
                else:
                    res += "0"
        res += " "
        for b in range(numB):
            if self.msgs["1a"][b]:
                res += "1"
            else:
                res += "0"
        res += " "
        for a in range(numA):
            for b in range(numB):
                for mbal in range(-1, numB):
                    for mval in range(NONE, numV):
                        if self.msgs["1b"][a][b][mbal][mval]:
                            res += "1"
                        else:
                            res += "0"
        res += " "
        for b in range(numB):
            for v in range(numV):
                if self.msgs["2a"][b][v]:
                    res += "1"
                else:
                    res += "0"
        res += " "
        for a in range(numA):
            for b in range(numB):
                for v in range(numV):
                    if self.msgs["2b"][a][b][v]:
                        res += "1"
                    else:
                        res += "0"
        res += " "
        return res

class System():
    def __init__(self):
        self.R = set()
        self.forwardReach()

    def a_in_Q1b(self, state, a, _q_, _b_):
        return state.member[a][_q_] and any(any(state.msgs["1b"][a][_b_][mbal][mval] for mval in range(NONE, numV)) for mbal in range(-1, numB))

    def mbal_mval_in_Q1bv(self, state, mbal, mval, _q_, _b_):
        return (mbal >= 0) and any((state.member[a][_q_] and state.msgs["1b"][a][_b_][mbal][mval]) for a in range(numA))

    def phase_1a(self, state, b):
        dest = State(state)
        dest.msgs["1a"][b] = True
        return True, dest
        
    def phase_1b(self, state, a, _b_):
        if not (state.msgs["1a"][_b_] and _b_ > state.maxBal[a]):
            return False, state
        dest = State(state)
        dest.maxBal[a] = _b_
        dest.msgs["1b"][a][_b_][state.maxVBal[a]][state.maxVal[a]] = True;
        return True, dest

    def phase_2a(self, state, b, v):
        if any(state.msgs["2a"][b][v] for v in range(numV)):
            return False, state
        exists_q = False
        for q in range(numQ):
            forall_a = True
            for a in range(numA):
                if state.member[a][q] and not self.a_in_Q1b(state, a, q, b):
                    forall_a = False
            empty_Q1bv = True
            for mbal in range(-1, numB):
                for mval in range(NONE, numV):
                    if self.mbal_mval_in_Q1bv(state, mbal, mval, q, b):
                        empty_Q1bv = False
            exists_m = False
            for mbal in range(-1, numB):
                if not self.mbal_mval_in_Q1bv(state, mbal, v, q, b):
                    continue
                forall_mm = True
                for mmbal in range(-1, numB):
                    for mmval in range(NONE, numV):
                        if self.mbal_mval_in_Q1bv(state, mmbal, mmval, q, b):
                            if not (mbal >= mmbal):
                                forall_mm = False
                if forall_mm:
                    exists_m = True
            if forall_a and (empty_Q1bv or exists_m):
                exists_q = True
        if not exists_q:
            return False, state
        dest = State(state)
        dest.msgs["2a"][b][v] = True
        return True, dest

    def phase_2b(self, state, a, _b_, _v_):
        if not state.msgs["2a"][_b_][_v_]:
            return False, state
        if not (_b_ >= state.maxBal[a]):
            return False, state
        dest = State(state)
        dest.maxBal[a] = _b_
        dest.maxVBal[a] = _b_
        dest.maxVal[a] = _v_
        dest.msgs["2b"][a][_b_][_v_] = True
        return True, dest

    def forwardReach(self):
        q = []
        init_state = State()
        q.append(init_state)
        print("adding init")

        count = 0
        while len(q) != 0:
            count += 1
            curr = q.pop()
            if curr not in self.R:
                print("curr: \n%s" % curr.str())
                self.R.add(curr)
                for b in range(numB):
                        updated, dest = self.phase_1a(curr, b)
                        if updated:
                            if dest not in self.R:
                                q.append(dest)
                                print("\tstep: phase_1a(B%d)" % b)
                for a in range(numA):
                    for _b_ in range(numB):
                        updated, dest = self.phase_1b(curr, a, _b_)
                        if updated and (dest not in self.R):
                            q.append(dest)
                            print("\tstep: phase_1b(A%d, _B%d_)" % (a, _b_))
                for b in range(numB):
                    for v in range(numV):
                        updated, dest = self.phase_2a(curr, b, v)
                        if updated and (dest not in self.R):
                            q.append(dest)
                            print("\tstep: phase_2a(B%d, V%d)" % (b, v))
                for a in range(numA):
                    for _b_ in range(numB):
                        for _v_ in range(numV):
                            updated, dest = self.phase_2b(curr, a, _b_, _v_)
                            if updated and (dest not in self.R):
                                q.append(dest)
                                print("\tstep: phase_2b(A%d, _B%d_, _V%d_)" % (a, _b_, _v_))

        self.print_R_espresso()
        print("#R = %d" % len(self.R))

    def print_R_espresso(self):
        global outF, outFile
        outFile = "paxos_%dA_%dB_%dV.pla" % (numA, numB, numV)
        outF = open("pla/"+outFile, 'w')

        fprint("# paxos: %d acceptors, %d values, %d ballots" % (numA, numV, numB))
        fprint(".i %d" % (numA * (2*(numB+1)+(numV+1)) + numB + numA*numB*(numB+1)*(numV+1) + numB*numV + numA*numB*numV))
        fprint(".o 1")
        fprint(".ilb %s" % next(iter(self.R)).str_header_espresso())
        fprint(".ob notR")
        fprint(".phase 0")
        for state in self.R:
            fprint(state.str_espresso() + " 1")
        fprint(".e")
        fprint("")


def main():
    s = System()
    print("OK")


if __name__ == "__main__":
    main()
