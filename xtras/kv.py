#!/usr/bin/python2.7

from __future__ import print_function
import copy
from itertools import product

lost_keys = True

numN = 2
numK = 2
numV = 2

outFile = "out.pla"
outF = None
def fprint(s):
    global outF
    outF.write(s + "\n")


class State():
    def __init__(self, initializer):
        if isinstance(initializer, State):
            self.copy(initializer)
        else:
            self.reset(initializer)

    def copy(self, state):
        self.table = copy.deepcopy(state.table)
        self.owner = copy.deepcopy(state.owner)
        self.transfer_msg = copy.deepcopy(state.transfer_msg)

    def __key(self):
        return (str(self.table), str(self.owner), str(self.transfer_msg))

    def __hash__(self):
        return hash(self.__key())

    def __eq__(self, other):
        return (self.__class__ == other.__class__ and
                self.table == other.table and
                self.owner == other.owner and
                self.transfer_msg == other.transfer_msg)

    def reset(self, owner_list):
        self.table = [[[False for v in range(numV)] for k in range(numK)] for n in range(numN)]
        self.owner = [[False for k in range(numK)] for n in range(numN)]
        self.transfer_msg = [[[False for v in range(numV)] for k in range(numK)] for n in range(numN)]
        for k in range(numK):
            if owner_list[k] is not None:
                self.owner[owner_list[k]][k] = True

    def str(self, prefix="\t"):
        res = prefix + "table:         "
        for n in range(numN):
            for k in range(numK):
                for v in range(numV):
                    if self.table[n][k][v]:
                        res += "(N%d, K%d, V%d)  " % (n, k, v)
        res += "\n"
        res += prefix + "owner:         "
        for n in range(numN):
            for k in range(numK):
                if self.owner[n][k]:
                    res += "(N%d, K%d)  " % (n, k)
        res += "\n"
        res += prefix + "transfer_msg:  "
        for n in range(numN):
            for k in range(numK):
                for v in range(numV):
                    if self.transfer_msg[n][k][v]:
                        res += "(N%d, K%d, V%d)  " % (n, k, v)
        res += "\n"
        return res

    def str_header_espresso(self):
        res = ""
        for n in range(numN):
            for k in range(numK):
                for v in range(numV):
                    res += "table(N%d,K%d,V%d) " % (n, k, v)
        res += " "
        for n in range(numN):
            for k in range(numK):
                res += "owner(N%d,K%d) " % (n, k)
        res += " "
        for n in range(numN):
            for k in range(numK):
                for v in range(numV):
                    res += "transfer_msg(N%d,K%d,V%d) " % (n, k, v)
        res += " "
        return res

    def str_espresso(self):
        res = ""
        for n in range(numN):
            for k in range(numK):
                for v in range(numV):
                    res += "1" if self.table[n][k][v] else "0"
        res += " "
        for n in range(numN):
            for k in range(numK):
                res += "1" if self.owner[n][k] else "0"
        res += " "
        for n in range(numN):
            for k in range(numK):
                for v in range(numV):
                    res += "1" if self.transfer_msg[n][k][v] else "0"
        res += " "
        return res

class System():
    def __init__(self):
        self.R = set()
        self.forwardReach()

    def reshard(self, state, n1, n2, k, v):
        if not state.table[n1][k][v]:
            return False, state
        dest = State(state)
        dest.table[n1][k][v] = False
        dest.owner[n1][k] = False
        dest.transfer_msg[n2][k][v] = True
        return True, dest

    def recv_transfer_msg(self, state, n, k, v):
        if not state.transfer_msg[n][k][v]:
            return False, state
        dest = State(state)
        dest.transfer_msg[n][k][v] = False
        dest.table[n][k][v] = True
        dest.owner[n][k] = True
        return True, dest

    def put(self, state, n, k, v):
        if not state.owner[n][k]:
            return False, state
        dest = State(state)
        for v_all in range(numV):
            dest.table[n][k][v_all] = False
        dest.table[n][k][v] = True
        return True, dest

    def forwardReach(self):
        q = []
        possible_owners = ([None] + range(numN)) if lost_keys else range(numN)
        for owner_list in list(product(possible_owners, repeat=numK)):
            q.append(State(owner_list))
        print("adding init")

        count = 0
        while len(q) != 0:
            count += 1
            curr = q.pop()
            if curr not in self.R:
                print("curr: \n%s" % curr.str())
                self.R.add(curr)
                for n1 in range(numN):
                    for n2 in range(numN):
                        for k in range(numK):
                            for v in range(numV):
                                updated, dest = self.reshard(curr, n1, n2, k, v)
                                if updated and (dest not in self.R):
                                    q.append(dest)
                                    print("\tstep: reshard(N%d, N%d, K%d, V%d)" % (n1, n2, k, v))
                for n in range(numN):
                    for k in range(numK):
                        for v in range(numV):
                            updated, dest = self.recv_transfer_msg(curr, n, k, v)
                            if updated and (dest not in self.R):
                                q.append(dest)
                                print("\tstep: recv_transfer_msg(N%d, K%d, V%d)" % (n, k, v))
                for n in range(numN):
                    for k in range(numK):
                        for v in range(numV):
                            updated, dest = self.put(curr, n, k, v)
                            if updated and (dest not in self.R):
                                q.append(dest)
                                print("\tstep: put(N%d, K%d, V%d)" % (n, k, v))

        self.print_R_espresso()
        print("#R = %d" % len(self.R))

    def print_R_espresso(self):
        global outF, outFile
        outFile = "kv.pla"
        outF = open(outFile, 'w')

        fprint("# kv_%dN_%dK_%dV%s" % (numN, numK, numV, "" if lost_keys else "_nlk"))
        fprint(".i %d" % (numN * numK * (1 + 2* numV)))
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
