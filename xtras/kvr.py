#!/usr/bin/python2.7

from __future__ import print_function
import copy
from itertools import product

numN = 1
numK = 1
numV = 1
numS = 1

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
        self.ack_msg = copy.deepcopy(state.ack_msg)
        self.seqnum_sent = copy.deepcopy(state.seqnum_sent)
        self.seqnum_recvd = copy.deepcopy(state.seqnum_recvd)
        self.unacked = copy.deepcopy(state.unacked)

    def __key(self):
        return (
            str(self.table),
            str(self.owner),
            str(self.transfer_msg),
            str(self.ack_msg),
            str(self.seqnum_sent),
            str(self.seqnum_recvd),
            str(self.unacked)
        )

    def __hash__(self):
        return hash(self.__key())

    def __eq__(self, other):
        return (self.__class__ == other.__class__
            and self.table == other.table
            and self.owner == other.owner
            and self.transfer_msg == other.transfer_msg
            and self.ack_msg == other.ack_msg
            and self.seqnum_sent == other.seqnum_sent
            and self.seqnum_recvd == other.seqnum_recvd
            and self.unacked == other.unacked
        )

    def reset(self, owner_list):
        self.table = [[[False for v in range(numV)] for k in range(numK)] for n in range(numN)]
        self.owner = [[False for k in range(numK)] for n in range(numN)]
        self.transfer_msg = [[[[[False for s in range(numS)] for v in range(numV)] for k in range(numK)] for n2 in range(numN)] for n1 in range(numN)]
        self.ack_msg = [[[False for s in range(numS)] for n2 in range(numN)] for n1 in range(numN)]
        self.seqnum_sent = [[False for s in range(numS)] for n in range(numN)]
        self.seqnum_recvd = [[[False for s in range(numS)] for n2 in range(numN)] for n1 in range(numN)]
        self.unacked = [[[[[False for s in range(numS)] for v in range(numV)] for k in range(numK)] for n2 in range(numN)] for n1 in range(numN)]
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
        for n1 in range(numN):
            for n2 in range(numN):
                for k in range(numK):
                    for v in range(numV):
                        for s in range(numS):
                            if self.transfer_msg[n1][n2][k][v][s]:
                                res += "(N%d, N%d, K%d, V%d, S%d)  " % (n1, n2, k, v, s)
        res += "\n"
        res += prefix + "ack_msg:       "
        for n1 in range(numN):
            for n2 in range(numN):
                for s in range(numS):
                    if self.ack_msg[n1][n2][s]:
                        res += "(N%d, N%d, S%d)  " % (n1, n2, s)
        res += "\n"
        res += prefix + "seqnum_sent:   "
        for n in range(numN):
            for s in range(numS):
                if self.seqnum_sent[n][s]:
                    res += "(N%d, S%d)  " % (n, s)
        res += "\n"
        res += prefix + "seqnum_recvd:  "
        for n1 in range(numN):
            for n2 in range(numN):
                for s in range(numS):
                    if self.seqnum_recvd[n1][n2][s]:
                        res += "(N%d, N%d, S%d)  " % (n1, n2, s)
        res += "\n"
        res += prefix + "unacked:       "
        for n1 in range(numN):
            for n2 in range(numN):
                for k in range(numK):
                    for v in range(numV):
                        for s in range(numS):
                            if self.unacked[n1][n2][k][v][s]:
                                res += "(N%d, N%d, K%d, V%d, S%d)  " % (n1, n2, k, v, s)
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
                res += "owner(N%d, K%d) " % (n, k)
        res += " "
        for n1 in range(numN):
            for n2 in range(numN):
                for k in range(numK):
                    for v in range(numV):
                        for s in range(numS):
                            res += "transfer_msg(N%d,N%d,K%d,V%d,S%d) " % (n1, n2, k, v, s)
        res += " "
        for n1 in range(numN):
            for n2 in range(numN):
                for s in range(numS):
                    res += "ack_msg(N%d,N%d,S%d) " % (n1, n2, s)
        res += " "
        for n in range(numN):
            for s in range(numS):
                res += "seqnum_sent(N%d,S%d) " % (n, s)
        res += " "
        for n1 in range(numN):
            for n2 in range(numN):
                for s in range(numS):
                    res += "seqnum_recvd(N%d,N%d,S%d) " % (n1, n2, s)
        res += " "
        for n1 in range(numN):
            for n2 in range(numN):
                for k in range(numK):
                    for v in range(numV):
                        for s in range(numS):
                            res += "unacked(N%d,N%d,K%d,V%d,S%d) " % (n1, n2, k, v, s)
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
        for n1 in range(numN):
            for n2 in range(numN):
                for k in range(numK):
                    for v in range(numV):
                        for s in range(numS):
                            res += "1" if self.transfer_msg[n1][n2][k][v][s] else "0"
        res += " "
        for n1 in range(numN):
            for n2 in range(numN):
                for s in range(numS):
                    res += "1" if self.ack_msg[n1][n2][s] else "0"
        res += " "
        for n in range(numN):
            for s in range(numS):
                res += "1" if self.seqnum_sent[n][s] else "0"
        res += " "
        for n1 in range(numN):
            for n2 in range(numN):
                for s in range(numS):
                    res += "1" if self.seqnum_recvd[n1][n2][s] else "0"
        res += " "
        for n1 in range(numN):
            for n2 in range(numN):
                for k in range(numK):
                    for v in range(numV):
                        for s in range(numS):
                            res += "1" if self.unacked[n1][n2][k][v][s] else "0"
        res += " "
        return res


class System():
    def __init__(self):
        self.R = set()
        self.forwardReach()

    def put(self, state, n, k, v):
        if not state.owner[n][k]:
            return False, state
        dest = State(state)
        for v_all in range(numV):
            dest.table[n][k][v_all] = False
        dest.table[n][k][v] = True
        return True, dest

    def reshard(self, state, n1, n2, k, v, s):
        if not state.table[n1][k][v] or state.seqnum_sent[n1][s]:
            return False, state
        dest = State(state)
        dest.seqnum_sent[n1][s] = True
        dest.table[n1][k][v] = False
        dest.owner[n1][k] = False
        dest.transfer_msg[n1][n2][k][v][s] = True
        dest.unacked[n1][n2][k][v][s] = True
        return True, dest

    def drop_transfer_msg(self, state, n1, n2, k, v, s):
        if not state.transfer_msg[n1][n2][k][v][s]:
            return False, state
        dest = State(state)
        dest.transfer_msg[n1][n2][k][v][s] = False
        return True, dest

    def retransmit(self, state, n1, n2, k, v, s):
        if not state.unacked[n1][n2][k][v][s]:
            return False, state
        dest = State(state)
        dest.transfer_msg[n1][n2][k][v][s] = True
        return True, dest

    def recv_transfer_msg(self, state, n1, n2, k, v, s):
        if not state.transfer_msg[n1][n2][k][v][s] or state.seqnum_recvd[n2][n1][s]:
            return False, state
        dest = State(state)
        dest.seqnum_recvd[n2][n1][s] = True
        dest.table[n2][k][v] = True
        dest.owner[n2][k] = True
        return True, dest

    def send_ack(self, state, n1, n2, k, v, s):
        if not state.transfer_msg[n1][n2][k][v][s] or not state.seqnum_recvd[n2][n1][s]:
            return False, state
        dest = State(state)
        dest.ack_msg[n1][n2][s] = True
        return True, dest

    def drop_ack_msg(self, state, n1, n2, s):
        if not state.ack_msg[n1][n2][s]:
            return False, state
        dest = State(state)
        dest.ack_msg[n1][n2][s] = False
        return True, dest

    def recv_ack_msg(self, state, n1, n2, s):
        if not state.ack_msg[n1][n2][s]:
            return False, state
        dest = State(state)
        for k_all in range(numK):
            for v_all in range(numV):
                dest.unacked[n1][n2][k_all][v_all][s] = False
        return True, dest

    def forwardReach(self):
        q = []
        for owner_list in list(product([None] + range(numN), repeat=numK)):
            q.append(State(owner_list))
        print("adding init")

        count = 0
        while len(q) != 0:
            count += 1
            curr = q.pop()
            if curr not in self.R:
                print("curr(%d, %d): \n%s" % (len(self.R), len(q), curr.str()))
                self.R.add(curr)
                for n in range(numN):
                    for k in range(numK):
                        for v in range(numV):
                            updated, dest = self.put(curr, n, k, v)
                            if updated and (dest not in self.R):
                                q.append(dest)
                                print("\tstep: put(N%d, K%d, V%d)" % (n, k, v))
                for n1 in range(numN):
                    for n2 in range(numN):
                        for k in range(numK):
                            for v in range(numV):
                                for s in range(numS):
                                    updated, dest = self.reshard(curr, n1, n2, k, v, s)
                                    if updated and (dest not in self.R):
                                        q.append(dest)
                                        print("\tstep: reshard(N%d, N%d, K%d, V%d, S%d)" % (n1, n2, k, v, s))
                for n1 in range(numN):
                    for n2 in range(numN):
                        for k in range(numK):
                            for v in range(numV):
                                for s in range(numS):
                                    updated, dest = self.drop_transfer_msg(curr, n1, n2, k, v, s)
                                    if updated and (dest not in self.R):
                                        q.append(dest)
                                        print("\tstep: drop_transfer_msg(N%d, N%d, K%d, V%d, S%d)" % (n1, n2, k, v, s))
                for n1 in range(numN):
                    for n2 in range(numN):
                        for k in range(numK):
                            for v in range(numV):
                                for s in range(numS):
                                    updated, dest = self.retransmit(curr, n1, n2, k, v, s)
                                    if updated and (dest not in self.R):
                                        q.append(dest)
                                        print("\tstep: retransmit(N%d, N%d, K%d, V%d, S%d)" % (n1, n2, k, v, s))
                for n1 in range(numN):
                    for n2 in range(numN):
                        for k in range(numK):
                            for v in range(numV):
                                for s in range(numS):
                                    updated, dest = self.recv_transfer_msg(curr, n1, n2, k, v, s)
                                    if updated and (dest not in self.R):
                                        q.append(dest)
                                        print("\tstep: recv_transfer_msg(N%d, N%d, K%d, V%d, S%d)" % (n1, n2, k, v, s))
                for n1 in range(numN):
                    for n2 in range(numN):
                        for k in range(numK):
                            for v in range(numV):
                                for s in range(numS):
                                    updated, dest = self.send_ack(curr, n1, n2, k, v, s)
                                    if updated and (dest not in self.R):
                                        q.append(dest)
                                        print("\tstep: send_ack(N%d, N%d, K%d, V%d, S%d)" % (n1, n2, k, v, s))
                for n1 in range(numN):
                    for n2 in range(numN):
                        for s in range(numS):
                            updated, dest = self.drop_ack_msg(curr, n1, n2, s)
                            if updated and (dest not in self.R):
                                q.append(dest)
                                print("\tstep: drop_ack_msg(N%d, N%d, S%d)" % (n1, n2, s))
                for n1 in range(numN):
                    for n2 in range(numN):
                        for s in range(numS):
                            updated, dest = self.recv_ack_msg(curr, n1, n2, s)
                            if updated and (dest not in self.R):
                                q.append(dest)
                                print("\tstep: recv_ack_msg(N%d, N%d, S%d)" % (n1, n2, s))

        self.print_R_espresso()
        print("#R = %d" % len(self.R))

    def print_R_espresso(self):
        global outF, outFile
        outFile = "kvr.pla"
        outF = open(outFile, 'w')

        fprint("# kvr_%dN_%dK_%dV_%dS" % (numN, numK, numV, numS))
        fprint(".i %d" % (numN*numK*numV + numN*numK + 2*numN*numN*numK*numV*numS + 2*numN*numN*numS + numN*numS))
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
