from typing import Dict,List
from pysat.card import ITotalizer 
from protocol import Protocol
from util import QrmOptions, PrimeGen

class DualRailNegation():
    def __init__(self, options : QrmOptions, protocol : Protocol) -> None:
        self.options = options
        self.clauses    : List[List[int]] = [] 
        self._totalizer : ITotalizer
        self._state_atom_num  : int = protocol.state_atom_num 
        self._atom_id2vars : Dict[int, List[int]]  = {}
        self._var2clause_id : Dict[int, List[int]] = {}
        self._encode(protocol)
        if self.options.prime_gen == PrimeGen.ilp or self.options.prime_gen == PrimeGen.binary:
            self._set_totalizer()
        elif self.options.prime_gen == PrimeGen.enumerate: 
            # Implementing the paper "Enumerating Prime Implicants of Propositional Formulae in Conjunctive Normal Form"
            self._encode_M()

    def _set_dualrail_vars(self, atom_id: int) -> None:
        self._atom_id2vars[atom_id] = [atom_id*2+2, atom_id*2+1]
        
    def _get_pos_var(self, atom_id: int) -> int:
        return self._atom_id2vars[atom_id][1]

    def _get_neg_var(self, atom_id: int) -> int:
        return self._atom_id2vars[atom_id][0]

    def _encode(self, protocol : Protocol) -> None:
        for atom_id in range(self._state_atom_num):
            self._set_dualrail_vars(atom_id) 
            pvar = self._get_pos_var(atom_id)
            nvar = self._get_neg_var(atom_id)
            self.clauses.append([-1*pvar, -1*nvar]) # (~pvar + ~nvar)
            if self.options.prime_gen == PrimeGen.enumerate:
                self._var2clause_id[pvar] = []
                self._var2clause_id[nvar] = []

        for state in protocol.quotient_reachable_states: # use quotient reachable states to prevent excessive redudant orbits
            clause = []
            for (atom_id, value) in enumerate(state):
                if value == '0':
                    pos_var = self._get_pos_var(atom_id)
                    clause.append(pos_var)
                    if self.options.prime_gen == PrimeGen.enumerate:
                        self._var2clause_id[pos_var].append(len(self.clauses))
                elif value == '1':
                    neg_var = self._get_neg_var(atom_id)
                    clause.append(neg_var)
                    if self.options.prime_gen == PrimeGen.enumerate:
                        self._var2clause_id[neg_var].append(len(self.clauses))
            self.clauses.append(clause)

    def _encode_M(self):
        tseitin_var = self._state_atom_num*2+1
        for var, clause_ids in self._var2clause_id.items():
            mclause = []
            for cid in clause_ids:
                clause = self.clauses[cid]
                red_clause = list(filter(lambda x: x != var, clause))
                # t <-> (red_clause)
                for lit in red_clause:
                    self.clauses.append([-1*lit, tseitin_var])      # ~red_clause + t
                self.clauses.append(red_clause + [-1*tseitin_var])  # ~t + red_clause
                mclause.append(-1*tseitin_var)
                tseitin_var += 1
            # mclause: var -> ~(t1t2 ....) = (~var + ~t1 + ~t2 ....)
            mclause.append(-1*var)  
            self.clauses.append(mclause)

    def _set_totalizer(self) -> None:
        max_var = 2 * self._state_atom_num
        literals = list(range(1,max_var+1)) # summing the literals 1,2,....max_var
        self._totalizer = ITotalizer(lits=literals, ubound=self._state_atom_num, top_id=max_var)
        self.clauses.extend(self._totalizer.cnf.clauses)

    def assume(self, ubound: int) -> List[int]:
        return [-1*self._totalizer.rhs[ubound]]

    def block(self, values : List[str]) -> List[int]:
        var = 0
        block_clause = []
        for (atom_id, value) in enumerate(values):
            if value == '1':
                var = self._get_pos_var(atom_id)
                block_clause.append(-1*var)
            elif value == '0':
                var = self._get_neg_var(atom_id)
                block_clause.append(-1*var)
        return block_clause

    def single_rail(self, sat_model) -> List[str]:
        values = ['-']* self._state_atom_num
        for atom_id in range(self._state_atom_num):
            if self._get_pos_var(atom_id) in sat_model:
                values[atom_id] = '1'
            elif self._get_neg_var(atom_id) in sat_model:
                values[atom_id] = '0'
        return values