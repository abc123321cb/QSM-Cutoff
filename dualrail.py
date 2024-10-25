from typing import Dict,List
from pysat.card import ITotalizer 
from protocol import Protocol

class DualRailNegation():
    def __init__(self, protocol : Protocol) -> None:
        self.clauses    : List[List[int]] = [] 
        self._totalizer : ITotalizer
        self._atom_num  : int = protocol.atom_num 
        self._atom_id2vars : Dict[int, List[int]] = {}

        self._encode(protocol)
        self._set_totalizer()

    def _set_dualrail_vars(self, id: int) -> None:
        self._atom_id2vars[id] = [id*2+2, id*2+1]
        
    def _get_pos_var(self, id: int) -> int:
        return self._atom_id2vars[id][1]

    def _get_neg_var(self, id: int) -> int:
        return self._atom_id2vars[id][0]

    def _encode(self, protocol : Protocol) -> None:
        for atom_id in range(self._atom_num):
            self._set_dualrail_vars(atom_id) 
            pvar = self._get_pos_var(atom_id)
            nvar = self._get_neg_var(atom_id)
            self.clauses.append([-1*pvar, -1*nvar]) # (~pvar + ~nvar)

        for state in protocol.quotient_reachable_states: # use quotient reachable states to prevent excessive redudant orbits
            clause = []
            for (atom_id, value) in enumerate(state):
                if value == '0':
                    clause.append(self._get_pos_var(atom_id))
                elif value == '1':
                    clause.append(self._get_neg_var(atom_id))
            self.clauses.append(clause)

    def _set_totalizer(self) -> None:
        max_var = 2 * self._atom_num
        literals = list(range(1,max_var+1))
        self._totalizer = ITotalizer(lits=literals, ubound=self._atom_num, top_id=max_var)
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
        values = ['-']* self._atom_num
        for atom_id in range(self._atom_num):
            if self._get_pos_var(atom_id) in sat_model:
                values[atom_id] = '1'
            elif self._get_neg_var(atom_id) in sat_model:
                values[atom_id] = '0'
        return values