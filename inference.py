# This code is doing unessary work so we can print all enumarations
import math
from qformula import QFormula
from prime import *
from verbose import *
from protocol import Protocol
import re
from typing import Iterable, List, Sequence

# the list should be turned into a set because order does not matter in a clause
# dnf is not implemented yet

class Inference:
    def __init__(self, orbit: PrimeOrbit, options: QrmOptions, protocol: Protocol, is_dnf: bool):
        self.orbit   = orbit
        self.options = options
        self.protocol = protocol
        self.is_dnf  = is_dnf


    def get_qclause(self):
        self.enumerate()
        if self.is_dnf:
            return self._get_dnf_qclause()
        else:
            return self._get_cnf_qclause()

    def enumerate(self):
        # Enumeration logic for quantifier inference
        
        sizes = self.options.sizes # dictionary of sort name to size
        total_results: List[List[tuple]] = []
        valid_results: List[List[int]] = [] # just contains valid equality functions
        for size in sizes:
            sort_results: List[tuple] = []
            valid_sort_results: List[tuple] = []
            sort_size = sizes[size]
            sort_results.append((size, sort_size))
            num_sorts = -1
            p: Prime
            for prime in self.orbit.suborbit_repr_primes:
                i = self._get_quantifier_num(prime)
                if i > num_sorts:
                    num_sorts = i
                    p = prime
            vprint(self.options, "Using prime " + str(p.literals) + " with " + str(num_sorts) + " sorts.", 2)
            # we are working in base sizes[size]
            initial_clause = self.to_number_list(p.to_list())
            for i in range(int(math.pow(sort_size, sort_size))):
                mapped = []
                count = i
                initial_clause = self.to_number_list(p.to_list())
                for j in range(sort_size):
                    mapped.append(count % sort_size)
                    count = count // sort_size
                initial_clause = self._replace(initial_clause, mapped, size)
                valid = self._check_clause(initial_clause)
                sort_results.append((initial_clause, valid, self.get_e(mapped)))
                if valid:
                    valid_sort_results.append(self.get_e(mapped))

            total_results.append(sort_results)
            valid_results.append(valid_sort_results)

            vprint(self.options, "Valid equality functions found:", 2)
            header = ""
            for i in range(sort_size):
                for j in range(i+1, sort_size):
                    header += " E(" + str(i) + str(j) + ") "
            vprint(self.options, header, 2)
            body = ""
            for results in valid_sort_results:
                body += str(results) + " "
            vprint(self.options, body, 2)

            for results in total_results:
                self._print_chart(results)


    # get the equality functions for a given reordering
    def get_e(self, l: list[int]) -> list[bool]:
        r = []
        for i in range(len(l)):
            for j in range(i+1, len(l)):
                if l[i] == l[j]:
                    r.append(True)
                else:
                    r.append(False)
        return r

    def _print_chart(self, results: List[tuple]) -> None:
        # data in the tuple is (clause, is_valid, e)
        # the first tuple is (sort, size)
        vprint(self.options, "Enumeration results:", 3, ending="\n")
        vprint(self.options, "---------------------", 3)
        sort = results[0][0]
        size = results[0][1]
        header = ""
        for i in range(size):
            header += sort + str(i) + " "
        for i in range(size):
            for j in range(i+1, size):
                header += " E(" + str(i) + str(j) + ") "

        vprint(self.options, header, 3)

        for i in range(len(results) - 1):
            clause, is_valid, e = results[i + 1]
            line = ""
            temp = i
            for _ in range(size):
                line += " " + str(temp % size) + sort[::-1]
                temp = temp // size
            line = line[::-1]  # reverse the line

            line += " : " + f'{str(e)} : {str(self.to_string_list(clause))} : ({("VALID" if is_valid else "INVALID")})'
            vprint(self.options, line, 3, ending="\n")
        vprint(self.options, "\n", 3)



    def _swap(self,
        signed_ids: Iterable[int],
        const_a: str,
        const_b: str,
    ) -> List[int]:
        """
        Swap const_a and const_b inside all state atoms, then remap a 1-based signed index list.
        Example: [1, 2, -4, -6] -> [2, 1, -6, -4] after swapping where those atoms land.
        """
        # find the sort that contains both constants
        target_sort = None
        a_idx = b_idx = None
        for sort_id, consts in enumerate(self.protocol.sort_constants):
            if const_a in consts and const_b in consts:
                target_sort = sort_id
                a_idx = consts.index(const_a)
                b_idx = consts.index(const_b)
                break
        if target_sort is None:
            raise ValueError(f"Both {const_a} and {const_b} must be in the same sort")

        # build per-sort permutation
        permutation = []
        for sort_id, consts in enumerate(self.protocol.sort_constants):
            mapping = list(range(len(consts)))
            if sort_id == target_sort:
                mapping[a_idx], mapping[b_idx] = mapping[b_idx], mapping[a_idx]
            permutation.append(mapping)

        # atom reindex map f: old atom id -> new atom id under the swap (0-based)
        idx_map: List[int] = []
        for atom_id in range(self.protocol.state_atom_num):
            renamed = self.protocol._get_renamed_atom(permutation, atom_id)
            new_id = self.protocol.atom_Name2Id.get(renamed)
            if new_id is None or new_id >= self.protocol.state_atom_num:
                raise ValueError(f"Renamed atom not a state atom: {renamed}")
            idx_map.append(new_id)

        # apply f to each 1-based signed index, preserving sign
        out: List[int] = []
        for v in signed_ids:
            sign = 1 if v >= 0 else -1
            i0 = abs(v) - 1  # to 0-based
            if not (0 <= i0 < self.protocol.state_atom_num):
                raise IndexError(f"Index out of range: {v}")
            j0 = idx_map[i0]
            out.append(sign * (j0 + 1))  # back to 1-based
        return out

    def _replace(
        self,
        signed_ids: Iterable[int],
        mapper: Sequence[int],   # map[old_const_id] = new_const_id (0-based, within sort)
        sort_name: str,          # e.g., "node"
    ) -> List[int]:
        """
        Simultaneously replace constants in 'sort_name' according to 'mapper',
        then remap a 1-based signed atom-id list.

        Example:
        sort_constants['node'] == ['node0','node1','node2']
        mapper = [1,0,2]  means node0->node1, node1->node0, node2->node2
        mapper = [1,1,2]  means node0->node1, node1->node1, node2->node2
        """
        if sort_name is None or sort_name not in self.protocol.sort_Name2Id:
            raise ValueError(f"Unknown sort: {sort_name}")

        sort_id = self.protocol.sort_Name2Id[sort_name]
        s = len(self.protocol.sort_constants[sort_id])

        if len(mapper) != s:
            raise ValueError(f"mapper length {len(mapper)} != size of sort {sort_name} ({s})")
        if any(m < 0 or m >= s for m in mapper):
            raise ValueError(f"mapper entries must be in [0, {s})")

        # Build per-sort permutation: use 'mapper' for target sort, identity elsewhere
        permutation: List[List[int]] = []
        for sid, consts in enumerate(self.protocol.sort_constants):
            if sid == sort_id:
                permutation.append(list(mapper))
            else:
                permutation.append(list(range(len(consts))))

        # Atom reindex map: old state-atom id -> new id after applying the mapping
        idx_map: List[int] = []
        for atom_id in range(self.protocol.state_atom_num):
            renamed = self.protocol._get_renamed_atom(permutation, atom_id)
            new_id = self.protocol.atom_Name2Id.get(renamed)
            if new_id is None or new_id >= self.protocol.state_atom_num:
                raise ValueError(f"Renamed atom not a state atom: {renamed}")
            idx_map.append(new_id)

        # Remap each 1-based signed atom index, preserving sign
        out: List[int] = []
        for v in signed_ids:
            sign = 1 if v >= 0 else -1
            i0 = abs(v) - 1  # to 0-based
            if not (0 <= i0 < self.protocol.state_atom_num):
                raise IndexError(f"Index out of range: {v}")
            j0 = idx_map[i0]
            out.append(sign * (j0 + 1))  # back to 1-based
        return out


    def _check_clause(self, clause: List[int]) -> bool:
        # Check if the clause is valid under the protocol
        clause.sort()
        for i in self.orbit.primes:
            f = self.to_number_list(i.to_list())
            f.sort()
            if clause == f:
                return True
        return False

    def _get_quantifier_num(self, prime: Prime) -> int:
        # Determine the number of quantifiers needed for this prime.
        # We count the number of unique constant arguments that appear
        # in the prime's literals. Example: ['p(node1)', 'p(node0)'] -> 2
        pattern = re.compile(r'([a-zA-Z_][a-zA-Z0-9_]*)\(([^()]*)\)')

        uniques: set[str] = set()
        for lit in prime.to_list():
            s = lit.strip()
            # ignore leading negation
            if s.startswith('~'):
                s = s[1:].strip()
            m = pattern.search(s)
            if not m:
                continue
            args_text = m.group(2).strip()
            if not args_text:
                continue
            for tok in args_text.split(','):
                tok = tok.strip()
                if tok:
                    uniques.add(tok)

        return len(uniques)

    def to_string_list(self, signed_ids: Iterable[int]) -> List[str]:
        """Convert 1-based signed atom ids to ['p(node0)', '~q(node1)', ...] for printing."""
        out: List[str] = []
        for v in signed_ids:
            neg = v < 0
            i0 = abs(v) - 1  # 0-based
            if not (0 <= i0 < self.protocol.state_atom_num):
                raise IndexError(f"Index out of range: {v}")
            name = self.protocol.state_atoms[i0]
            out.append(("~" if neg else "") + name)
        out.sort()
        return out

    def to_number_list(self, literals: Iterable[str]) -> List[int]:
        """
        Convert to 1-based signed atom ids.
        """
        out: List[int] = []
        for s in literals:
            lit = s.strip()
            neg = lit.startswith("~")
            if neg:
                lit = lit[1:].strip()
            atom0 = self.protocol.atom_Name2Id.get(lit)
            if atom0 is None:
                raise ValueError(f"Unknown atom name: {s}")
            if atom0 >= self.protocol.state_atom_num:
                raise ValueError(f"Not a state atom: {s}")
            out.append((-1 if neg else 1) * (atom0 + 1))  # 1-based
        return out

    def _get_cnf_qclause(self):
        # CNF quantifier inference logic
        pass

    def _get_dnf_qclause(self):
        # DNF quantifier inference logic
        return self._get_cnf_qclause()  # Placeholder
    

    