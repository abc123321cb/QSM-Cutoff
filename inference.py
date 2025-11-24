# This code is doing unessary work so we can print all enumarations it needs to be fixed
# if your getting errors here make sure you have pyeda installed
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
from qinference import _nnf_push_not


# the list should be turned into a set because order does not matter in a clause
# dnf is not implemented yet

class Inference:
    def __init__(self, orbit: PrimeOrbit, options: QrmOptions, protocol: Protocol, is_dnf: bool):
        self.orbit   = orbit
        self.options = options
        self.protocol = protocol
        self.is_dnf  = is_dnf
        self.forall_clauses: List[QFormula] = []


    def get_qclause(self):
        self.enumerate()
        if self.is_dnf:
            return self._get_dnf_qclause()
        else:
            return self._get_cnf_qclause()

    def enumerate(self):
        # Enumeration logic for quantifier inference
        result = []
        sizes = self.options.sizes # dictionary of sort name to size
        total_results: List[List[tuple]] = []
        valid_results: list[List[int]] = [] # just contains valid equality functions
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
                if valid and self.get_e(mapped) not in valid_sort_results:
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
                body += str(results) + "\n"
            vprint(self.options, body, 2)

            ivy_forall = self.minimize_over_partitions(size, sort_size, valid_sort_results)
            # store the minimized forall constraint so it can be combined into the final qclause
            self.forall_clauses.append(ivy_forall)
            vprint(self.options, "Minimized equality functions:", 2, ending="\n")
            vprint(self.options, ivy_forall, 2)
            result.append(ivy_forall)

        return result

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

    def pair_index_map(self,n):
        """
        Return a list of (i, j) pairs in the same order
        you use in your boolean vectors.
        """
        pairs = []
        for i in range(n):
            for j in range(i + 1, n):
                pairs.append((i, j))
        return pairs

    def is_valid_partition_vector(self,vec, n):
        """
        vec: list/tuple of booleans for all pairs (i < j)
        n:   number of elements being partitioned

        Returns True iff vec is a valid partition vector
        """
        pairs = self.pair_index_map(n)

        # Disjoint set (union find)
        parent = list(range(n))

        def find(x):
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x

        def union(a, b):
            ra, rb = find(a), find(b)
            if ra != rb:
                parent[rb] = ra

        for bit, (i, j) in zip(vec, pairs):
            if bit:
                union(i, j)

        for bit, (i, j) in zip(vec, pairs):
            same_block = (find(i) == find(j))
            if same_block and not bit:
                return False

        return True

    def minimize_over_partitions(self, sort_name, n, good_partitions):
        m = n * (n - 1) // 2
        E = ttvars('e', m)

        good_set = {tuple(int(b) for b in vec) for vec in good_partitions}
        table_entries = []

        for bits in product([0, 1], repeat=m):
            if bits in good_set:
                table_entries.append('1')
            elif not self.is_valid_partition_vector(bits, n):
                table_entries.append('-')
            else:
                table_entries.append('0')

        tt = truthtable(E, ''.join(table_entries))
        f_min, = espresso_tts(tt)

        # Translate to ForAll over node0,node1,...
        return self._pyeda_to_ivy_forall(sort_name, n, f_min, E)


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
        # Build an OR of negated per-prime quantified clauses for the orbit,
        # and conjoin with any stored forall constraints collected during enumeration.
        
        negated_primes = []
        primes = list(getattr(self.orbit, 'suborbit_repr_primes', []) or [])
        if not primes:
            # fallback to repr_prime or orbit.primes
            p = getattr(self.orbit, 'repr_prime', None)
            if p is not None:
                primes = [p]
            else:
                primes = list(getattr(self.orbit, 'primes', []))

        # helper to build quantified formula for a single prime (like before)
        def build_for_prime(prime: Prime):
            terms = self.prime_to_qterms(prime, use_qvars=False)

            # collect argument names
            pattern = re.compile(r'([a-zA-Z_][a-zA-Z0-9_]*)\(([^()]*)\)')
            unique_names: list[str] = []
            seen: set[str] = set()
            for lit in prime.to_list():
                s = lit.strip()
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
                    if tok and tok not in seen:
                        seen.add(tok)
                        unique_names.append(tok)

            # build variables and substitution map
            const_name_to_ast: dict[str, object] = {}
            for atom in self.protocol.state_atoms_fmla:
                for c in ilu.used_constants_ast(atom):
                    cname = str(c)
                    if cname in seen and cname not in const_name_to_ast:
                        const_name_to_ast[cname] = c

            var_list = []
            const_ast_to_var: dict[object, object] = {}
            sort_counters: dict[str, int] = {}
            for name in unique_names:
                const_ast = const_name_to_ast.get(name)
                sort_obj = None
                sort_name = None
                if const_ast is not None:
                    try:
                        sort_obj = getattr(const_ast, 'sort', None)
                    except Exception:
                        sort_obj = None
                if sort_obj is None:
                    for sid, consts in enumerate(self.protocol.sort_constants):
                        if name in consts:
                            sort_name = self.protocol.sorts[sid]
                            break
                else:
                    sort_name = getattr(sort_obj, 'name', None)
                if sort_name is None:
                    sort_name = 'X'
                try:
                    sort = il.find_sort(sort_name)
                except Exception:
                    sort = il.UninterpretedSort(sort_name)
                    try:
                        il.add_sort(sort)
                    except Exception:
                        sort = il.find_sort(sort_name)
                idx = sort_counters.get(sort_name, 0)
                sort_counters[sort_name] = idx + 1
                vname = f"{sort_name.capitalize()}{idx+1}"
                v = il.Variable(vname, sort)
                var_list.append(v)
                if const_ast is not None:
                    const_ast_to_var[const_ast] = v

            if len(const_ast_to_var) == 0:
                terms_substituted = terms
            else:
                terms_substituted = []
                for t in terms:
                    try:
                        terms_substituted.append(il.substitute(t, const_ast_to_var))
                    except Exception:
                        terms_substituted.append(t)

            body = il.And(*terms_substituted) if len(terms_substituted) > 0 else il.And()
            return il.ForAll(var_list, body) if var_list else body

        # Merge stored forall_clauses (from enumerate) into a single forall
        def get_vars_and_body(fmla):
            vars_ = getattr(fmla, 'variables', None)
            if vars_ is None:
                vars_ = getattr(fmla, 'vars', ())
            body_ = getattr(fmla, 'body', None)
            if body_ is None:
                body_ = getattr(fmla, 'formula', None)
            if body_ is None:
                body_ = fmla
            return list(vars_) if vars_ is not None else [], body_

        merged_forall_vars = []
        merged_forall_body = il.Or()
        if getattr(self, 'forall_clauses', None):
            # sequentially merge and alpha-avoid to prevent name clashes
            first = True
            for fc in self.forall_clauses:
                if first:
                    vlist, body = get_vars_and_body(fc)
                    merged_forall_vars = list(vlist)
                    merged_forall_body = body
                    first = False
                else:
                    # rename fc to avoid clashing with merged vars
                    fc_ren = il.alpha_avoid(fc, merged_forall_vars)
                    vlist, body = get_vars_and_body(fc_ren)
                    merged_forall_vars += list(vlist)
                    merged_forall_body = il.Or(merged_forall_body, body)

        # Now process primes, renaming each against the merged_forall_vars and previously used prime vars
        used_vars = list(merged_forall_vars)
        negated_bodies = []
        all_prime_vars = []
        for p in primes:
            f_p = build_for_prime(p)
            # rename to avoid colliding with used_vars
            if used_vars:
                try:
                    f_p = il.alpha_avoid(f_p, used_vars)
                except Exception:
                    pass
            vlist, body = get_vars_and_body(f_p)
            # negate only the body (not the forall) and push the negation inside
            try:
                pushed = _nnf_push_not(il.Not(body))
            except Exception:
                pushed = il.Not(body)
            negated_bodies.append(pushed)
            used_vars += list(vlist)
            all_prime_vars += list(vlist)

        # Build final body: merged_forall_body AND (OR of negated prime bodies)
        or_part = il.Or(*negated_bodies) if negated_bodies else il.Or()
        final_body = il.And(merged_forall_body, or_part)

        # Build a single ForAll quantifying over merged_forall_vars + all_prime_vars
        total_vars = list(merged_forall_vars) + list(all_prime_vars)
        if total_vars:
            return il.ForAll(total_vars, final_body)
        else:
            return final_body

    def _get_dnf_qclause(self):
        # DNF quantifier inference logic
        vprint(self.options,"DNF is unsupported CNF will be used", 1)
        return self._get_cnf_qclause()  # Placeholder
    

    def _pyeda_to_ivy_forall(self, sort_name: str, n: int, f_min, E):
        """
        Convert the minimized PyEDA expression `f_min` over equality bits E
        into an Ivy formula of the form

            forall N1, ..., Nn. <boolean combination of N_i = N_j>

        The bits are:
            E[k]  <->  (N_i = N_j)
        in the order given by self.pair_index_map(n).

        `f_min` is the DNF expression returned by espresso_tts(tt).
        """
        try:
            sort = il.find_sort(sort_name)
        except Exception:
            # If the sort is not known yet, create it as uninterpreted
            sort = il.UninterpretedSort(sort_name)
            try:
                il.add_sort(sort)
            except Exception:
                # If someone else added it concurrently, just re-find it
                sort = il.find_sort(sort_name)

        # Universally quantified Ivy variables: N1, N2, ..., Nn
        xs = [il.Variable(f"{sort_name.capitalize()}{i+1}", sort) for i in range(n)]

        # Pairs (i, j) with i < j, in the same order as bits in E
        pairs = self.pair_index_map(n)  # length m = n*(n-1)//2

        # 2. Build maps from PyEDA inputs to bit indices

        # E was created as: E = ttvars('e', m)
        # Each element has .names, .indices, .uniqid
        uniqid_to_idx: dict[int, int] = {}
        name_idx_to_idx: dict[tuple[tuple[str, ...], tuple[int, ...]], int] = {}

        for k, v in enumerate(E):
            names = getattr(v, "names", None)
            indices = getattr(v, "indices", None)
            uniqid = getattr(v, "uniqid", None)

            if uniqid is not None:
                uniqid_to_idx[uniqid] = k
            if names is not None and indices is not None:
                key = (tuple(names), tuple(indices))
                name_idx_to_idx[key] = k

        # 3. Work on DNF and get its AST
        #
        # espresso_tts already returns a DNF expression, but to be safe:
        f_dnf = f_min.to_dnf()
        ast = f_dnf.to_ast()

        # 4. AST helpers

        def lit_from_var_ast(names, indices, positive=True):
            """Handle old-style ('var', names, indices) [+ optional 'not']."""
            key = (tuple(names), tuple(indices))
            if key not in name_idx_to_idx:
                raise KeyError(f"Unknown PyEDA variable {names}[{indices}] in minimized expression")

            k = name_idx_to_idx[key]
            i, j = pairs[k]
            atom = il.Equals(xs[i], xs[j])
            return atom if positive else il.Not(atom)

        def lit_from_lit_ast(u):
            """Handle new-style ('lit', uniqid). Sign encodes complement."""
            # u > 0  -> positive literal
            # u < 0  -> complement
            positive = (u > 0)
            base_uid = abs(u)

            if base_uid not in uniqid_to_idx:
                raise KeyError(f"Unknown uniqid {u} in minimized expression")

            k = uniqid_to_idx[base_uid]
            i, j = pairs[k]
            atom = il.Equals(xs[i], xs[j])
            return atom if positive else il.Not(atom)

        def ast_to_ivy(node):
            """
            Recursively convert a PyEDA AST into an Ivy term.

            AST forms we care about:

              ('const', 0|1)
              ('var', names, indices)           [old expr versions]
              ('lit', uniqid)                   [new expr versions]
              ('not', sub_ast)
              ('or', sub1, sub2, ...)
              ('and', sub1, sub2, ...)
            """
            if not isinstance(node, tuple) or not node:
                raise TypeError(f"Unexpected AST node: {node!r}")

            tag = node[0]

            # constants
            if tag == "const":
                val = bool(node[1])
                # In Ivy, empty And is True, empty Or is False
                return il.And() if val else il.Or()

            # variable / literal leaf
            if tag == "var":
                # old representation: ('var', names, indices)
                _, names, indices = node
                return lit_from_var_ast(names, indices, positive=True)

            if tag == "lit":
                # new representation: ('lit', uniqid)
                _, u = node
                return lit_from_lit_ast(u)

            # unary not
            if tag == "not":
                # Typically wraps a single literal in older ASTs
                sub = ast_to_ivy(node[1])
                return il.Not(sub)

            # N-ary or / and
            if tag == "or":
                return il.Or(*(ast_to_ivy(sub) for sub in node[1:]))

            if tag == "and":
                return il.And(*(ast_to_ivy(sub) for sub in node[1:]))

            # Anything else would be unexpected for a DNF from espresso_tts
            raise ValueError(f"Unexpected AST operator '{tag}' in minimized expression: {node!r}")

        body = ast_to_ivy(ast)

        # 5. Wrap with universal quantifiers
        return il.ForAll(xs, body)
    
    def prime_to_qterms(self, prime: Prime, tran_sys=None, use_qvars=False):
        """
        If use_qvars is False: returns the simple IL terms (like get_terms)
        -> get_terms(tran_sys, atoms, prime) (tran_sys may be None for get_terms)
        If use_qvars is True: returns qterms (constants replaced by quantifier vars) using get_qterms,
        which requires tran_sys (TransitionSystem).
        """
        atoms = self.protocol.state_atoms_fmla
        if use_qvars:
            if tran_sys is None:
                raise ValueError("tran_sys required when use_qvars=True")
            return get_qterms(tran_sys, atoms, prime)
        else:
            # get_terms signature is (tran_sys, atoms, prime) but tran_sys is unused for this simple conversion
            return get_terms(None, atoms, prime)

