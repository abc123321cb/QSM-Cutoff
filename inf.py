from qformula import QFormula
from prime import *
from verbose import *
from protocol import Protocol
import re
from typing import List
from itertools import permutations
from pyeda.inter import exprvar, truthtable
from pyeda.boolalg.minimization import espresso_tts
from ivy import ivy_logic as il
from ivy import ivy_logic_utils as ilu
from qinference import *

# To use this class first initilize it then call get_qclause to get a forall statement for a for_all statement
class Inference:
    
    def __init__(self, orbit: PrimeOrbit, options: QrmOptions, protocol: Protocol, is_dnf: bool):
        self.orbit   = orbit
        self.options = options
        self.protocol = protocol
        self.is_dnf  = is_dnf

        self.forall_clauses: List[QFormula] = []


    def get_qclause(self):
        restrictions = self.enumerate()
        qclause = self._get_cnf_qclause(restrictions)
        return {
            'qclause': qclause,
            'restrictions': restrictions,
            'orbit_literals': list(self.orbit.repr_prime.literals_list),
        }
    

    #expand the clause out so a orbit like this at size =2
    # ['e(node0)', 'h(node1)', '~l(node1)']
    # becomes
    # ['e(N0)', 'H(N1)', '~l(N2)']
    # we are making every spot get its own quantifier.
    # then take this table change it into equality checks so over e01e02e12 for this case.
    # We make all the non bell satifiable possiabities don't care so e01,e02,~e12 would be one because N0=N1 & N0=N2 -> N1=N2
    # Then we have to mark all the valid substutions from the orbit as true and the rest as false
    # run espresso_tts to get the combinations and negate to cover reach instead of ~reach
    # Note all functions here until _get_cnf_qclauses are for enumerate
    # RETURNS: something like And(e01 OR(e12 e02)) note it should always be a and on the outer layer
    def enumerate(self):
        clause = list(self.orbit.repr_prime.literals_list)
        if not clause:
            return il.And()

        # Makes the repr_prime become [(bool is_negated, string function name, list of sorts)]
        # so it turns ~l(node1) into (True, 'l', ['node1'])
        parsed_clause = [self._parse_literal(lit) for lit in clause]
        slot_sort_names = self._get_slot_sort_names(parsed_clause)
        slot_count = len(slot_sort_names)
        if slot_count <= 1:
            return il.And()

        pair_list = [
            (i, j)
            for i in range(slot_count - 1)
            for j in range(i + 1, slot_count)
            if slot_sort_names[i] == slot_sort_names[j]
        ]
        eq_vars = [f'e{i}{j}' for i, j in pair_list]

        positive_assignments = self._collect_positive_assignments(parsed_clause, pair_list, slot_count)
        if len(positive_assignments) == 0:
            positive_assignments.add(self._build_bitvector_from_args(parsed_clause, pair_list))

        var_count = len(eq_vars)
        if var_count == 0:
            return il.And() if tuple() in positive_assignments else il.Or()

        vars_tt = [exprvar(name) for name in eq_vars]
        table_bits = []
        for mask in range(1 << var_count):
            bits = tuple((mask >> idx) & 1 for idx in range(var_count))
            if not self._is_valid_partition(bits, pair_list, slot_count):
                table_bits.append('-')
            elif bits in positive_assignments:
                table_bits.append('1')
            else:
                table_bits.append('0')

        tt = truthtable(vars_tt, ''.join(table_bits))
        minimized = espresso_tts(tt)
        minimized_expr = minimized[0] if minimized else None
        return minimized_expr if minimized_expr is not None else il.And()

    def _parse_literal(self, literal: str):
        token = literal.strip()
        is_neg = token.startswith('~')
        if is_neg:
            token = token[1:].strip()

        m_rel = re.match(r'^([\w.]+)\(([^)]*)\)$', token)
        if m_rel:
            pred = m_rel.group(1)
            args = [arg.strip() for arg in m_rel.group(2).split(',') if arg.strip()]
            return (is_neg, pred, args)

        # Handle: func(args)=var without parens, e.g. _epoch3(node0)=ep
        m_fun_var_eq = re.match(r'^([\w.]+)\(([^)]*)\)=([\w.]+)$', token)
        if m_fun_var_eq:
            func = m_fun_var_eq.group(1)
            func_args = [arg.strip() for arg in m_fun_var_eq.group(2).split(',') if arg.strip()]
            rhs = m_fun_var_eq.group(3).strip()
            return (is_neg, rhs + '=' + func, func_args)

        # Handle: var=func(args) without parens, e.g. ep=_epoch3(node0)
        m_var_fun_eq = re.match(r'^([\w.]+)=([\w.]+)\(([^)]*)\)$', token)
        if m_var_fun_eq:
            lhs = m_var_fun_eq.group(1).strip()
            func = m_var_fun_eq.group(2).strip()
            func_args = [arg.strip() for arg in m_var_fun_eq.group(3).split(',') if arg.strip()]
            return (is_neg, lhs + '=' + func, func_args)

        # Handle: var=var without parens, e.g. ep=epoch0
        m_simple_eq = re.match(r'^([\w.]+)=([\w.]+)$', token)
        if m_simple_eq:
            pred = m_simple_eq.group(1) + '='
            return (is_neg, pred, [m_simple_eq.group(2).strip()])

        if token.startswith('(') and token.endswith(')') and '=' in token:
            inner = token[1:-1].strip()
            m_fun_eq = re.match(r'^([\w.]+)\(([^)]*)\)=([\w.]+)$', inner)
            if m_fun_eq:
                pred = m_fun_eq.group(1) + '='
                lhs_args = [arg.strip() for arg in m_fun_eq.group(2).split(',') if arg.strip()]
                rhs = m_fun_eq.group(3).strip()
                return (is_neg, pred, lhs_args + [rhs])
            m_eq = re.match(r'^([\w.]+)=([\w.]+)$', inner)
            if m_eq:
                pred = m_eq.group(1) + '='
                return (is_neg, pred, [m_eq.group(2).strip()])

        return (is_neg, token, [])

    def _format_literal(self, is_neg: bool, pred: str, args: List[str]) -> str:
        body = pred
        if pred.endswith('='):
            f = pred[:-1]
            if len(args) == 1:
                body = f'({f}={args[0]})'
            elif len(args) > 1:
                body = f'({f}({",".join(args[:-1])})={args[-1]})'
            else:
                body = f'({f}=)'
        elif len(args) > 0:
            body = f'{pred}({",".join(args)})'
        return ('~' if is_neg else '') + body

    def _signature_key(self, parsed_literal):
        is_neg, pred, args = parsed_literal
        return (is_neg, pred, len(args))

    def _get_slot_sort_names(self, parsed_clause):
        const_to_sort = {}
        for sort_id, consts in enumerate(self.protocol.sort_constants):
            sort_name = self.protocol.sorts[sort_id]
            for c in consts:
                const_to_sort[c] = sort_name

        slot_sort_names = []
        for _, pred, args in parsed_clause:
            pred_sorts = self.protocol.predicates.get(pred, ())
            for arg_idx, arg in enumerate(args):
                sort_name = None
                if arg_idx < len(pred_sorts):
                    sort_name = pred_sorts[arg_idx]
                elif arg in const_to_sort:
                    sort_name = const_to_sort[arg]
                else:
                    raise ValueError(f'Cannot determine sort for argument {arg} at {pred}[{arg_idx}]')
                slot_sort_names.append(sort_name)
        return slot_sort_names

    def _build_slot_labels(self, slot_sort_names):
        per_sort_count = {}
        labels = []

        for sort_name in slot_sort_names:
            sort_key = str(sort_name)
            idx = per_sort_count.get(sort_key, 0)
            per_sort_count[sort_key] = idx + 1
            label = self.protocol.get_sort_quantifier_name(sort_key, idx)
            labels.append(label)

        return labels

    def _collect_positive_assignments(self, parsed_clause, pair_list, slot_count):
        """
        Compute all equality bit-vectors that are realizable by matching the
        representative parsed clause against each prime in the orbit.

        A "positive assignment" is a tuple of 0/1 bits aligned with `pair_list`:
        bit k corresponds to pair `pair_list[k]` and is 1 iff the two slots are
        assigned the same concrete constant under a consistent literal matching.

        Matching is done per literal signature (negation, predicate, arity), and
        all permutations within each signature group are explored. Any complete,
        conflict-free slot-to-constant mapping contributes one positive bit-vector.
        """
        positive = set()
        slot_offsets = self._compute_slot_offsets(parsed_clause)
        template_groups = {}
        for idx, lit in enumerate(parsed_clause):
            key = self._signature_key(lit)
            template_groups.setdefault(key, []).append((idx, lit))

        for prime in self.orbit.suborbit_repr_primes:
            parsed_prime = [self._parse_literal(lit) for lit in prime.literals_list]
            prime_groups = {}
            for lit in parsed_prime:
                key = self._signature_key(lit)
                prime_groups.setdefault(key, []).append(lit)

            if set(prime_groups.keys()) != set(template_groups.keys()):
                continue

            group_maps = []
            valid = True
            for key, tmpl_entries in template_groups.items():
                prime_entries = prime_groups.get(key, [])
                if len(prime_entries) != len(tmpl_entries):
                    valid = False
                    break
                indices = list(range(len(prime_entries)))
                idx_perms = list(permutations(indices))
                group_maps.append((tmpl_entries, prime_entries, idx_perms))
            if not valid:
                continue

            self._expand_group_assignments(
                slot_offsets,
                group_maps,
                0,
                {},
                positive,
                pair_list,
                slot_count,
            )

        return positive

    def _expand_group_assignments(self, slot_offsets, group_maps, gid, slot_to_const, positive, pair_list, slot_count):
        if gid >= len(group_maps):
            if len(slot_to_const) == slot_count:
                bits = self._bitvector_from_slot_map(slot_to_const, pair_list)
                positive.add(bits)
            return

        tmpl_entries, prime_entries, permutations = group_maps[gid]
        for perm in permutations:
            local = dict(slot_to_const)
            conflict = False
            for t_idx, p_idx in enumerate(perm):
                tmpl_lit_idx, tmpl_lit = tmpl_entries[t_idx]
                prime_lit = prime_entries[p_idx]
                tmpl_args = tmpl_lit[2]
                prime_args = prime_lit[2]
                if len(tmpl_args) != len(prime_args):
                    conflict = True
                    break
                for arg_pos in range(len(tmpl_args)):
                    slot_id = self._slot_id_from_literal_arg(slot_offsets, lit_idx=tmpl_lit_idx, arg_idx=arg_pos)
                    concrete = prime_args[arg_pos]
                    if slot_id in local and local[slot_id] != concrete:
                        conflict = True
                        break
                    local[slot_id] = concrete
                if conflict:
                    break
            if not conflict:
                self._expand_group_assignments(slot_offsets, group_maps, gid + 1, local, positive, pair_list, slot_count)

    def _compute_slot_offsets(self, parsed_clause):
        offsets = [0]
        total = 0
        for _, _, args in parsed_clause:
            total += len(args)
            offsets.append(total)
        return offsets

    def _slot_id_from_literal_arg(self, slot_offsets, lit_idx, arg_idx):
        return slot_offsets[lit_idx] + arg_idx

    def _bitvector_from_slot_map(self, slot_to_const, pair_list):
        bits = [0] * len(pair_list)
        for idx, (i, j) in enumerate(pair_list):
            bits[idx] = 1 if slot_to_const[i] == slot_to_const[j] else 0
        return tuple(bits)

    def _build_bitvector_from_args(self, parsed_clause, pair_list):
        slot_constants = []
        for _, _, args in parsed_clause:
            slot_constants.extend(args)
        bits = [0] * len(pair_list)
        for idx, (i, j) in enumerate(pair_list):
            bits[idx] = 1 if slot_constants[i] == slot_constants[j] else 0
        return tuple(bits)

    def _is_valid_partition(self, bits, pair_list, slot_count):
        parent = list(range(slot_count))

        def find(x):
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x

        def union(a, b):
            ra, rb = find(a), find(b)
            if ra != rb:
                parent[rb] = ra

        for idx, (i, j) in enumerate(pair_list):
            if bits[idx] == 1:
                union(i, j)

        for idx, (i, j) in enumerate(pair_list):
            same_block = 1 if find(i) == find(j) else 0
            if same_block != bits[idx]:
                return False
        return True
    

    # INPUT the expression from enumerate
    # we then convert e01 and so on into the right format for the rest of the code so the And(e01 OR(e12 e02))
    # turns into forall N0,N1,N2. (N0=N1 & (N1=N2 | N0=N2)) -> orbit stuff 

    def _lifted_orbit_literals(self, parsed_clause, slot_labels):
        lifted = []
        slot_id = 0
        for is_neg, pred, args in parsed_clause:
            lifted_args = []
            for _ in args:
                lifted_args.append(slot_labels[slot_id])
                slot_id += 1
            lifted.append(self._format_literal(is_neg, pred, lifted_args))
        return lifted

    def _pyeda_expr_to_eq_string(self, expression, slot_labels):
        if expression is None:
            return 'true'
        if not hasattr(expression, 'to_ast'):
            return str(expression)

        uniqid_to_name = {}
        for v in expression.inputs:
            uniqid = getattr(v, 'uniqid', None)
            name = getattr(v, 'name', None)
            if uniqid is not None and name is not None:
                uniqid_to_name[uniqid] = name

        def lit_name_to_eq(name):
            m = re.fullmatch(r'e(\d+)(\d+)', name)
            if not m:
                return name
            i, j = int(m.group(1)), int(m.group(2))
            left = slot_labels[i]
            right = slot_labels[j]
            return f'{left} = {right}'

        def walk(node):
            tag = node[0]
            if tag == 'const':
                return 'true' if bool(node[1]) else 'false'
            if tag == 'lit':
                lit_id = node[1]
                sign = lit_id > 0
                base = abs(lit_id)
                name = uniqid_to_name.get(base, f'e{base}')
                atom = lit_name_to_eq(name)
                return atom if sign else f'~({atom})'
            if tag == 'not':
                return f'~({walk(node[1])})'
            if tag == 'and':
                return '(' + ' & '.join(walk(sub) for sub in node[1:]) + ')'
            if tag == 'or':
                return '(' + ' | '.join(walk(sub) for sub in node[1:]) + ')'
            if tag == 'xor':
                parts = [walk(sub) for sub in node[1:]]
                if len(parts) == 0:
                    return 'false'
                if len(parts) == 1:
                    return parts[0]
                acc = f'(({parts[0]} & ~({parts[1]})) | (~({parts[0]}) & {parts[1]}))'
                for p in parts[2:]:
                    acc = f'(({acc} & ~({p})) | (~({acc}) & {p}))'
                return acc
            return str(node)

        return walk(expression.to_ast())

    def _get_cnf_qclause(self, expression):
        clause = list(self.orbit.repr_prime.literals_list)
        parsed_clause = [self._parse_literal(lit) for lit in clause]
        slot_sort_names = self._get_slot_sort_names(parsed_clause)
        slot_labels = self._build_slot_labels(slot_sort_names)
        lifted_literals = self._lifted_orbit_literals(parsed_clause, slot_labels)

        qvars = list(slot_labels)
        eq_part = self._pyeda_expr_to_eq_string(expression, slot_labels)
        orbit_part = ' & '.join(lifted_literals) if len(lifted_literals) > 0 else 'true'

        body = f'({eq_part} -> ({orbit_part}))'
        if len(qvars) == 0:
            return body
        return f'forall {",".join(qvars)}. {body}'
