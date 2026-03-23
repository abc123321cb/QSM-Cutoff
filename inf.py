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
        """Initialize inference state for deriving quantified orbit clauses.

        Args:
            orbit: Orbit data containing representative and suborbit primes.
            options: Runtime options for quantifier inference.
            protocol: Protocol metadata (sorts, constants, predicates).
            is_dnf: Flag indicating whether caller is using DNF mode.

        Returns:
            None.

        Example:
            inf = Inference(orbit, options, protocol, is_dnf=False)
        """
        self.orbit   = orbit
        self.options = options
        self.protocol = protocol
        self.is_dnf  = is_dnf

        self.forall_clauses: List[QFormula] = []


    def get_qclause(self):
        """Compute final quantified clause, restrictions, and source orbit literals.

        Args:
            None.

        Returns:
            A dict with keys:
                qclause: Ivy AST formula after redundant-sort merging.
                restrictions: Minimized equality restriction expression.
                orbit_literals: Representative orbit literals as strings.

        Example:
            out = inf.get_qclause()
            # out['qclause'] is an Ivy AST ForAll/Formula
        """
        restrictions = self.enumerate()
        large_qclause = self._get_cnf_qclause(restrictions)
        qclause = self.combine_redundant_sorts(large_qclause, restrictions)
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
        """Enumerate valid equalities and minimize them into a restriction formula.

        Args:
            None.

        Returns:
            A minimized Boolean expression (PyEDA AST) over eij equalities,
            or Ivy true/false formulas for degenerate cases.

        Example:
            expr = inf.enumerate()
            # expr can look like And(~e01, e12)
        """
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
        """Parse one literal string into normalized tuple form.

        Args:
            literal: Literal string in relation or equality style syntax.

        Returns:
            A tuple (is_negated, predicate_key, args) where args is a list of
            argument tokens.

        Example:
            inf._parse_literal('~e(node0,node1)')
            # (True, 'e', ['node0', 'node1'])
        """
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
        """Render a normalized literal tuple back into source-like string form.

        Args:
            is_neg: Whether the literal is negated.
            pred: Predicate/function marker from parsed form.
            args: Literal arguments.

        Returns:
            Formatted literal string.

        Example:
            inf._format_literal(True, 'e', ['NODE0', 'NODE1'])
            # '~e(NODE0,NODE1)'
        """
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
        """Build grouping key used for literal-shape matching.

        Args:
            parsed_literal: Parsed literal tuple (is_neg, pred, args).

        Returns:
            Tuple key (is_neg, pred, arity).

        Example:
            inf._signature_key((True, 'e', ['node0', 'node1']))
            # (True, 'e', 2)
        """
        is_neg, pred, args = parsed_literal
        return (is_neg, pred, len(args))

    def _get_slot_sort_names(self, parsed_clause):
        """Infer sort name for every argument slot in clause order.

        Args:
            parsed_clause: List of parsed literals.

        Returns:
            List of sort names, one per flattened argument slot.

        Example:
            # for ['mix(node0,epoch0)'] -> ['node', 'epoch']
        """
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
        """Create quantifier variable labels for each argument slot.

        Args:
            slot_sort_names: Flattened slot sort sequence.

        Returns:
            Slot label list aligned with slot_sort_names.

        Example:
            inf._build_slot_labels(['node', 'node', 'epoch'])
            # ['NODE0', 'NODE1', 'EPOCH0']
        """
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
        """Collect all realizable equality bit-vectors from orbit representatives.

        Args:
            parsed_clause: Parsed representative clause literals.
            pair_list: Slot-index pairs corresponding to equality variables.
            slot_count: Number of flattened argument slots.

        Returns:
            Set of tuples; each tuple is a 0/1 assignment aligned with pair_list.

        Example:
            # may return {(1, 0, 1), (0, 1, 0)} for three equality pairs
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
        """Recursively enumerate consistent literal-group matchings.

        Args:
            slot_offsets: Prefix offsets for slot indexing by literal.
            group_maps: Per-signature matching/permutation data.
            gid: Current group index in recursion.
            slot_to_const: Current partial slot-to-constant map.
            positive: Output set collecting realized bit-vectors.
            pair_list: Slot pairs for equality bits.
            slot_count: Total number of slots.

        Returns:
            None. Updates positive in place.

        Example:
            # called internally to explore all group permutations recursively
        """
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
        """Compute prefix sums used to flatten (literal,arg) positions to slot IDs.

        Args:
            parsed_clause: Parsed literals.

        Returns:
            Prefix-offset list of length len(parsed_clause) + 1.

        Example:
            # arg counts [2, 1, 3] -> [0, 2, 3, 6]
        """
        offsets = [0]
        total = 0
        for _, _, args in parsed_clause:
            total += len(args)
            offsets.append(total)
        return offsets

    def _slot_id_from_literal_arg(self, slot_offsets, lit_idx, arg_idx):
        """Map literal index and argument index to global flattened slot ID.

        Args:
            slot_offsets: Prefix offsets for literals.
            lit_idx: Literal index in parsed clause.
            arg_idx: Argument index inside the literal.

        Returns:
            Integer slot ID.

        Example:
            # offsets [0,2,5], lit_idx=1, arg_idx=2 -> 4
        """
        return slot_offsets[lit_idx] + arg_idx

    def _bitvector_from_slot_map(self, slot_to_const, pair_list):
        """Convert slot-constant map to equality bit-vector over pair_list.

        Args:
            slot_to_const: Mapping slot ID -> concrete constant.
            pair_list: Slot-index pairs.

        Returns:
            Tuple of 0/1 bits indicating equality for each slot pair.

        Example:
            # pair (0,1) is 1 if slot_to_const[0] == slot_to_const[1]
        """
        bits = [0] * len(pair_list)
        for idx, (i, j) in enumerate(pair_list):
            bits[idx] = 1 if slot_to_const[i] == slot_to_const[j] else 0
        return tuple(bits)

    def _build_bitvector_from_args(self, parsed_clause, pair_list):
        """Build default equality bit-vector from representative literal arguments.

        Args:
            parsed_clause: Parsed representative literals.
            pair_list: Slot-index pairs.

        Returns:
            Tuple of 0/1 equality bits.

        Example:
            # parsed args ['node0','node0'] with pair (0,1) -> (1,)
        """
        slot_constants = []
        for _, _, args in parsed_clause:
            slot_constants.extend(args)
        bits = [0] * len(pair_list)
        for idx, (i, j) in enumerate(pair_list):
            bits[idx] = 1 if slot_constants[i] == slot_constants[j] else 0
        return tuple(bits)

    def _is_valid_partition(self, bits, pair_list, slot_count):
        """Check if bit assignment encodes a valid equivalence relation.

        Args:
            bits: Candidate 0/1 equality assignment.
            pair_list: Slot-index pairs corresponding to bits.
            slot_count: Number of slots.

        Returns:
            True if assignment is transitively consistent, otherwise False.

        Example:
            # bits for e01=1, e12=1, e02=0 are invalid (violates transitivity)
        """
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

    def _nnf_push_not(self, f):
        """Push negations inward to produce a lightweight NNF formula.

        Args:
            f: Ivy AST formula.

        Returns:
            Ivy AST with negations pushed through And/Or where handled.

        Example:
            # ~(a | b) -> (~a & ~b)
        """
        if isinstance(f, il.Not):
            g = f.args[0]
            if isinstance(g, il.Not):
                return self._nnf_push_not(g.args[0])
            if isinstance(g, il.Or):
                return il.And(*[self._nnf_push_not(il.Not(a)) for a in g.args])
            if isinstance(g, il.And):
                return il.Or(*[self._nnf_push_not(il.Not(a)) for a in g.args])
            return f
        if isinstance(f, il.Or):
            return il.Or(*[self._nnf_push_not(a) for a in f.args])
        if isinstance(f, il.And):
            return il.And(*[self._nnf_push_not(a) for a in f.args])
        return f

    def _build_label_to_var(self, slot_sort_names, slot_labels):
        """Create a label-to-variable mapping using protocol sort definitions.

        Args:
            slot_sort_names: Sort names by slot index.
            slot_labels: Variable labels by slot index.

        Returns:
            Dict mapping each label to an Ivy variable object.

        Example:
            # {'NODE0': Var('NODE0', ...), 'NODE1': Var('NODE1', ...)}
        """
        sort_map = {
            str(sort_name): il.EnumeratedSort(str(sort_name), list(self.protocol.sort_constants[sort_id]))
            for sort_id, sort_name in enumerate(self.protocol.sorts)
        }
        label_to_var = {}
        for label, sort_name in zip(slot_labels, slot_sort_names):
            if label not in label_to_var:
                label_to_var[label] = il.Variable(label, sort_map[str(sort_name)])
        return label_to_var

    def _evaluate_pyeda_ast(self, node, assignment, uniqid_to_name):
        """Evaluate a PyEDA AST node under a Boolean variable assignment.

        Args:
            node: PyEDA AST tuple.
            assignment: Mapping variable name -> Boolean value.
            uniqid_to_name: Mapping PyEDA literal IDs to variable names.

        Returns:
            Boolean result of evaluating node under assignment.

        Example:
            # evaluates ('and', ('lit', 1), ('not', ('lit', 2)))
        """
        tag = node[0]
        if tag == 'const':
            return bool(node[1])
        if tag == 'lit':
            lit_id = node[1]
            name = uniqid_to_name.get(abs(lit_id), f'e{abs(lit_id)}')
            value = assignment.get(name, False)
            return value if lit_id > 0 else not value
        if tag == 'not':
            return not self._evaluate_pyeda_ast(node[1], assignment, uniqid_to_name)
        if tag == 'and':
            return all(self._evaluate_pyeda_ast(child, assignment, uniqid_to_name) for child in node[1:])
        if tag == 'or':
            return any(self._evaluate_pyeda_ast(child, assignment, uniqid_to_name) for child in node[1:])
        if tag == 'xor':
            value = False
            for child in node[1:]:
                value ^= self._evaluate_pyeda_ast(child, assignment, uniqid_to_name)
            return value
        return False

    def _iter_pyeda_models(self, expression):
        """Enumerate satisfying assignments for a PyEDA expression.

        Args:
            expression: PyEDA expression or Ivy true/false fallback.

        Returns:
            Generator of assignments as dicts name -> bool.

        Example:
            # yields {'e01': True, 'e12': False}, ... for satisfying models
        """
        if not hasattr(expression, 'to_ast'):
            if il.is_true(expression):
                yield {}
            return
        inputs = list(expression.inputs)
        uniqid_to_name = {
            getattr(var, 'uniqid', None): getattr(var, 'name', None)
            for var in inputs
            if getattr(var, 'uniqid', None) is not None and getattr(var, 'name', None) is not None
        }
        names = [name for name in (getattr(var, 'name', None) for var in inputs) if name is not None]
        ast = expression.to_ast()
        for mask in range(1 << len(names)):
            assignment = {
                names[idx]: bool((mask >> idx) & 1)
                for idx in range(len(names))
            }
            if self._evaluate_pyeda_ast(ast, assignment, uniqid_to_name):
                yield assignment

    def _restriction_is_unsat(self, restrictions):
        """Determine whether the restriction formula has no satisfying model.

        Args:
            restrictions: Restriction expression (PyEDA or Ivy fallback).

        Returns:
            True if unsatisfiable, else False.

        Example:
            # returns True when no assignment satisfies restrictions
        """
        if hasattr(restrictions, 'to_ast'):
            for _ in self._iter_pyeda_models(restrictions):
                return False
            return True
        return il.is_false(restrictions)

    def _restriction_forces_equality(self, restrictions, var_name):
        """Check whether all satisfying models force a given equality variable true.

        Args:
            restrictions: Restriction expression (PyEDA or Ivy fallback).
            var_name: Equality variable name (e.g., e01).

        Returns:
            True if var_name is true in every satisfying model, else False.

        Example:
            inf._restriction_forces_equality(expr, 'e01')
            # True means e01 is logically implied by expr
        """
        if self._restriction_is_unsat(restrictions):
            return False
        if not hasattr(restrictions, 'to_ast'):
            return False
        saw_model = False
        for assignment in self._iter_pyeda_models(restrictions):
            saw_model = True
            if not assignment.get(var_name, False):
                return False
        return saw_model

    def _pyeda_expr_to_ivy_formula(self, expression, slot_labels, label_to_var):
        """Translate minimized PyEDA expression into Ivy equality formula AST.

        Args:
            expression: PyEDA expression over eij variables.
            slot_labels: Slot labels by index.
            label_to_var: Mapping from labels to Ivy variables.

        Returns:
            Ivy formula equivalent to the given PyEDA expression.

        Example:
            # e01 & ~e12 -> (NODE0 = NODE1) & ~(NODE1 = NODE2)
        """
        if expression is None:
            return il.And()
        if not hasattr(expression, 'to_ast'):
            if il.is_true(expression):
                return il.And()
            if il.is_false(expression):
                return il.Or()
            return il.And()

        uniqid_to_name = {}
        for var in expression.inputs:
            uniqid = getattr(var, 'uniqid', None)
            name = getattr(var, 'name', None)
            if uniqid is not None and name is not None:
                uniqid_to_name[uniqid] = name

        def eq_atom(name):
            match = re.fullmatch(r'e(\d+)(\d+)', name)
            if not match:
                return il.And()
            left_idx, right_idx = int(match.group(1)), int(match.group(2))
            return il.Equals(label_to_var[slot_labels[left_idx]], label_to_var[slot_labels[right_idx]])

        def walk(node):
            tag = node[0]
            if tag == 'const':
                return il.And() if bool(node[1]) else il.Or()
            if tag == 'lit':
                lit_id = node[1]
                atom = eq_atom(uniqid_to_name.get(abs(lit_id), f'e{abs(lit_id)}'))
                return atom if lit_id > 0 else il.Not(atom)
            if tag == 'not':
                return il.Not(walk(node[1]))
            if tag == 'and':
                return il.And(*[walk(sub) for sub in node[1:]])
            if tag == 'or':
                return il.Or(*[walk(sub) for sub in node[1:]])
            if tag == 'xor':
                parts = [walk(sub) for sub in node[1:]]
                if len(parts) == 0:
                    return il.Or()
                acc = parts[0]
                for part in parts[1:]:
                    acc = il.Or(il.And(acc, il.Not(part)), il.And(il.Not(acc), part))
                return acc
            return il.And()

        return walk(expression.to_ast())

    def _simplify_formula(self, formula):
        """Apply lightweight algebraic simplifications over Ivy AST formulas.

        Args:
            formula: Ivy formula to simplify.

        Returns:
            Simplified Ivy formula.

        Example:
            # simplifies (true -> phi) to phi
        """
        args = [self._simplify_formula(arg) for arg in formula.args]
        if isinstance(formula, il.Not):
            inner = args[0]
            if il.is_true(inner):
                return il.Or()
            if il.is_false(inner):
                return il.And()
            if isinstance(inner, il.Not):
                return inner.args[0]
            return il.Not(inner)
        if isinstance(formula, il.Or):
            reduced = []
            seen = set()
            for arg in args:
                if il.is_true(arg):
                    return il.And()
                if il.is_false(arg):
                    continue
                key = str(arg)
                if key not in seen:
                    seen.add(key)
                    reduced.append(arg)
            return il.Or(*reduced)
        if isinstance(formula, il.And):
            reduced = []
            seen = set()
            for arg in args:
                if il.is_false(arg):
                    return il.Or()
                if il.is_true(arg):
                    continue
                key = str(arg)
                if key not in seen:
                    seen.add(key)
                    reduced.append(arg)
            return il.And(*reduced)
        if isinstance(formula, il.Implies):
            left, right = args
            if il.is_false(left) or il.is_true(right):
                return il.And()
            if il.is_true(left):
                return right
            if il.is_false(right):
                return self._simplify_formula(il.Not(left))
            if left == right:
                return il.And()
            return il.Implies(left, right)
        if il.is_eq(formula):
            left, right = args
            if left == right:
                return il.And()
            if (il.is_true(left) or il.is_false(left)) and (il.is_true(right) or il.is_false(right)):
                return il.And() if left == right else il.Or()
            if il.is_true(left):
                return right
            if il.is_true(right):
                return left
            if il.is_false(left):
                return self._simplify_formula(il.Not(right))
            if il.is_false(right):
                return self._simplify_formula(il.Not(left))
            return il.Equals(left, right)
        return formula

    def _build_lifted_orbit_formula(self, parsed_clause, slot_sort_names, slot_labels, label_to_var=None):
        """Build Ivy AST formula for the representative orbit clause over slot vars.

        Args:
            parsed_clause: Parsed representative literals.
            slot_sort_names: Sort names by flattened slot.
            slot_labels: Slot labels by flattened slot.
            label_to_var: Optional prebuilt label-to-variable map.

        Returns:
            Ivy conjunction formula representing lifted orbit literals.

        Example:
            # ['e(node0,node1)'] -> e(NODE0,NODE1)
        """
        if label_to_var is None:
            label_to_var = self._build_label_to_var(slot_sort_names, slot_labels)
        symbol_cache = {}
        atoms = []
        slot_id = 0

        def get_symbol(name, dom_sorts, rng_sort=None):
            key = (name, tuple(str(sort) for sort in dom_sorts), str(rng_sort) if rng_sort is not None else None)
            if key in symbol_cache:
                return symbol_cache[key]
            if rng_sort is None:
                symbol_sort = il.RelationSort(list(dom_sorts))
            elif len(dom_sorts) == 0:
                symbol_sort = rng_sort
            else:
                symbol_sort = il.FunctionSort(*(list(dom_sorts) + [rng_sort]))
            symbol_cache[key] = il.Symbol(name, symbol_sort)
            return symbol_cache[key]

        for is_neg, pred, args in parsed_clause:
            arg_terms = []
            for _ in args:
                arg_terms.append(label_to_var[slot_labels[slot_id]])
                slot_id += 1

            if pred.endswith('='):
                head = pred[:-1]
                if len(arg_terms) == 0:
                    atom = il.Equals(get_symbol(head, [], None), get_symbol(head, [], None))
                elif len(arg_terms) == 1:
                    lhs = get_symbol(head, [], arg_terms[0].sort)
                    atom = il.Equals(lhs, arg_terms[0])
                else:
                    lhs = il.App(
                        get_symbol(head, [term.sort for term in arg_terms[:-1]], arg_terms[-1].sort),
                        *arg_terms[:-1],
                    )
                    atom = il.Equals(lhs, arg_terms[-1])
            else:
                rel = get_symbol(pred, [term.sort for term in arg_terms], None)
                atom = il.App(rel, *arg_terms) if len(arg_terms) > 0 else rel

            atoms.append(il.Not(atom) if is_neg else atom)

        return il.And(*atoms)

    def _lifted_orbit_literals(self, parsed_clause, slot_labels):
        """Create string-form lifted literals using slot labels as arguments.

        Args:
            parsed_clause: Parsed representative literals.
            slot_labels: Slot labels by flattened slot.

        Returns:
            List of lifted literal strings.

        Example:
            # ['~e(node0,node1)'] -> ['~e(NODE0,NODE1)']
        """
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
        """Render PyEDA equality expression into readable string using slot labels.

        Args:
            expression: PyEDA expression over eij variables.
            slot_labels: Slot labels by index.

        Returns:
            String representation of the Boolean equality expression.

        Example:
            # e01 | ~e12 -> '(NODE0 = NODE1 | ~(NODE1 = NODE2))'
        """
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
        """Construct initial quantified Ivy clause from restrictions and orbit body.

        Args:
            expression: Restriction expression produced by enumerate().

        Returns:
            Ivy formula, usually a ForAll with implication body.

        Example:
            q = inf._get_cnf_qclause(expr)
            # forall NODE... . (restrictions -> negated_orbit)
        """
        clause = list(self.orbit.repr_prime.literals_list)
        parsed_clause = [self._parse_literal(lit) for lit in clause]
        slot_sort_names = self._get_slot_sort_names(parsed_clause)
        slot_labels = self._build_slot_labels(slot_sort_names)
        label_to_var = self._build_label_to_var(slot_sort_names, slot_labels)
        antecedent = self._simplify_formula(self._pyeda_expr_to_ivy_formula(expression, slot_labels, label_to_var))
        orbit_formula = self._build_lifted_orbit_formula(parsed_clause, slot_sort_names, slot_labels, label_to_var)
        negated_orbit_formula = self._simplify_formula(self._nnf_push_not(il.Not(orbit_formula)))
        body_formula = self._simplify_formula(il.Implies(antecedent, negated_orbit_formula))

        qvars = []
        seen = set()
        for label in slot_labels:
            if label in seen:
                continue
            seen.add(label)
            qvars.append(label_to_var[label])
        if len(qvars) == 0:
            return body_formula
        return il.ForAll(qvars, body_formula)

    # this function takes the expression and looks at the expression so if we have something like 
    # forall NODE0,NODE1. (NODE0 = NODE1 -> (~locked_epoch3(NODE0) | ep=_epoch3(NODE1)))
    # We can actually just combine NODE0 and NODE1 to 
    # forall NODE0. true -> (~locked_epoch3(NODE0) | ep=_epoch3(NODE0))
    # which will simplify the expression.
    # This will actually check the domain size so if we are at size 2 for nodes
    # NODE0 != NODE1 & NODE0 != NODE2
    # Will actually combine node1 and node2 because the above expression at size 2 implies
    # NODE1 = NODE2 
    def combine_redundant_sorts(self, expression, restrictions):
        """Merge forced-equal quantified variables and rebuild a smaller quantifier list.

        Args:
            expression: Ivy quantified formula produced by _get_cnf_qclause.
            restrictions: Restriction expression over eij equalities.

        Returns:
            Ivy formula with redundant quantified variables merged/eliminated.

        Example:
            # if restrictions force NODE0 = NODE1, drops NODE1 from quantifiers
        """
        clause = list(self.orbit.repr_prime.literals_list)
        if not clause:
            return expression

        if not isinstance(expression, il.ForAll):
            return expression

        parsed_clause = [self._parse_literal(lit) for lit in clause]
        slot_sort_names = self._get_slot_sort_names(parsed_clause)
        slot_labels = self._build_slot_labels(slot_sort_names)
        slot_count = len(slot_sort_names)

        if self._restriction_is_unsat(restrictions):
            return il.And()

        qvars = list(il.quantifier_vars(expression))
        body_formula = il.quantifier_body(expression)

        name_to_var = {}
        for qvar in qvars:
            name = getattr(qvar, 'name', getattr(qvar, 'rep', str(qvar)))
            name_to_var[name] = qvar

        slot_vars = []
        for label in slot_labels:
            qvar = name_to_var.get(label)
            if qvar is None:
                return expression
            slot_vars.append(qvar)

        pair_list = [
            (i, j)
            for i in range(slot_count - 1)
            for j in range(i + 1, slot_count)
            if slot_sort_names[i] == slot_sort_names[j]
        ]

        parent = list(range(slot_count))

        def find(x):
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x

        def union(left, right):
            root_left, root_right = find(left), find(right)
            if root_left != root_right:
                parent[root_right] = root_left

        for left_idx, right_idx in pair_list:
            if self._restriction_forces_equality(restrictions, f'e{left_idx}{right_idx}'):
                union(left_idx, right_idx)

        subs = {}
        for idx, qvar in enumerate(slot_vars):
            rep_var = slot_vars[find(idx)]
            if qvar != rep_var:
                subs[qvar] = rep_var

        if len(subs) > 0:
            body_formula = il.substitute(body_formula, subs)
        body_formula = self._simplify_formula(body_formula)

        used_vars = ilu.used_variables_ast(body_formula)
        ordered_qvars = []
        seen = set()
        for qvar in slot_vars:
            rep_var = subs.get(qvar, qvar)
            if rep_var in seen:
                continue
            seen.add(rep_var)
            if rep_var in used_vars:
                ordered_qvars.append(rep_var)
        for qvar in qvars:
            rep_var = subs.get(qvar, qvar)
            if rep_var in seen:
                continue
            seen.add(rep_var)
            if rep_var in used_vars:
                ordered_qvars.append(rep_var)

        if len(ordered_qvars) == 0:
            return body_formula
        return il.ForAll(ordered_qvars, body_formula)
    
