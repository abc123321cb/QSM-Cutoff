#!/usr/bin/env python3
import ast
import itertools
import re
from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple, Any

from z3 import (
    And, Or, Not, BoolSort, EnumSort, Function, Const, Bool,
    Solver, substitute, sat, ExprRef, FuncDeclRef, SortRef
)

# ----------------------------
# Parsing helpers
# ----------------------------

TOKEN_RE = re.compile(
    r"\s*("
    r"forall|exists|=>|~=|!=|=|\||&|~|\(|\)|\[|\]|,|\.|"
    r"[A-Za-z_][A-Za-z0-9_]*"
    r")"
)


class ParseError(Exception):
    pass

def strip_wrapping_parens(s: str) -> str:
    s = s.strip()
    if s.startswith("(") and s.endswith(")"):
        depth = 0
        for i, ch in enumerate(s):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0 and i != len(s) - 1:
                    return s
        return s[1:-1].strip()
    return s

def natural_key(name: str) -> Tuple[str, int]:
    m = re.match(r"^([A-Za-z_]+)(\d+)$", name)
    if not m:
        return (name, -1)
    return (m.group(1), int(m.group(2)))

def rewrite_invariant_line(line: str) -> str:
    """
    Tries to normalize some common naming differences to match your state atoms.

    Examples:
      locked_epoch2(NODE1) -> locked(epoch2,NODE1)
      transfer_epoch3(NODE0) -> transfer(epoch3,NODE0)
      ep=_epoch0(NODE1) -> ep(NODE1)=epoch0
    """
    line = line.strip()
    line = line.replace("~=", "!=")


    def rep_locked(m):
        k = m.group(1)
        v = m.group(2)
        return f"locked(epoch{k},{v})"

    def rep_transfer(m):
        k = m.group(1)
        v = m.group(2)
        return f"transfer(epoch{k},{v})"

    def rep_ep_epoch(m):
        k = m.group(1)
        v = m.group(2)
        return f"ep({v})=epoch{k}"

    line = re.sub(r"\blocked_epoch(\d+)\(\s*([A-Za-z_][A-Za-z0-9_]*)\s*\)", rep_locked, line)
    line = re.sub(r"\btransfer_epoch(\d+)\(\s*([A-Za-z_][A-Za-z0-9_]*)\s*\)", rep_transfer, line)
    line = re.sub(r"\bep\s*=\s*_epoch(\d+)\(\s*([A-Za-z_][A-Za-z0-9_]*)\s*\)", rep_ep_epoch, line)

    return line

@dataclass
class ParsedInvariant:
    # A sequence of quantifier blocks such as:
    #   [("forall", [EPOCH0]), ("exists", [NODE0, NODE1])]
    # representing: forall EPOCH0. exists NODE0,NODE1. body
    quant_blocks: List[Tuple[str, List[ExprRef]]]
    body: ExprRef


class Z3ClauseParser:
    """
    Parses a single line clause-ish syntax:
      forall NODE1,NODE0. A | ~B | X = Y
    into a ParsedInvariant. Quantifiers are not created as Z3 quantifiers;
    we expand them ourselves later over a finite domain.
    """

    def __init__(
        self,
        node_names: List[str],
        epoch_names: List[str],
    ):
        self.node_names = node_names
        self.epoch_names = epoch_names

        # Finite domains (EnumSort) so we can ground quantifiers cleanly
        self.NodeSort, self.node_consts = EnumSort("Node", node_names) if node_names else (None, [])
        self.EpochSort, self.epoch_consts = EnumSort("Epoch", epoch_names) if epoch_names else (None, [])

        # Name -> constant mapping for known domain constants
        self.predeclared: Dict[str, ExprRef] = {}
        if self.NodeSort is not None:
            for n, c in zip(node_names, self.node_consts):
                self.predeclared[n] = c
        if self.EpochSort is not None:
            for n, c in zip(epoch_names, self.epoch_consts):
                self.predeclared[n] = c

        # Symbol tables
        self.term_consts: Dict[str, ExprRef] = {}
        self.bool_consts: Dict[str, ExprRef] = {}
        self.funcs: Dict[str, FuncDeclRef] = {}
        self.preds: Dict[str, FuncDeclRef] = {}

        # Per-line
        self.env: Dict[str, ExprRef] = {}
        self.tokens: List[str] = []
        self.i = 0

    def declarations(self) -> Dict[str, Any]:
        return {
            "NodeSort": self.NodeSort,
            "EpochSort": self.EpochSort,
            "nodes": self.node_consts,
            "epochs": self.epoch_consts,
            "predeclared": self.predeclared,
            "term_consts": self.term_consts,
            "bool_consts": self.bool_consts,
            "funcs": self.funcs,
            "preds": self.preds,
        }

    # ------------- token stream -------------
    def _tokenize(self, s: str) -> List[str]:
        toks = TOKEN_RE.findall(s)
        joined = "".join(toks)
        compact = re.sub(r"\s+", "", s)
        if joined != compact:
            raise ParseError("Tokenization failed: unsupported character(s) present")
        return toks

    def _peek(self) -> Optional[str]:
        return self.tokens[self.i] if self.i < len(self.tokens) else None

    def _pop(self) -> str:
        t = self._peek()
        if t is None:
            raise ParseError("Unexpected end of input")
        self.i += 1
        return t

    def _accept(self, t: str) -> bool:
        if self._peek() == t:
            self.i += 1
            return True
        return False

    def _expect(self, t: str) -> None:
        if not self._accept(t):
            raise ParseError(f"Expected '{t}', got '{self._peek()}'")

    def _is_ident(self, t: Optional[str]) -> bool:
        return t is not None and re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", t) is not None

    # ------------- sort inference -------------
    def _infer_var_sort(self, name: str) -> SortRef:
        up = name.upper()
        if self.NodeSort is not None and up.startswith("NODE"):
            return self.NodeSort
        if self.EpochSort is not None and (up.startswith("EPOCH") or name.lower().startswith("epoch")):
            return self.EpochSort
        # Fallback: if it looks like nodeX or epochX, map to those
        if self.NodeSort is not None and re.match(r"^node\d+$", name, re.IGNORECASE):
            return self.NodeSort
        if self.EpochSort is not None and re.match(r"^epoch\d+$", name, re.IGNORECASE):
            return self.EpochSort
        # Last resort: treat as Node if only Node exists
        if self.NodeSort is not None and self.EpochSort is None:
            return self.NodeSort
        if self.EpochSort is not None and self.NodeSort is None:
            return self.EpochSort
        # If both exist and unknown, default to Node
        if self.NodeSort is not None:
            return self.NodeSort
        raise ParseError(f"Cannot infer sort for '{name}' (no finite domains found)")

    # ------------- public parse -------------
    def parse_invariant_line(self, line: str) -> ParsedInvariant:
        self.tokens = self._tokenize(line)
        self.i = 0
        self.env = {}

        quant_blocks: List[Tuple[str, List[ExprRef]]] = []
        if self._peek() in ("forall", "exists"):
            # Support mixed prefixes like: forall EPOCH0, exists NODE0.
            while self._peek() in ("forall", "exists"):
                q = self._pop()
                vars_out = self._parse_varlist_until_quant_or_dot()
                if not vars_out:
                    raise ParseError("Empty quantified variable list")
                quant_blocks.append((q, vars_out))
                self._accept(",")
            self._expect(".")

        body = self._parse_expr()

        if self._peek() is not None:
            raise ParseError(f"Unexpected token '{self._peek()}' at end")

        return ParsedInvariant(quant_blocks=quant_blocks, body=body)
    
    def _parse_expr(self) -> ExprRef:
        return self._parse_implies()

    def _parse_implies(self) -> ExprRef:
        left = self._parse_or()
        if self._accept("=>"):
            right = self._parse_implies()  # right-associative
            return Or(Not(left), right)
        return left

    def _parse_or(self) -> ExprRef:
        left = self._parse_and()
        while self._accept("|"):
            right = self._parse_and()
            left = Or(left, right)
        return left

    def _parse_and(self) -> ExprRef:
        left = self._parse_unary()
        while self._accept("&"):
            right = self._parse_unary()
            left = And(left, right)
        return left

    def _parse_unary(self) -> ExprRef:
        if self._accept("~"):
            return Not(self._parse_unary())

        if self._accept("("):
            e = self._parse_expr()
            self._expect(")")
            return e

        if self._accept("["):
            e = self._parse_expr()
            self._expect("]")
            return e

        return self._parse_atom_or_equality()
    
    def parse_atom(self, atom_str: str) -> ExprRef:
        atom_str = strip_wrapping_parens(atom_str)
        pi = self.parse_invariant_line(atom_str)
        if pi.quant_blocks:
            raise ParseError("State atom unexpectedly contains a quantifier")
        return pi.body

    # ------------- grammar -------------
    def _parse_varlist_until_quant_or_dot(self) -> List[ExprRef]:
        out: List[ExprRef] = []
        while True:
            t = self._peek()
            if t is None:
                raise ParseError("Unexpected end while reading quantified variable list")
            if t == "." or t in ("forall", "exists"):
                break
            if t == ",":
                self._pop()
                continue
            if not self._is_ident(t):
                raise ParseError(f"Expected variable name, got '{t}'")
            name = self._pop()
            if name in self.env:
                raise ParseError(f"Duplicate bound variable '{name}'")
            v = Const(name, self._infer_var_sort(name))
            self.env[name] = v
            out.append(v)
        return out

    def _parse_atom_or_equality(self) -> ExprRef:
        left_ast = self._parse_term_ast()
        if self._accept("="):
            right_ast = self._parse_term_ast()
            return self._term_to_z3(left_ast) == self._term_to_z3(right_ast)
        if self._accept("!=") or self._accept("~="):
            right_ast = self._parse_term_ast()
            return self._term_to_z3(left_ast) != self._term_to_z3(right_ast)
        return self._atom_to_z3(left_ast)

    def _parse_term_ast(self) -> Tuple:
        t = self._peek()
        if not self._is_ident(t):
            raise ParseError(f"Expected identifier, got '{t}'")
        name = self._pop()
        if self._accept("("):
            args: List[Tuple] = []
            if not self._accept(")"):
                args.append(self._parse_term_ast())
                while self._accept(","):
                    args.append(self._parse_term_ast())
                self._expect(")")
            return ("app", name, args)
        return ("id", name)

    # ------------- AST -> Z3 -------------
    def _id_to_term(self, name: str) -> ExprRef:
        if name in self.env:
            return self.env[name]
        if name in self.predeclared:
            return self.predeclared[name]

        # Epoch aliases: treat designated names as concrete epoch constants.
        # This matches typical Ivy encodings where:
        #   zero  == epoch0
        #   firste == epoch1
        #   max   == last epoch in the finite domain
        if self.EpochSort is not None and self.epoch_names:
            lname = name.lower()
            target_epoch: Optional[str] = None
            if lname == "zero":
                target_epoch = "epoch0"
            elif lname == "firste":
                target_epoch = "epoch1"
            elif lname == "max":
                target_epoch = self.epoch_names[-1]

            if target_epoch is not None:
                for k, v in self.predeclared.items():
                    if k.lower() == target_epoch.lower():
                        return v
                raise ParseError(
                    f"Alias '{name}' used but '{target_epoch}' not found in epoch constants"
                )

        if name in self.bool_consts:
            raise ParseError(f"Symbol '{name}' used as term but previously used as Bool atom")
        c = self.term_consts.get(name)
        if c is None:
            c = Const(name, self._infer_var_sort(name))
            self.term_consts[name] = c
        return c

    def _term_to_z3(self, ast: Tuple) -> ExprRef:
        kind = ast[0]
        if kind == "id":
            return self._id_to_term(ast[1])

        if kind == "app":
            fname, args_ast = ast[1], ast[2]
            args_z = [self._term_to_z3(a) for a in args_ast]
            arg_sorts = [a.sort() for a in args_z]
            f = self.funcs.get(fname)
            if f is None:
                # result sort heuristic: "ep" returns Epoch if available, else Node
                if fname.lower() == "ep" and self.EpochSort is not None:
                    res_sort = self.EpochSort
                else:
                    res_sort = self._infer_var_sort(fname)
                f = Function(fname, *arg_sorts, res_sort)
                self.funcs[fname] = f
            else:
                if f.arity() != len(arg_sorts):
                    raise ParseError(f"Arity mismatch for function '{fname}'")
            return f(*args_z)

        raise ParseError(f"Unknown AST kind '{kind}'")

    def _atom_to_z3(self, ast: Tuple) -> ExprRef:
        kind = ast[0]
        if kind == "id":
            name = ast[1]
            if name in self.env:
                raise ParseError(f"Bound variable '{name}' used as boolean atom without arguments")
            if name in self.predeclared:
                raise ParseError(f"Constant '{name}' used as boolean atom")
            if name in self.term_consts:
                raise ParseError(f"Symbol '{name}' used as Bool atom but previously used as term")
            b = self.bool_consts.get(name)
            if b is None:
                b = Bool(name)
                self.bool_consts[name] = b
            return b

        if kind == "app":
            pname, args_ast = ast[1], ast[2]
            args_z = [self._term_to_z3(a) for a in args_ast]
            arg_sorts = [a.sort() for a in args_z]
            p = self.preds.get(pname)
            if p is None:
                p = Function(pname, *arg_sorts, BoolSort())
                self.preds[pname] = p
            else:
                if p.arity() != len(arg_sorts):
                    raise ParseError(f"Arity mismatch for predicate '{pname}'")
            return p(*args_z)

        raise ParseError(f"Unknown AST kind '{kind}'")

# ----------------------------
# State file parsing
# ----------------------------

def read_states_file(path: str) -> Tuple[List[str], List[str], Dict[str, str]]:
    """
    Returns (atoms_list, bitstrings_list, interpreted_atoms).

    interpreted_atoms is a dict mapping atom strings to "0"/"1".
    If the file has no 'interpreted atoms: {...}' block, this is {}.
    """
    with open(path, "r", encoding="utf-8") as f:
        text = f.read()

    # Extract the python list after "state atoms:"
    m = re.search(r"state atoms:\s*(\[[\s\S]*?\])", text)
    if not m:
        raise ValueError("Could not find 'state atoms: [...]' in states file")

    atoms_str = m.group(1)
    atoms: List[str] = ast.literal_eval(atoms_str)

    interpreted_atoms: Dict[str, str] = {}
    m2 = re.search(r"interpreted atoms:\s*(\{[\s\S]*?\})", text)
    if m2:
        interpreted_atoms = ast.literal_eval(m2.group(1))

    bitstrings: List[str] = []
    for line in text.splitlines():
        s = line.strip()
        if re.fullmatch(r"[01]+", s):
            bitstrings.append(s)

    if not bitstrings:
        raise ValueError("No bitstring lines found in states file")

    # Validate lengths
    n = len(atoms)
    bad = [b for b in bitstrings if len(b) != n]
    if bad:
        raise ValueError(
            f"Found bitstrings with wrong length. Expected {n}, got lengths: "
            + ", ".join(sorted({str(len(b)) for b in bad}))
        )

    return atoms, bitstrings, interpreted_atoms

def extract_domain_constants(atoms: List[str]) -> Tuple[List[str], List[str]]:
    nodes = set()
    epochs = set()
    for a in atoms:
        for n in re.findall(r"\bnode\d+\b", a, flags=re.IGNORECASE):
            nodes.add(n)
        for e in re.findall(r"\bepoch\d+\b", a, flags=re.IGNORECASE):
            epochs.add(e)
    node_list = sorted(nodes, key=natural_key)
    epoch_list = sorted(epochs, key=natural_key)
    return node_list, epoch_list

# ----------------------------
# Grounding quantifiers over finite domains
# ----------------------------

def ground_invariant(pi: ParsedInvariant, domains: Dict[SortRef, List[ExprRef]]) -> ExprRef:
    """Ground ParsedInvariant by enumerating its finite domains.

    Supports mixed quantifier prefixes such as:
      forall EPOCH0, exists NODE0. body
    which ground to:
      And_{EPOCH0} Or_{NODE0} body
    """

    if not pi.quant_blocks:
        return pi.body

    def ground_from(block_index: int, expr: ExprRef) -> ExprRef:
        if block_index >= len(pi.quant_blocks):
            return expr

        quant, vars_in_block = pi.quant_blocks[block_index]
        if not vars_in_block:
            return ground_from(block_index + 1, expr)

        dom_lists: List[List[ExprRef]] = []
        for v in vars_in_block:
            vs = v.sort()
            if vs not in domains or not domains[vs]:
                raise ValueError(f"No finite domain provided for sort {vs} (var {v})")
            dom_lists.append(domains[vs])

        instances: List[ExprRef] = []
        for values in itertools.product(*dom_lists):
            subs = [(vars_in_block[i], values[i]) for i in range(len(vars_in_block))]
            inst_expr = substitute(expr, subs)
            instances.append(ground_from(block_index + 1, inst_expr))

        if quant == "forall":
            return And(instances) if instances else True
        if quant == "exists":
            return Or(instances) if instances else False
        raise ValueError(f"Unknown quantifier: {quant}")

    return ground_from(0, pi.body)

# ----------------------------
# Main comparison logic
# ----------------------------

def bitstring_to_constraints(atoms_z3: List[ExprRef], bits: str) -> List[ExprRef]:
    return [(a if b == "1" else Not(a)) for a, b in zip(atoms_z3, bits)]

def exclude_bitstring(atoms_z3: List[ExprRef], bits: str) -> ExprRef:
    # Blocks exactly this valuation
    # Or(atom != bit) is Or(atom) for bit=0, Or(Not(atom)) for bit=1
    return Or([(a if b == "0" else Not(a)) for a, b in zip(atoms_z3, bits)])

def model_to_bitstring(model, atoms_z3: List[ExprRef]) -> str:
    out = []
    for a in atoms_z3:
        v = model.eval(a, model_completion=True)
        out.append("1" if str(v) == "True" else "0")
    return "".join(out)

def main(invariants_path: str, states_path: str, spurious_limit: int = 10) -> None:
    atoms, reachable_bits, interpreted_atoms = read_states_file(states_path)
    node_names, epoch_names = extract_domain_constants(atoms)

    parser = Z3ClauseParser(node_names=node_names, epoch_names=epoch_names)
    decls = parser.declarations()

    # Parse state atoms into Z3 expressions (in a fixed order)
    atoms_z3: List[ExprRef] = [parser.parse_atom(a) for a in atoms]

    # Fixed constraints from interpreted atoms (e.g., le(epochi,epochj), (zero=epoch0), ...)
    interpreted_constraints: List[ExprRef] = []
    for atom_str, bit in interpreted_atoms.items():
        try:
            a = parser.parse_atom(atom_str)
        except Exception as e:
            raise ParseError(f"Could not parse interpreted atom '{atom_str}': {e}") from e
        interpreted_constraints.append(a if str(bit) == "1" else Not(a))

    # Parse and ground invariants
    parsed_invs: List[ParsedInvariant] = []
    with open(invariants_path, "r", encoding="utf-8") as f:
        for lineno, raw in enumerate(f, start=1):
            line = raw.strip()
            if not line or line.startswith("#"):
                continue
            line = rewrite_invariant_line(line)
            try:
                parsed_invs.append(parser.parse_invariant_line(line))
            except ParseError as e:
                raise ParseError(f"{invariants_path}:{lineno}: {e}\n  line: {raw.rstrip()}") from e

    domains: Dict[SortRef, List[ExprRef]] = {}
    if decls["NodeSort"] is not None:
        domains[decls["NodeSort"]] = decls["nodes"]
    if decls["EpochSort"] is not None:
        domains[decls["EpochSort"]] = decls["epochs"]

    invs_ground: List[ExprRef] = [ground_invariant(pi, domains) for pi in parsed_invs]

    print(f"Atoms: {len(atoms_z3)}")
    print(f"Reachable states (bitstrings): {len(reachable_bits)}")
    print(f"Invariants (lines): {len(parsed_invs)}")
    print(f"Invariants (grounded): {len(invs_ground)}")
    print()

    # 1) Check reachable states vs invariants
    bad_states: List[Tuple[int, List[int]]] = []
    for si, bits in enumerate(reachable_bits):
        s = Solver()
        s.add(bitstring_to_constraints(atoms_z3, bits))
        if interpreted_constraints:
            s.add(interpreted_constraints)
        violated = []
        for ii, inv in enumerate(invs_ground):
            s.push()
            s.add(Not(inv))
            if s.check() == sat:
                violated.append(ii)
            s.pop()
        if violated:
            bad_states.append((si, violated))

    if not bad_states:
        print("All reachable states satisfy all invariants.")
    else:
        print("Some reachable states violate invariants:")
        for si, violated in bad_states[:20]:
            print(f"  state[{si}] violates invariants: {violated}")
        if len(bad_states) > 20:
            print(f"  (showing first 20 of {len(bad_states)})")

    print()

    # 2) Find spurious states: satisfy invariants but not in reachable list
    if spurious_limit > 0:
        base = Solver()
        base.add(invs_ground)
        if interpreted_constraints:
            base.add(interpreted_constraints)

        # Exclude all known reachable valuations
        for bits in reachable_bits:
            base.add(exclude_bitstring(atoms_z3, bits))

        spurious: List[str] = []
        while len(spurious) < spurious_limit and base.check() == sat:
            m = base.model()
            b = model_to_bitstring(m, atoms_z3)
            spurious.append(b)
            base.add(exclude_bitstring(atoms_z3, b))

        if not spurious:
            print("No spurious states found (within this atom vocabulary).")
        else:
            print(f"Spurious states found (up to {spurious_limit}): {len(spurious)}")
            for i, b in enumerate(spurious, start=1):
                true_atoms = [atoms[j] for j, bit in enumerate(b) if bit == "1"]
                print(f"\n  spurious[{i}] bits: {b}")
                print(f"  true atoms ({len(true_atoms)}): {true_atoms}")

if __name__ == "__main__":
    import argparse

    ap = argparse.ArgumentParser()
    ap.add_argument("invariants_file", help="Text file, one invariant per line")
    ap.add_argument("states_file", help="File containing 'state atoms: [...]' and bitstrings")
    ap.add_argument("--spurious-limit", type=int, default=10, help="How many spurious states to enumerate (0 disables)")
    args = ap.parse_args()

    main(args.invariants_file, args.states_file, spurious_limit=args.spurious_limit)
