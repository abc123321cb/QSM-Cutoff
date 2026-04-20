#!/usr/bin/env python3
import os
import ast
import itertools
import re
from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple, Any

try:
    # Typical `z3-solver` layout
    from z3 import (
        And, Or, Not, BoolSort, EnumSort, Function, Const, Bool,
        Solver, substitute, sat, ExprRef, FuncDeclRef, SortRef,
    )
except ImportError:
    # Some environments install a `z3` package that exposes these via `z3.z3`.
    from z3.z3 import (
        And, Or, Not, BoolSort, EnumSort, Function, Const, Bool,
        Solver, substitute, sat, ExprRef, FuncDeclRef, SortRef,
    )


def _collect_balanced_sexpr(lines: List[str], start_index: int) -> Tuple[str, int]:
    """Collect a balanced SMT-LIB2 s-expression starting at lines[start_index].

    Returns (sexpr_text, next_index_after_consumed).
    """
    depth = 0
    collected: List[str] = []
    i = start_index
    while i < len(lines):
        line = lines[i]
        collected.append(line)
        depth += line.count("(")
        depth -= line.count(")")
        i += 1
        if depth == 0:
            break
    return "".join(collected), i


def _tokenize_sexpr(s: str) -> List[str]:
    # Minimal SMT-LIB2 S-expression tokenizer for Z3's `to_smt2()` output.
    # Handles parentheses, symbols, numerals, and quoted strings (rare in our asserts).
    out: List[str] = []
    i = 0
    n = len(s)
    while i < n:
        ch = s[i]
        if ch.isspace():
            i += 1
            continue
        if ch == ";":
            # comment to end of line
            while i < n and s[i] != "\n":
                i += 1
            continue
        if ch in ("(", ")"):
            out.append(ch)
            i += 1
            continue
        if ch == '"':
            j = i + 1
            while j < n:
                if s[j] == '"':
                    j += 1
                    break
                # SMT-LIB escapes quotes by doubling them
                if s[j] == '"' and j + 1 < n and s[j + 1] == '"':
                    j += 2
                    continue
                j += 1
            out.append(s[i:j])
            i = j
            continue

        j = i
        while j < n and (not s[j].isspace()) and s[j] not in ("(", ")", ";"):
            j += 1
        out.append(s[i:j])
        i = j
    return out


def _parse_sexpr_tokens(tokens: List[str]) -> Any:
    def parse_at(k: int) -> Tuple[Any, int]:
        if k >= len(tokens):
            raise ValueError("Unexpected end of tokens")
        t = tokens[k]
        if t == "(":
            k += 1
            items: List[Any] = []
            while True:
                if k >= len(tokens):
                    raise ValueError("Unclosed '('")
                if tokens[k] == ")":
                    k += 1
                    return items, k
                item, k = parse_at(k)
                items.append(item)
        if t == ")":
            raise ValueError("Unexpected ')'")
        return t, k + 1

    expr, next_k = parse_at(0)
    if next_k != len(tokens):
        raise ValueError("Extra tokens after s-expression")
    return expr


def _inline_lets(expr: Any, env: Optional[Dict[str, Any]] = None) -> Any:
    """Inline/eliminate SMT-LIB2 (let ((x t)) body) bindings.

    This is a best-effort inliner intended for Z3's pretty-printed `let` chains.
    """
    if env is None:
        env = {}

    if isinstance(expr, str):
        return env.get(expr, expr)

    if not isinstance(expr, list) or not expr:
        return expr

    head = expr[0]
    if head == "let" and len(expr) == 3 and isinstance(expr[1], list):
        bindings = expr[1]
        body = expr[2]
        new_env = dict(env)

        # SMT-LIB2 let-bindings are (nominally) simultaneous: binding expressions
        # should not see the newly-bound names, so we rewrite them using `env`.
        for b in bindings:
            if not (isinstance(b, list) and len(b) == 2 and isinstance(b[0], str)):
                return [_inline_lets(x, env) for x in expr]
            var, val = b[0], b[1]
            new_env[var] = _inline_lets(val, env)

        return _inline_lets(body, new_env)

    return [_inline_lets(x, env) for x in expr]


def _sexpr_to_oneline(expr: Any) -> str:
    """Render an s-expression on a single line (no pretty indentation)."""
    if isinstance(expr, str):
        return expr
    if not isinstance(expr, list):
        return str(expr)
    return "(" + " ".join(_sexpr_to_oneline(x) for x in expr) + ")"

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

    def rep_ep_curried(m):
        k = m.group(1)
        v = m.group(2)
        return f"ep({v})=epoch{k}"

    line = re.sub(r"\blocked_epoch(\d+)\(\s*([A-Za-z_][A-Za-z0-9_]*)\s*\)", rep_locked, line)
    line = re.sub(r"\btransfer_epoch(\d+)\(\s*([A-Za-z_][A-Za-z0-9_]*)\s*\)", rep_transfer, line)
    line = re.sub(r"\bep\s*=\s*_epoch(\d+)\(\s*([A-Za-z_][A-Za-z0-9_]*)\s*\)", rep_ep_epoch, line)
    line = re.sub(r"\bep_epoch(\d+)\(\s*([A-Za-z_][A-Za-z0-9_]*)\s*\)", rep_ep_curried, line)

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
        # Common short variable conventions in orbit files
        if self.NodeSort is not None and re.fullmatch(r"N\d+", up) is not None:
            return self.NodeSort
        if self.EpochSort is not None and re.fullmatch(r"E\d+", up) is not None:
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
            # Support multiple quantifier blocks, either comma-separated or dot-separated, e.g.:
            #   forall N0,N1. forall E0,E1. <body>
            #   forall EPOCH0, exists NODE0. <body>
            while self._peek() in ("forall", "exists"):
                q = self._pop()
                vars_out = self._parse_varlist_until_quant_or_dot()
                if not vars_out:
                    raise ParseError("Empty quantified variable list")
                quant_blocks.append((q, vars_out))

                if self._accept(","):
                    continue
                if self._accept("."):
                    # If another quantifier immediately follows, keep reading quant blocks.
                    if self._peek() in ("forall", "exists"):
                        continue
                    break
                raise ParseError(f"Expected ',' or '.' after quantified variables, got '{self._peek()}'")

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


def _normalize_dump_path(dump_path: str, invariants_path: str) -> str:
    """Normalize the user's requested SMT dump path.

    Supports:
    - Passing a directory path (existing dir or ending with a path separator): writes
      to that directory using a default filename.
    - Passing a bare filename: writes next to the invariants file for stability
      regardless of current working directory.
    - Avoids the common pitfall: running inside directory X and passing "X/out.smt2"
      (which would otherwise create nested X/X/out.smt2).
    """
    default_name = "orbits_minus_reach.smt2"

    # If user passed a directory (or indicated one with a trailing slash), write into it.
    if dump_path.endswith(os.sep) or (os.path.exists(dump_path) and os.path.isdir(dump_path)):
        return os.path.join(dump_path, default_name)

    # If user passed something like "z3-checking/out.smt2" while already in "z3-checking",
    # interpret it as "out.smt2" to avoid creating a nested directory.
    if not os.path.isabs(dump_path):
        parts = dump_path.split(os.sep)
        if len(parts) >= 2:
            cwd_base = os.path.basename(os.getcwd())
            first = parts[0]
            nested_dir = os.path.join(os.getcwd(), first)
            if first == cwd_base and not os.path.exists(nested_dir):
                dump_path = os.sep.join(parts[1:])

    # If it's just a filename, put it next to the invariants file.
    if not os.path.isabs(dump_path) and os.path.dirname(dump_path) == "":
        inv_dir = os.path.dirname(os.path.abspath(invariants_path))
        return os.path.join(inv_dir, dump_path)

    return dump_path

def main(
    invariants_path: str,
    states_path: str,
    spurious_limit: int = 10,
    debug_rewrite: bool = False,
    debug_rewrite_all: bool = False,
    debug_rewrite_limit: int = 200,
    dump_orbits_minus_reach: Optional[str] = None,
) -> None:
    atoms, reachable_bits, interpreted_atoms = read_states_file(states_path)
    node_names, epoch_names = extract_domain_constants(atoms)

    parser = Z3ClauseParser(node_names=node_names, epoch_names=epoch_names)
    decls = parser.declarations()

    # Parse state atoms into Z3 expressions (in a fixed order)
    atoms_z3: List[ExprRef] = [parser.parse_atom(a) for a in atoms]

    # Fixed constraints from interpreted atoms (e.g., le(epochi,epochj), (zero=epoch0), ...)
    interpreted_constraints: List[ExprRef] = []
    interpreted_meta: List[Tuple[str, str]] = []
    for atom_str, bit in interpreted_atoms.items():
        try:
            a = parser.parse_atom(atom_str)
        except Exception as e:
            raise ParseError(f"Could not parse interpreted atom '{atom_str}': {e}") from e
        interpreted_constraints.append(a if str(bit) == "1" else Not(a))
        interpreted_meta.append((atom_str, str(bit)))

    # Parse and ground invariants
    parsed_invs: List[ParsedInvariant] = []
    # Each parsed invariant corresponds to one SMT `(assert ...)` emitted by `base.to_smt2()`.
    # We keep metadata so SMT dumps can comment which orbit line produced which assert.
    # Format supports both legacy files (one formula per line) and grouped files like:
    #   F3
    #   10: forall N. ...
    # Group headers are non-formula lines like "F1" or "E2".
    inv_meta: List[Tuple[int, Optional[str], Optional[int], str, str, str]] = []
    # (lineno, group, orbit_id, source_line, formula, rewritten)
    rewrite_printed = 0
    current_group: Optional[str] = None
    with open(invariants_path, "r", encoding="utf-8") as f:
        for lineno, raw in enumerate(f, start=1):
            source_line = raw.strip()
            if not source_line or source_line.startswith("#") or source_line.startswith(";"):
                continue

            # Group header line (e.g., "F1", "E2")
            # Be conservative to avoid breaking legacy files that might contain a bare boolean constant.
            if re.fullmatch(r"[A-Za-z]\d+", source_line) and source_line[0].upper() in ("F", "E"):
                current_group = source_line
                continue

            orbit_id: Optional[int] = None
            formula = source_line

            # Optional numeric prefix like "10: <formula>" or "10; <formula>".
            m = re.match(r"^(\d+)\s*[:;]\s*(.+)$", source_line)
            if m:
                orbit_id = int(m.group(1))
                formula = m.group(2).strip()

            rewritten = rewrite_invariant_line(formula)
            inv_meta.append((lineno, current_group, orbit_id, source_line, formula, rewritten))

            if debug_rewrite and (debug_rewrite_all or rewritten != formula):
                if debug_rewrite_limit < 0:
                    # treat negative as "no limit"
                    pass
                if debug_rewrite_limit == 0 or rewrite_printed < debug_rewrite_limit:
                    if rewritten == formula:
                        print(f"[REWRITE:{lineno}] {rewritten}")
                    else:
                        print(f"[REWRITE:{lineno}] {formula}  ==>  {rewritten}")
                    rewrite_printed += 1
            try:
                parsed_invs.append(parser.parse_invariant_line(rewritten))
            except ParseError as e:
                raise ParseError(f"{invariants_path}:{lineno}: {e}\n  line: {raw.rstrip()}") from e

    if debug_rewrite and debug_rewrite_limit != 0 and rewrite_printed >= debug_rewrite_limit:
        print(f"[REWRITE] printed first {rewrite_printed} rewritten lines (limit reached)")

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
    if spurious_limit > 0 or dump_orbits_minus_reach is not None:
        base = Solver()
        base.add(invs_ground)
        if interpreted_constraints:
            base.add(interpreted_constraints)

        # Exclude all known reachable valuations
        for bits in reachable_bits:
            base.add(exclude_bitstring(atoms_z3, bits))

        if dump_orbits_minus_reach is not None:
            dump_orbits_minus_reach = _normalize_dump_path(dump_orbits_minus_reach, invariants_path)
            smt2 = base.to_smt2()
            lines = smt2.splitlines(keepends=True)

            out_lines: List[str] = []
            asserted_orbits = 0
            assert_count = 0
            reach_header_written = False
            interpreted_header_written = False
            reach_start_assert_index = len(inv_meta) + len(interpreted_constraints)
            last_group_emitted: Optional[str] = None
            interpreted_start_assert_index = len(inv_meta)

            pending_group: Optional[str] = None
            pending_group_exprs: List[Any] = []
            group_var_assert_lines: List[str] = []
            group_var_asserts_emitted = False

            def _flush_pending_group() -> None:
                nonlocal pending_group, pending_group_exprs
                if pending_group is None:
                    return

                def _flatten_and(exprs: List[Any]) -> List[Any]:
                    flat: List[Any] = []
                    for e in exprs:
                        if isinstance(e, list) and len(e) >= 1 and e[0] == "and":
                            flat.extend(e[1:])
                        else:
                            flat.append(e)
                    return flat

                group_label = pending_group if pending_group is not None else "(ungrouped)"
                safe = re.sub(r"[^A-Za-z0-9_]", "_", group_label)
                if not safe or safe[0].isdigit():
                    safe = "G_" + safe
                var = f"orbit_group_{safe}"

                out_lines.append(f"(declare-fun {var} () Bool)\n")

                exprs = _flatten_and(pending_group_exprs)
                if len(exprs) == 1:
                    body = exprs[0]
                else:
                    body = ["and", *exprs]
                out_lines.append(_sexpr_to_oneline(["assert", ["=", var, body]]) + "\n")
                group_var_assert_lines.append(_sexpr_to_oneline(["assert", var]) + "\n")

                pending_group = None
                pending_group_exprs = []

            i = 0
            while i < len(lines):
                line = lines[i]

                # Emit all group-variable asserts right before check-sat.
                if (not group_var_asserts_emitted) and re.match(r"^\s*\(check-sat\b", line):
                    _flush_pending_group()
                    if group_var_assert_lines:
                        if out_lines and out_lines[-1] != "\n":
                            out_lines.append("\n")
                        out_lines.append(
                            f"; --- orbit-group variables asserted true: {len(group_var_assert_lines)} groups ---\n"
                        )
                        out_lines.extend(group_var_assert_lines)
                        out_lines.append("\n")
                    group_var_asserts_emitted = True

                if re.match(r"^\s*\(assert\b", line):
                    # The `to_smt2()` stream is:
                    #   [orbit asserts] + [interpreted asserts] + [reachable exclusions] + (check-sat)
                    # Before entering non-orbit sections, flush the last orbit group.
                    if assert_count == interpreted_start_assert_index:
                        _flush_pending_group()

                    if (
                        (not interpreted_header_written)
                        and len(interpreted_constraints) > 0
                        and assert_count == interpreted_start_assert_index
                    ):
                        if out_lines and out_lines[-1] != "\n":
                            out_lines.append("\n")
                        out_lines.append(
                            f"; --- interpreted atoms begin: {len(interpreted_constraints)} constraints ---\n"
                        )
                        interpreted_header_written = True

                    if (not reach_header_written) and assert_count == reach_start_assert_index:
                        if out_lines and out_lines[-1] != "\n":
                            out_lines.append("\n")
                        out_lines.append(
                            f"; --- reachable state exclusions begin: excluding {len(reachable_bits)} reachable states ---\n"
                        )
                        reach_header_written = True

                    # Label reachable exclusions with their original reachable-state index.
                    # These asserts are emitted after invariants + interpreted constraints.
                    if assert_count >= reach_start_assert_index:
                        reach_i = assert_count - reach_start_assert_index
                        if 0 <= reach_i < len(reachable_bits):
                            out_lines.append(f"; reachable[{reach_i}] bits: {reachable_bits[reach_i]}\n")

                    # Label interpreted-atom asserts so it's easy to map them back to `reach.txt`.
                    if len(interpreted_constraints) > 0 and interpreted_start_assert_index <= assert_count < reach_start_assert_index:
                        interp_i = assert_count - interpreted_start_assert_index
                        if 0 <= interp_i < len(interpreted_meta):
                            atom_str, bit = interpreted_meta[interp_i]
                            out_lines.append(f"; interpreted[{interp_i}] {atom_str} = {bit}\n")

                    # ORBIT ASSERTS: collect into a per-group AND and assert that group variable.
                    if assert_count < interpreted_start_assert_index:
                        (
                            src_lineno,
                            group,
                            orbit_id,
                            source_line,
                            formula,
                            rewritten,
                        ) = inv_meta[asserted_orbits]

                        # Group changed -> flush previous group's variable definition/asserts.
                        if group != pending_group and pending_group is not None:
                            _flush_pending_group()

                        # Emit a group header (with a blank line) when the group changes.
                        if group != last_group_emitted:
                            # Insert exactly one blank line *between* groups (not before the first).
                            if last_group_emitted is not None:
                                if out_lines and out_lines[-1] != "\n":
                                    out_lines.append("\n")
                            group_label = group if group is not None else "(ungrouped)"
                            out_lines.append(f"; ===== Orbit Group {group_label} =====\n")
                            last_group_emitted = group

                        # Orbit comment format: just "#: <FOL statement>".
                        if orbit_id is not None:
                            out_lines.append(f"; {orbit_id}: {formula}\n")
                        else:
                            out_lines.append(f"; {asserted_orbits + 1}: {formula}\n")

                        # Parse the assert, inline lets, and store its body into this group's AND.
                        assert_text, next_i = _collect_balanced_sexpr(lines, i)
                        try:
                            tokens = _tokenize_sexpr(assert_text)
                            sexpr = _parse_sexpr_tokens(tokens)
                            sexpr_inlined = _inline_lets(sexpr)
                            if isinstance(sexpr_inlined, list) and len(sexpr_inlined) == 2 and sexpr_inlined[0] == "assert":
                                pending_group = group
                                pending_group_exprs.append(sexpr_inlined[1])
                            else:
                                # Unexpected shape; fall back to emitting original.
                                _flush_pending_group()
                                out_lines.append(assert_text)
                        except Exception:
                            _flush_pending_group()
                            out_lines.append(assert_text)

                        asserted_orbits += 1
                        i = next_i
                        assert_count += 1
                        continue

                    # NON-ORBIT ASSERTS: emit as single-line (still with labels above).
                    assert_text, next_i = _collect_balanced_sexpr(lines, i)
                    try:
                        tokens = _tokenize_sexpr(assert_text)
                        sexpr = _parse_sexpr_tokens(tokens)
                        sexpr_inlined = _inline_lets(sexpr)
                        out_lines.append(_sexpr_to_oneline(sexpr_inlined) + "\n")
                    except Exception:
                        out_lines.append(assert_text)

                    i = next_i
                    assert_count += 1
                    continue

                out_lines.append(line)
                i += 1

            # If the SMT2 ended without transitioning to interpreted/reachable, flush any pending orbit group.
            _flush_pending_group()

            # If we never saw (check-sat), still emit group-variable asserts at the end.
            if (not group_var_asserts_emitted) and group_var_assert_lines:
                if out_lines and out_lines[-1] != "\n":
                    out_lines.append("\n")
                out_lines.append(
                    f"; --- orbit-group variables asserted true: {len(group_var_assert_lines)} groups ---\n"
                )
                out_lines.extend(group_var_assert_lines)

            out_dir = os.path.dirname(dump_orbits_minus_reach)
            if out_dir:
                os.makedirs(out_dir, exist_ok=True)
            with open(dump_orbits_minus_reach, "w", encoding="utf-8") as out:
                out.writelines(out_lines)
            print(f"Wrote SMT2 to {dump_orbits_minus_reach}")
            if spurious_limit <= 0:
                return

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
    ap.add_argument(
        "--dump-orbits-minus-reach",
        nargs="?",
        const="orbits_minus_reach.smt2",
        default=None,
        help="Write SMT-LIB2 for (invariants ∧ interpreted ∧ ¬reachable) to this file",
    )
    ap.add_argument(
        "--debug-rewrite",
        action="store_true",
        help="Print invariant lines after rewrite/uncurrying (only when changed)",
    )
    ap.add_argument(
        "--debug-rewrite-all",
        action="store_true",
        help="Print rewritten invariants even if unchanged",
    )
    ap.add_argument(
        "--debug-rewrite-limit",
        type=int,
        default=200,
        help="Max rewritten lines to print (0=all, negative=no limit)",
    )
    args = ap.parse_args()

    main(
        args.invariants_file,
        args.states_file,
        spurious_limit=args.spurious_limit,
        debug_rewrite=args.debug_rewrite,
        debug_rewrite_all=args.debug_rewrite_all,
        debug_rewrite_limit=args.debug_rewrite_limit,
        dump_orbits_minus_reach=args.dump_orbits_minus_reach,
    )
