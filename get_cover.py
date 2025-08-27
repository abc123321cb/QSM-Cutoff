#This is a seperate file to get cover of the non converging orbits.

#!/usr/bin/env python3


from __future__ import annotations
from pathlib import Path
import re
from typing import Dict, List, Set, Tuple, Iterable, Optional
from itertools import product
import argparse

# ---------------------------
# Parsing
# ---------------------------

import ast
import re
from itertools import permutations  # you'll use this below for symmetry

_NODE_RE = re.compile(r'\((?:node)?(\d+)\)')
STATE_ATOMS_RE = re.compile(r'^\s*state\s*atoms\s*:\s*(\[.+\])\s*$',
                            flags=re.IGNORECASE | re.MULTILINE)

def parse_state_atoms_from_text(text: str) -> list[str] | None:
    """
    Looks for a line like:
        state atoms: ['p(node0)', 'p(node1)', ..., 'q(node3)']
    Returns the list of strings if found, else None.
    """
    m = STATE_ATOMS_RE.search(text)
    if not m:
        return None
    payload = m.group(1)
    try:
        atoms = ast.literal_eval(payload)
        if isinstance(atoms, list) and all(isinstance(x, str) for x in atoms):
            return atoms
    except Exception:
        pass
    # Fallback parser (very forgiving)
    inner = payload.strip()[1:-1]
    atoms = [s.strip().strip("'\"") for s in inner.split(',') if s.strip()]
    return atoms if atoms else None


def parse_prime_orbit_file(path: str | Path) -> Tuple[List[str], Dict[int, List[str]], Dict[int, List[str]], Optional[List[str]]]:
    """
    Returns:
        reachable: list of bitstrings
        subset1:   {orbit_id: [cube_bitpattern, ...]}    # Converging
        subset2:   {orbit_id: [cube_bitpattern, ...]}    # Diverging
        state_atoms: list[str] parsed from 'state atoms: [...]' if present, else None
    """
    text = Path(path).read_text()
    state_atoms = parse_state_atoms_from_text(text)  # <-- NEW

    lines = text.splitlines()
    reachable: List[str] = []
    subset1: Dict[int, List[str]] = {}
    subset2: Dict[int, List[str]] = {}
    n = len(lines)
    i = 0

    # reachable section (case-insensitive "reachable")
    while i < n and not lines[i].strip().lower().startswith('reachable'):
        i += 1
    i += 1  # skip the 'reachable' header line
    # collect bitstrings until a blank line
    while i < n and lines[i].strip():
        s = lines[i].strip()
        if re.fullmatch(r'[01-]+', s):
            reachable.append(s)
        i += 1
    bitlen = len(reachable[0]) if reachable else None

    cube_line_re = re.compile(r'^\s*\d+\s*(?:\(\*\))?\s*:\s*([01-]+)\s*$')

    def parse_subset(idx: int, out: Dict[int, List[str]]) -> int:
        i = idx
        while i < n:
            line = lines[i].strip()
            if line.startswith('=== Prime Orbit'):
                m = re.search(r'Prime Orbit\s+(\d+)', line)
                oid = int(m.group(1)) if m else None
                i += 1
                cubes: List[str] = []
                while i < n:
                    s = lines[i].rstrip()
                    st = s.strip()
                    if not st:
                        break
                    if st.startswith('=== Prime Orbit') or st.startswith('Subset') or st.lower().startswith('reachable') or st.startswith('Converging') or st.startswith('Diverging'):
                        break
                    m2 = cube_line_re.fullmatch(s)
                    if m2:
                        patt = m2.group(1)
                        if bitlen is None or len(patt) == bitlen:
                            cubes.append(patt)
                    i += 1
                if oid is not None:
                    out[oid] = cubes
            elif line.startswith('Diverging') or line.startswith('Converging') or line.lower().startswith('reachable'):
                break
            else:
                i += 1
        return i

    # subset1 (Converging)
    while i < n and not lines[i].strip().startswith('Converging'):
        i += 1
    i += 1
    i = parse_subset(i, subset1)

    # subset2 (Diverging)
    while i < n and not lines[i].strip().startswith('Diverging'):
        i += 1
    i += 1
    i = parse_subset(i, subset2)

    return reachable, subset1, subset2, state_atoms  # <-- NEW

def _atoms_info(state_atoms: List[str]) -> Tuple[List[Tuple[Optional[str], Optional[int]]],
                                                 List[int],
                                                 Dict[Tuple[Optional[str], Optional[int]], int]]:
    """
    Returns:
      info: [(predicate_name, node_index_or_None)] in bit order
      nodes: sorted list of node indices we found
      pos: {(predicate, node): bit_position}
    Atoms without a node index (if any) are treated as fixed under permutation.
    """
    info: List[Tuple[Optional[str], Optional[int]]] = []
    nodes: Set[int] = set()
    pos: Dict[Tuple[Optional[str], Optional[int]], int] = {}

    for idx, a in enumerate(state_atoms):
        # predicate name is the token before '(' with optional leading '~' stripped
        pred = a.lstrip('~').split('(', 1)[0].strip() if '(' in a else a.lstrip('~').strip()
        m = _NODE_RE.search(a)
        node = int(m.group(1)) if m else None
        info.append((pred, node))
        pos[(pred, node)] = idx
        if node is not None:
            nodes.add(node)

    return info, sorted(nodes), pos


def canonicalize_state(bits: str, state_atoms: List[str]) -> str:
    """
    Apply all node-index permutations to 'bits' (in the order of 'state_atoms') and
    return the lexicographically smallest image.
    """
    info, nodes, pos = _atoms_info(state_atoms)
    if not nodes:
        return bits  # nothing to permute

    best: Optional[str] = None
    for perm in permutations(nodes):  # e.g., 24 perms for 4 nodes
        node_map = {nodes[i]: perm[i] for i in range(len(nodes))}
        out = ['0'] * len(bits)
        for src_idx, (pred, node) in enumerate(info):
            if node is None:
                dst_idx = src_idx  # fixed atom
            else:
                dst_idx = pos[(pred, node_map[node])]
            out[dst_idx] = bits[src_idx]
        cand = ''.join(out)
        if best is None or cand < best:
            best = cand
    return best  # type: ignore


def collapse_states(states: Iterable[str], state_atoms: List[str]) -> Set[str]:
    """
    Map each state to its canonical representative under node permutations,
    and return the deduped set of representatives.
    """
    return {canonicalize_state(s, state_atoms) for s in states}


def enum_states_by_pysat(cubes: Iterable[str], bitlen: int) -> Optional[Set[str]]:
    """Enumerate minterms using sat."""
    try:
        from pysat.solvers import Minisat22
    except Exception:
        return None
    s = Minisat22()

    states: Set[str] = set()

    for cube in cubes:
        clause = []
        for i, ch in enumerate(cube, start=1):
            if ch == '1':
                clause.append(-i)
            elif ch == '0':
                clause.append(i)
        if clause:
            s.add_clause(clause)
   
    states: Set[str] = set()
    while s.solve():
        model = s.get_model()
        bits = ''.join('1' if model[i - 1] > 0 else '0' for i in range(1, bitlen + 1))
        if bits not in states:
            states.add(bits)
        # Block this assignment
        s.add_clause([-i if model[i - 1] > 0 else i for i in range(1, bitlen + 1)])

    return states

def union_states(cube_dict: Dict[int, List[str]], bitlen: int) -> Dict[int, Set[str]]:
    """For each orbit -> list[cube], compute orbit -> set[minterm bitstrings] (union over its cubes)."""
    out: Dict[int, Set[str]] = {}
    for oid, cubes in cube_dict.items():
        sat_res = enum_states_by_pysat(cubes, bitlen)
        if sat_res is not None:
            out[oid] = sat_res
    return out

def main(path: str | Path, prefer_sat: bool = True):
    reachable, subset1_raw, subset2_raw, state_atoms = parse_prime_orbit_file(path)
    if not reachable:
        raise RuntimeError("No reachable states found in file.")
    bitlen = len(reachable[0])
    reachable_set = set(reachable)

    print("Reachable states: ")
    for s in sorted(reachable_set):
        print(f"  {s}")
    print(f"Total reachable states: {len(reachable_set)}")

    print(f"Converging orbits: {len(subset1_raw)}")
    print(f"Diverging orbits: {len(subset2_raw)}")

    # gives a set of states per orbit each set is a superset of the reachable states
    temp_Converging_states = union_states(subset1_raw, bitlen)
    Diverging_states = union_states(subset2_raw, bitlen)
    Converging_states= set.intersection(*temp_Converging_states.values()) - reachable_set

    print(f"All {len(Converging_states)} unreachable states in Converging orbits:")
    for s in Converging_states:
        print(f"  {s}")

    for key in Diverging_states.keys():
        Diverging_states[key] = Converging_states - Diverging_states[key]
        print(f"Diverging orbit {key} blocks {len(Diverging_states[key])} unreachable states.", end="\n  ")
        print(f"\n  ".join(sorted(Diverging_states[key])))

    Converging_states = collapse_states(Converging_states, state_atoms)
    for k in list(Diverging_states.keys()):
        Diverging_states[k] = collapse_states(Diverging_states[k], state_atoms)
    
    print(f"There are {len(Converging_states)} unreachable orbits in the Converging prime orbits.")
    for s in sorted(Converging_states):
        print(f"  {s}")
    
    print("Diverging orbits blocking unreachable states:")
    for key in Diverging_states.keys():
        print(f"Diverging orbit {key} blocks {len(Diverging_states[key])} unreachable states.", end="\n  ")
        print(f"\n  ".join(sorted(Diverging_states[key])))

    return

if __name__ == "__main__":
    ap = argparse.ArgumentParser(
        description="For each Subset2 orbit o2, list states satisfying (in Subset1) ∧ (¬reachable) ∧ (¬ in o2)."
    )
    ap.add_argument("file", help="Input txt like Prime_orbit_in.txt")
    args = ap.parse_args()

    main(args.file)
