#!/usr/bin/env python3
"""Convert orbit/group assignments into SMT-LIB group assertions.

Input format:
  One assignment per line: <orbit_id> <group_id>
  Example:
	0 0
	7 0
	1 1

Output format (SMT2):
  (assert (= G0 (and R0 R7)))
  (assert (= G1 (and R1)))
"""

from __future__ import annotations

import argparse
from collections import defaultdict
from pathlib import Path


def parse_assignments(input_path: Path) -> dict[str, list[str]]:
	"""Parse orbit->group assignments into group->orbit-symbols."""
	groups: dict[str, list[str]] = defaultdict(list)

	for line_no, raw in enumerate(input_path.read_text(encoding="utf-8").splitlines(), start=1):
		line = raw.strip()
		if not line or line.startswith("#"):
			continue

		parts = line.split()
		if len(parts) < 2:
			raise ValueError(
				f"Invalid input at line {line_no}: expected '<orbit_id> <group_id>', got '{raw}'"
			)

		orbit_id, group_id = parts[0], parts[1]
		groups[group_id].append(orbit_id)

	return groups


def _sort_key(val: str) -> tuple[int, int | str]:
	"""Sort numerically when possible, then lexicographically."""
	try:
		return (0, int(val))
	except ValueError:
		return (1, val)


def build_smt2(groups: dict[str, list[str]], group_prefix: str, orbit_prefix: str) -> str:
	"""Build SMT2 assertions for each group."""
	lines: list[str] = []

	for group_id in sorted(groups.keys(), key=_sort_key):
		orbit_ids = sorted(groups[group_id], key=_sort_key)
		orbit_symbols = [f"{orbit_prefix}{oid}" for oid in orbit_ids]
		rhs = f"(and {' '.join(orbit_symbols)})"
		lines.append(f"(assert (= {group_prefix}{group_id} {rhs}))")

	return "\n".join(lines) + ("\n" if lines else "")


def main() -> None:
	parser = argparse.ArgumentParser(
		description="Generate SMT2 group assertions from orbit/group assignments."
	)
	parser.add_argument("input", type=Path, help="Path to orbit_to_groups-style text file")
	parser.add_argument(
		"-o",
		"--output",
		type=Path,
		default=None,
		help="Output SMT2 file path (defaults to stdout)",
	)
	parser.add_argument(
		"--group-prefix",
		default="G",
		help="Prefix for group symbols (default: G)",
	)
	parser.add_argument(
		"--orbit-prefix",
		default="R",
		help="Prefix for orbit symbols (default: R)",
	)
	args = parser.parse_args()

	groups = parse_assignments(args.input)
	smt2 = build_smt2(groups, args.group_prefix, args.orbit_prefix)

	if args.output is None:
		print(smt2, end="")
	else:
		args.output.write_text(smt2, encoding="utf-8")


if __name__ == "__main__":
	main()
