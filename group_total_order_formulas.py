import re
from collections import defaultdict
from pathlib import Path

def normalize_formula(formula):
    """
    Normalize a formula by:
    1. Replacing node and epoch numbers with placeholders
    2. Sorting literals in OR clauses (since OR is commutative)
    E.g., 'NODE0', 'NODE1' -> 'NODE#', 'epoch0', 'epoch1' -> 'epoch#'
    """
    # Replace NODE followed by digits
    normalized = re.sub(r'NODE\d+', 'NODE#', formula)
    # Replace epoch followed by digits
    normalized = re.sub(r'epoch\d+', 'epoch#', normalized)
    
    # Canonicalize by sorting top-level OR literals
    # Split on ' | ' but preserve nested expressions in parentheses
    normalized = canonicalize_disjunction(normalized)
    
    return normalized

def canonicalize_disjunction(formula):
    """
    Sort literals in OR clauses to handle commutativity.
    Handles nested parentheses by only sorting at the appropriate level.
    """
    # Split formula into parts, keeping track of parenthesis depth
    parts = []
    current = []
    depth = 0
    i = 0
    
    while i < len(formula):
        if formula[i] == '(':
            depth += 1
            current.append(formula[i])
        elif formula[i] == ')':
            depth -= 1
            current.append(formula[i])
        elif depth == 0 and i + 3 <= len(formula) and formula[i:i+3] == ' | ':
            # Found a top-level OR separator
            parts.append(''.join(current))
            current = []
            i += 2  # skip the ' | ', will increment by 1 at end of loop
        else:
            current.append(formula[i])
        i += 1
    
    # Add the last part
    if current:
        parts.append(''.join(current))
    
    # Sort the parts and rejoin
    if len(parts) > 1:
        parts.sort()
        return ' | '.join(parts)
    else:
        return formula

def group_formulas(input_file):
    """
    Read formulas from input file and group them by structure.
    Returns a dict mapping normalized form to list of (line_num, original_formula) tuples.
    """
    groups = defaultdict(list)
    
    with open(input_file, 'r') as f:
        for line_num, line in enumerate(f, start=1):
            formula = line.strip()
            if not formula:
                continue
            
            normalized = normalize_formula(formula)
            groups[normalized].append((line_num, formula))
    
    return groups

def print_groups(groups):
    """
    Print the grouped formulas in a readable format.
    """
    # Sort groups by size (smallest first) then by structure length (shortest first)
    sorted_groups = sorted(groups.items(), key=lambda x: (len(x[1]), len(x[0]), x[0]))
    
    print(f"Total unique formula structures: {len(sorted_groups)}\n")
    print("=" * 80)
    
    for group_id, (normalized, formulas) in enumerate(sorted_groups, start=1):
        print(f"\n### Orbit group {group_id} ({len(formulas)} formulas) ###")
        print(f"Structure: {normalized}")
        print(f"Prime orbits: {[line_num for line_num, _ in formulas]}")
        print("\nFormulas:")
        for line_num, formula in formulas:
            print(f"  [{line_num:3d}] {formula}")
        print("-" * 80)

def export_to_file(groups, output_file):
    """
    Export grouped formulas to a file.
    """
    # Sort groups by size (smallest first) then by structure length (shortest first)
    sorted_groups = sorted(groups.items(), key=lambda x: (len(x[1]), len(x[0]), x[0]))
    
    with open(output_file, 'w') as f:
        f.write(f"Total unique formula structures: {len(sorted_groups)}\n\n")
        
        for group_id, (normalized, formulas) in enumerate(sorted_groups, start=1):
            f.write(f"=== Orbit group {group_id} ===\n")
            f.write(f"Size: {len(formulas)}\n")
            f.write(f"Structure: {normalized}\n")
            f.write(f"Prime orbits: {[line_num for line_num, _ in formulas]}\n")
            f.write("\nFormulas:\n")
            for line_num, formula in formulas:
                f.write(f"  [{line_num:3d}] {formula}\n")
            f.write("\n")

def main():
    import sys
    
    # Default input file
    input_file = "distributed_lock_375.log"
    output_file = None
    
    # Parse command line arguments
    if len(sys.argv) > 1:
        input_file = sys.argv[1]
    if len(sys.argv) > 2:
        output_file = sys.argv[2]
    
    if not Path(input_file).exists():
        print(f"Error: Input file '{input_file}' not found")
        sys.exit(1)
    
    print(f"Reading formulas from: {input_file}")
    groups = group_formulas(input_file)
    
    print_groups(groups)
    
    if output_file:
        export_to_file(groups, output_file)
        print(f"\nResults exported to: {output_file}")

if __name__ == '__main__':
    main()