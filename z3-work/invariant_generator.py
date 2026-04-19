import re
import sys
from pathlib import Path

def convert_to_smt(text):
    lines = text.strip().split('\n')
    smt_lines = []
    
    for i, line in enumerate(lines, 0):
        line = line.strip()
        if not line or line.startswith(';'): continue
        
        # 1. Improved Header Detection (forall/exists)
        header_match = re.search(r'^(forall|exists)\s+(.*?)\.', line, re.IGNORECASE)
        if not header_match: 
            # Check if it's a simple predicate without a quantifier
            if '(' in line and ')' in line:
                try:
                    parsed = parse_expression(line)
                    smt_lines.append(f"(assert (= R{i} {parsed}))")
                    continue
                except: pass
            smt_lines.append(f"; SKIPPED line {i}: {line[:30]}...")
            continue
        
        quant_type = header_match.group(1).lower()
        vars_raw = header_match.group(2).split(',')
        vars_list = [v.strip().lower() for v in vars_raw]
        
        # 2. Extract Logic
        logic_part = line.split('.', 1)[1].strip()
        
        # 3. Final Conversion
        try:
            parsed_logic = parse_expression(logic_part)
            forall_vars = " ".join([f"({v} node)" for v in vars_list])
            smt_lines.append(f"(assert (= R{i} ({quant_type} ({forall_vars}) {parsed_logic})))")
        except Exception as e:
            smt_lines.append(f"; ERROR on line {i}: {str(e)}")
            
    return "\n".join(smt_lines)

def parse_expression(expr):
    expr = expr.strip()
    
    # Remove outer balanced parentheses
    while expr.startswith('(') and expr.endswith(')') and _is_balanced(expr[1:-1]):
        expr = expr[1:-1].strip()

    # Handle Implication '=>' (Lowest precedence)
    top_imp = _find_top_level(expr, '=>')
    if top_imp:
        parts = _split_by_indices(expr, top_imp, length=2)
        return f"(=> {parse_expression(parts[0])} {parse_expression(parts[1])})"

    # Handle OR '|'
    top_or = _find_top_level(expr, '|')
    if top_or:
        parts = _split_by_indices(expr, top_or)
        return f"(or {' '.join([parse_expression(p) for p in parts])})"
    
    # Handle AND '&'
    top_and = _find_top_level(expr, '&')
    if top_and:
        parts = _split_by_indices(expr, top_and)
        return f"(and {' '.join([parse_expression(p) for p in parts])})"
    
    # Handle Negation '~'
    if expr.startswith('~'):
        return f"(not {parse_expression(expr[1:])})"
    
    # Handle Inequality '~='
    if '~=' in expr:
        left, right = expr.split('~=', 1)
        return f"(not (= {left.strip().lower()} {right.strip().lower()}))"
    
    # Handle Equality '='
    if '=' in expr:
        left, right = expr.split('=', 1)
        return f"(= {left.strip().lower()} {right.strip().lower()})"
    
    # Handle Predicates like held(n0)
    pred_match = re.match(r'(\w+)\((.*?)\)', expr)
    if pred_match:
        name = pred_match.group(1).lower()
        # Correctly handle comma-separated arguments inside predicates
        args = [a.strip().lower() for a in pred_match.group(2).split(',')]
        return f"({name} {' '.join(args)})"
    
    return expr.lower()

def _is_balanced(s):
    count = 0
    for char in s:
        if char == '(': count += 1
        elif char == ')': count -= 1
        if count < 0: return False
    return count == 0

def _find_top_level(s, op):
    indices = []
    depth = 0
    i = 0
    while i < len(s):
        if s[i] == '(': depth += 1
        elif s[i] == ')': depth -= 1
        elif depth == 0 and s[i:i+len(op)] == op:
            indices.append(i)
            i += len(op) - 1
        i += 1
    return indices

def _split_by_indices(s, indices, length=1):
    parts = []
    start = 0
    for idx in indices:
        parts.append(s[start:idx])
        start = idx + length
    parts.append(s[start:])
    return parts

def load_invariants_text(file_path):
    with open(file_path, 'r', encoding='utf-8') as f:
        text = f.read().strip()
    if not text:
        raise ValueError(f"No invariants found in {file_path}")
    return text


def main():
    default_invariants_path = Path(__file__).with_name('simplified_invars.txt')
    invariants_path = Path(sys.argv[1]) if len(sys.argv) > 1 else default_invariants_path

    if not invariants_path.exists():
        raise FileNotFoundError(
            f"Invariant file not found: {invariants_path}. "
            f"Create it or pass a file path as the first argument."
        )

    print(convert_to_smt(load_invariants_text(invariants_path)))


if __name__ == '__main__':
    main()