from ivy import ivy_logic as il
import re

def parse_general_formula(formula_str, size=3):
    """
    General parser for formulas with dynamic domain size
    """
    # Remove extra whitespace but keep spaces around operators for parsing
    formula_str = re.sub(r'\s+', ' ', formula_str.strip())
    
    # Parse quantifier part
    quant_match = re.match(r'^(forall|exists)\s+([A-Za-z0-9_,\s]+)\.\s*(.+)$', formula_str)
    if not quant_match:
        raise ValueError(f"Invalid formula format: {formula_str}")
    
    quant_type, vars_str, body_str = quant_match.groups()
    
    # Parse variables
    var_names = [v.strip() for v in vars_str.split(',') if v.strip()]
    
    # Create sorts and symbols with dynamic size
    node_constants = [f'node{i}' for i in range(size)]
    node_sort = il.EnumeratedSort('node', node_constants)
    p = il.Symbol('p', il.RelationSort([node_sort]))
    q = il.Symbol('q', il.RelationSort([node_sort]))
    
    # Create variable mapping
    variables = {name: il.Variable(name, node_sort) for name in var_names}
    
    # Parse the body
    body_formula = parse_formula_body(body_str, variables, p, q, node_sort, size)
    
    # Create quantified formula
    quant_vars = [variables[name] for name in var_names]
    if quant_type == 'forall':
        return il.ForAll(quant_vars, body_formula)
    else:  # exists
        return il.Exists(quant_vars, body_formula)

def parse_formula_body(body_str, variables, p, q, node_sort, size):
    """Recursively parse the formula body with nested quantifier support"""
    body_str = body_str.strip()
    
    # Check for nested quantifiers first
    quant_match = re.match(r'^(forall|exists)\s+([A-Za-z0-9_,\s]+)\.\s*(.+)$', body_str)
    if quant_match:
        quant_type, vars_str, inner_body = quant_match.groups()
        
        # Parse inner variables
        inner_var_names = [v.strip() for v in vars_str.split(',') if v.strip()]
        inner_variables = {**variables, **{name: il.Variable(name, node_sort) for name in inner_var_names}}
        
        # Parse inner body
        inner_formula = parse_formula_body(inner_body, inner_variables, p, q, node_sort, size)
        
        # Create quantified formula
        quant_vars = [inner_variables[name] for name in inner_var_names]
        if quant_type == 'forall':
            return il.ForAll(quant_vars, inner_formula)
        else:  # exists
            return il.Exists(quant_vars, inner_formula)
    
    # Handle parentheses for grouping
    if body_str.startswith('(') and body_str.endswith(')'):
        return parse_formula_body(body_str[1:-1], variables, p, q, node_sort, size)
    
    # Split by top-level OR (|) - lowest precedence
    or_parts = split_top_level(body_str, '|')
    if len(or_parts) > 1:
        return il.Or(*[parse_formula_body(part, variables, p, q, node_sort, size) for part in or_parts])
    
    # Split by top-level AND (&) 
    and_parts = split_top_level(body_str, '&')
    if len(and_parts) > 1:
        return il.And(*[parse_formula_body(part, variables, p, q, node_sort, size) for part in and_parts])
    
    # Handle implication (->)
    if '->' in body_str:
        left, right = body_str.split('->', 1)
        return il.Implies(
            parse_formula_body(left, variables, p, q, node_sort, size),
            parse_formula_body(right, variables, p, q, node_sort, size)
        )
    
    # Handle negation
    if body_str.startswith('~'):
        return il.Not(parse_formula_body(body_str[1:], variables, p, q, node_sort, size))
    
    # Handle atomic formulas
    return parse_atomic_formula(body_str, variables, p, q, node_sort, size)

def split_top_level(formula_str, delimiter):
    """Split formula by delimiter, respecting parentheses"""
    parts = []
    current = []
    paren_count = 0
    
    for char in formula_str:
        if char == '(':
            paren_count += 1
        elif char == ')':
            paren_count -= 1
        elif char == delimiter and paren_count == 0:
            parts.append(''.join(current).strip())
            current = []
            continue
        current.append(char)
    
    if current:
        parts.append(''.join(current).strip())
    
    return parts

def parse_atomic_formula(atom_str, variables, p, q, node_sort, size):
    """Parse atomic formulas like p(X), q(Y), X=Y, etc."""
    atom_str = atom_str.strip()
    
    # Handle inequality FIRST (before equality)
    if '!=' in atom_str:
        left, right = atom_str.split('!=', 1)
        left = left.strip()
        right = right.strip()
        
        left_term = parse_term(left, variables, node_sort, size)
        right_term = parse_term(right, variables, node_sort, size)
        return il.Not(il.Equals(left_term, right_term))
    
    # Handle equality
    if '=' in atom_str:
        left, right = atom_str.split('=', 1)
        left = left.strip()
        right = right.strip()
        
        left_term = parse_term(left, variables, node_sort, size)
        right_term = parse_term(right, variables, node_sort, size)
        return il.Equals(left_term, right_term)
    
    # Handle relations: p(X), q(Y)
    if atom_str.startswith('p(') and atom_str.endswith(')'):
        var_name = atom_str[2:-1].strip()
        return il.App(p, parse_term(var_name, variables, node_sort, size))
    
    if atom_str.startswith('q(') and atom_str.endswith(')'):
        var_name = atom_str[2:-1].strip()
        return il.App(q, parse_term(var_name, variables, node_sort, size))
    
    # Handle boolean constants
    if atom_str.lower() == 'true':
        return il.And()  # True
    if atom_str.lower() == 'false':
        return il.Or()   # False
    
    raise ValueError(f"Unknown atomic formula: {atom_str}")

def parse_term(term_str, variables, node_sort, size):
    """Parse terms (variables or constants) with dynamic size support"""
    term_str = term_str.strip()
    
    # If it's a variable we've seen
    if term_str in variables:
        return variables[term_str]
    
    # If it's a node constant (dynamic: node0, node1, ..., node{size-1})
    if re.match(r'^node\d+$', term_str):
        node_num = int(term_str[4:])  # Extract number from "nodeX"
        if node_num < size:
            return il.Constant(term_str)
        else:
            raise ValueError(f"Node constant {term_str} exceeds domain size {size}")
    
    # Try to parse as a variable (create if not exists)
    return il.Variable(term_str, node_sort)