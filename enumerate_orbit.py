from ivy import ivy_logic as il
from transition_system import get_transition_system
from util import QrmOptions
from util import FormulaUtility as futil
from finite_ivy_instantiate import FiniteIvyInstantiator
from ivy import ivy_logic_utils as ilu
from itertools import product
from qutil import evaluate_ground_formula_on_terms
from qutil import atoms_equal
from collections import OrderedDict
import click


from itertools import permutations


def construct_forall_exists_qformula(size=3):
    node_sort = il.EnumeratedSort('node', [f'node{i}' for i in range(size)])

    # Declare relation symbols
    p = il.Symbol('p', il.RelationSort([node_sort]))
    q = il.Symbol('q', il.RelationSort([node_sort]))


    # Variables
    N0 = il.Variable('N0', node_sort)
    N1 = il.Variable('N1', node_sort)
    N2 = il.Variable('N2', node_sort) 
    N3 = il.Variable('N3', node_sort)

    # Inner formula: (N0 = N1) | ~p(N0) | ~p(N1) | (N2 = N3) | ~q(N2) | ~q(N3)
    eq_01 = il.Equals(N0, N1)
    not_p0 = il.Not(il.App(p, N0))
    not_p1 = il.Not(il.App(p, N1))
    eq_23 = il.Equals(N2, N3)
    not_q2 = il.Not(il.App(q, N2))
    not_q3 = il.Not(il.App(q, N3))
    
    inner_disjunction = il.Or(eq_01, not_p0, not_p1, eq_23, not_q2, not_q3)

    # Inner universal: ∀N2,N3. [inner_disjunction]
    inner_forall = il.ForAll([N2, N3], inner_disjunction)

    # Outer negation: ¬∀N2,N3. [inner_disjunction]
    negated_inner = il.Not(inner_forall)

    # Outer universal: ∀N0,N1. [¬∀N2,N3. ...]
    full_formula = il.ForAll([N0, N1], negated_inner)

    print("Invariant formula:", full_formula)
    return full_formula



def construct_forall_qformula(size=3):
    node_sort = il.EnumeratedSort('node', [f'node{i}' for i in range(size)])

    # Declare relation symbols
    p = il.Symbol('p', il.RelationSort([node_sort]))
    q = il.Symbol('q', il.RelationSort([node_sort]))

    NODE0 = il.Variable('NODE0', node_sort)
    NODE1 = il.Variable('NODE1', node_sort) 
    NODE2 = il.Variable('NODE2', node_sort)

    # Build the disjunction: ~p(NODE0) | ~p(NODE1) | q(NODE0) | q(NODE2)
    not_p0 = il.Not(il.App(p, NODE0))
    not_p1 = il.Not(il.App(p, NODE1))
    q0 = il.App(q, NODE0)
    q2 = il.App(q, NODE2)
    disjunction = il.Or(not_p0, not_p1, q0, q2)

    # Build the equality disjunction: (NODE0 = NODE1) | (NODE0 = NODE2)
    eq01 = il.Equals(NODE0, NODE1)
    eq02 = il.Equals(NODE0, NODE2)
    equality_disjunction = il.Or(eq01, eq02)

    # Combine both parts with OR
    body = il.Or(disjunction, equality_disjunction)

    # Apply universal quantification
    full_formula = il.ForAll([NODE0, NODE1, NODE2], body)

    return full_formula


def get_trans_sys(size=3):
    options = QrmOptions()
    options.set_files_name('ivybench/sym/ivy/McMillan_Example2.ivy')
    options.set_sizes(f'node={size}')
    tran_sys = get_transition_system(options, options.ivy_filename)
    return tran_sys

def remove_quantifiers(qformula, tran_sys):
    """
    Recursively remove quantifiers by expanding over finite domains.
    Returns a quantifier-free formula.
    """
    if isinstance(qformula, il.ForAll):
        return expand_forall(qformula, tran_sys)
    elif isinstance(qformula, il.Exists):
        return expand_exists(qformula, tran_sys)
    elif isinstance(qformula, il.Not):
        return il.Not(remove_quantifiers(qformula.args[0], tran_sys))
    elif isinstance(qformula, il.And):
        return il.And(*[remove_quantifiers(arg, tran_sys) for arg in qformula.args])
    elif isinstance(qformula, il.Or):
        return il.Or(*[remove_quantifiers(arg, tran_sys) for arg in qformula.args])
    elif isinstance(qformula, il.Implies):
        left, right = qformula.args
        return il.Implies(remove_quantifiers(left, tran_sys), remove_quantifiers(right, tran_sys))
    elif il.is_eq(qformula) or isinstance(qformula, il.App):
        # Base case: atomic formula, no quantifiers to remove
        return qformula
    else:
        raise ValueError(f"Unsupported formula type: {type(qformula)}")

def expand_forall(forall_formula, tran_sys):
    """
    Expand ForAll x1..xn. P(x1..xn) into ∧_{c1..cn} P(c1..cn)
    """
    variables = forall_formula.variables
    body = forall_formula.body
    
    # Get constants for each variable's sort
    domains = []
    for var in variables:
        sort = var.sort
        if sort in tran_sys.sort2consts:
            constants = tran_sys.sort2consts[sort]
        else:
            # Fallback: try to find constants from the sort name
            constants = find_constants_by_sort_name(sort, tran_sys)
        domains.append(constants)
    
    # Generate all combinations and create conjunction
    instances = []
    for const_combination in product(*domains):
        substitution = dict(zip(variables, const_combination))
        instantiated_body = il.substitute(body, substitution)
        # Recursively remove quantifiers from the instantiated body
        quantifier_free_body = remove_quantifiers(instantiated_body, tran_sys)
        instances.append(quantifier_free_body)
    
    if not instances:
        return il.And()  # Empty conjunction is True
    elif len(instances) == 1:
        return instances[0]
    else:
        return il.And(*instances)

def expand_exists(exists_formula, tran_sys):
    """
    Expand Exists x1..xn. P(x1..xn) into ∨_{c1..cn} P(c1..cn)
    """
    variables = exists_formula.variables
    body = exists_formula.body
    
    # Get constants for each variable's sort
    domains = []
    for var in variables:
        sort = var.sort
        if sort in tran_sys.sort2consts:
            constants = tran_sys.sort2consts[sort]
        else:
            constants = find_constants_by_sort_name(sort, tran_sys)
        domains.append(constants)
    
    # Generate all combinations and create disjunction
    instances = []
    for const_combination in product(*domains):
        substitution = dict(zip(variables, const_combination))
        instantiated_body = il.substitute(body, substitution)
        # Recursively remove quantifiers from the instantiated body
        quantifier_free_body = remove_quantifiers(instantiated_body, tran_sys)
        instances.append(quantifier_free_body)
    
    if not instances:
        return il.Or()  # Empty disjunction is False
    elif len(instances) == 1:
        return instances[0]
    else:
        return il.Or(*instances)

def find_constants_by_sort_name(sort, tran_sys):
    """Find constants for a sort by its name"""
    sort_name = sort.name
    for finite_sort, constants in tran_sys.sort2consts.items():
        if finite_sort.name == sort_name:
            return constants
    
    # If not found, check if it's an enumerated sort
    if isinstance(sort, il.EnumeratedSort):
        return sort.domain_elements
    
    # Last resort: create default constants based on sort name
    print(f"Warning: Could not find constants for sort {sort_name}, using defaults")
    return [il.Constant(f"{sort_name}0")]



def get_all_state_atoms(transition_system):
    """Extract all ground state atoms from the transition system"""
    state_atoms = []
    
    # Get all state symbols (relations)
    state_symbols = transition_system.get_state_variables()
    
    print(f"Found {len(state_symbols)} state symbols:")
    for symbol in state_symbols:
        print(f"  {symbol}")
    
    # For each state symbol, generate all ground instances
    for symbol in state_symbols:
        symbol_sort = symbol.sort
        
        if isinstance(symbol_sort, il.FunctionSort):
            # This is a relation/function symbol
            domains = []
            for domain_sort in symbol_sort.domain:
                if domain_sort in transition_system.sort2consts:
                    # Get constants for this sort
                    constants = transition_system.sort2consts[domain_sort]
                    domains.append(constants)
                else:
                    # For sorts without explicit constants, try to get from options
                    sort_name = domain_sort.name
                    if sort_name in transition_system.options.sizes:
                        size = transition_system.options.sizes[sort_name]
                        constants = [il.Constant(f"{sort_name}{i}") for i in range(size)]
                        domains.append(constants)
                    else:
                        # Fallback: create default constants
                        domains.append([il.Constant(f"{sort_name}0")])
            
            # Generate all combinations of arguments
            for args in product(*domains):
                atom = il.App(symbol, *args)
                state_atoms.append(atom)
                
        elif isinstance(symbol_sort, il.BooleanSort):
            # This is a proposition (0-ary relation)
            state_atoms.append(symbol)
    
    state_atoms.sort(key=str)

    return state_atoms


def minimize_assignments(unsatisfying_assignments, state_atoms):
    """
    Find ALL prime implicants using proper Quine-McCluskey approach
    """
    if not unsatisfying_assignments:
        return []
    
    # Convert assignments to binary representations
    atom_order = [str(atom) for atom in state_atoms]
    n = len(atom_order)
    
    def assignment_to_binary(assignment):
        """Convert assignment to binary string (1=true, 0=false)"""
        binary = []
        for atom in state_atoms:
            binary.append('1' if assignment[atom] else '0')
        return ''.join(binary)
    
    def binary_to_assignment(binary):
        """Convert binary string back to assignment with don't-cares"""
        assignment = OrderedDict()
        for i, (atom, bit) in enumerate(zip(state_atoms, binary)):
            if bit == '-':
                assignment[atom] = None  # don't-care
            else:
                assignment[atom] = (bit == '1')
        return assignment
    
    def can_combine(bin1, bin2):
        """Check if two binary strings differ in exactly one position"""
        differences = 0
        for b1, b2 in zip(bin1, bin2):
            if b1 != b2:
                differences += 1
                if differences > 1:
                    return False
        return differences == 1
    
    def combine(bin1, bin2):
        """Combine two binary strings that differ in one position"""
        result = []
        for b1, b2 in zip(bin1, bin2):
            if b1 == b2:
                result.append(b1)
            else:
                result.append('-')  # don't-care
        return ''.join(result)
    
    def get_size(binary):
        """Get the number of concrete assignments covered by this pattern"""
        return 2 ** binary.count('-')
    
    # Step 1: Convert all assignments to binary
    binary_assignments = [assignment_to_binary(assign) for assign in unsatisfying_assignments]
    
    # Step 2: Find ALL prime implicants (not just essential ones)
    current_level = set(binary_assignments)
    all_primes = set()
    
    while current_level:
        next_level = set()
        used = set()
        
        for bin1 in current_level:
            for bin2 in current_level:
                if bin1 != bin2 and can_combine(bin1, bin2):
                    combined = combine(bin1, bin2)
                    next_level.add(combined)
                    used.add(bin1)
                    used.add(bin2)
        
        # Add uncombined patterns to primes
        for bin_val in current_level:
            if bin_val not in used:
                all_primes.add(bin_val)
        
        current_level = next_level
    
    # Step 3: Remove redundant primes (if one prime covers another)
    final_primes = set()
    prime_list = sorted(all_primes, key=get_size, reverse=True)  # Largest first
    
    for i, prime1 in enumerate(prime_list):
        is_redundant = False
        for j, prime2 in enumerate(prime_list):
            if i != j:
                # Check if prime2 covers everything prime1 covers
                covers_all = True
                for conc in binary_assignments:
                    if covers(prime1, conc) and not covers(prime2, conc):
                        covers_all = False
                        break
                if covers_all:
                    is_redundant = True
                    break
        if not is_redundant:
            final_primes.add(prime1)
    
    # Convert back to assignment format
    minimized_assignments = []
    for prime in final_primes:
        minimized_assignments.append(binary_to_assignment(prime))
    
    return minimized_assignments

def covers(pattern, concrete):
    """Check if a pattern with dashes covers a concrete binary string"""
    for p, c in zip(pattern, concrete):
        if p != '-' and p != c:
            return False
    return True

def format_minimized_assignment(assignment):
    """Format a minimized assignment with '-' for don't-care values"""
    atoms_list = []
    
    for atom, value in assignment.items():
        if value is True:
            atoms_list.append(str(atom))  # True atoms as-is
        elif value is False:
            atoms_list.append(f"¬{atom}")  # False atoms with negation
        else:  # value is None (don't-care)
            atoms_list.append(f"-")  # Don't-care with hyphen
    
    return "{" + ", ".join(atoms_list) + "}"

def enumerate_unsatisfying_assignments(formula, transition_system, print_all=False):
    """
    Now we can use the simple evaluation since formula is quantifier-free
    """
    state_atoms = get_all_state_atoms(transition_system)
    print(f"Found {len(state_atoms)} ground state atoms")

    
    unsatisfying_assignments = []
    n = len(state_atoms)
    
    for i in range(2 ** n):
        assignment = OrderedDict()
        for j, atom in enumerate(state_atoms):
            assignment[atom] = bool((i >> j) & 1)
        
        try:
            satisfies = evaluate_ground_formula(formula, assignment, state_atoms)
            if not satisfies:
                unsatisfying_assignments.append(assignment)
        except Exception as e:
            print(f"Error: {e}")
    
    print(f"\nTotal unsatisfying assignments: {len(unsatisfying_assignments)}")
    if print_all:
        for i, assignment in enumerate(unsatisfying_assignments, 1):
            print(f"{i}: {format_assignment(assignment)}")
        
    
    # Minimize the assignments
    minimized_assignments = minimize_assignments(unsatisfying_assignments, state_atoms)
    
    print(f"\nMinimized unsatisfying assignments: {len(minimized_assignments)}")
    for i, assignment in enumerate(minimized_assignments, 1):
        print(f"{i}: {format_minimized_assignment(assignment)}")
    
    return minimized_assignments

def evaluate_ground_formula(fmla, assignment, state_atoms):
    """
    Simple evaluation for quantifier-free formulas only.
    assignment: dictionary {ground_atom: True/False}
    state_atoms: list of all ground state atoms (for matching)
    """
    if isinstance(fmla, il.Not):
        return not evaluate_ground_formula(fmla.args[0], assignment, state_atoms)
    
    elif isinstance(fmla, il.And):
        return all(evaluate_ground_formula(a, assignment, state_atoms) for a in fmla.args)
    
    elif isinstance(fmla, il.Or):
        return any(evaluate_ground_formula(a, assignment, state_atoms) for a in fmla.args)
    
    elif il.is_eq(fmla):
        left, right = fmla.args
        # For ground terms, check if they're the same constant
        return left == right
    
    elif isinstance(fmla, il.App):
        # Look up this atom in the assignment dictionary
        for atom in state_atoms:
            if atoms_equal(atom, fmla):
                return assignment.get(atom, False)
        # If atom not found, return False (closed world assumption)
        return False
    
    elif isinstance(fmla, il.Implies):
        left, right = fmla.args
        return (not evaluate_ground_formula(left, assignment, state_atoms) or 
                evaluate_ground_formula(right, assignment, state_atoms))
    
    elif isinstance(fmla, il.Iff):
        left, right = fmla.args
        left_val = evaluate_ground_formula(left, assignment, state_atoms)
        right_val = evaluate_ground_formula(right, assignment, state_atoms)
        return left_val == right_val
    
    else:
        # If we somehow still get quantifiers or unsupported types, return False
        print(f"Warning: Unexpected formula type in ground eval: {type(fmla)}")
        return False

def atoms_equal(atom1, atom2):
    """Check if two atoms are equal (structural equality)"""
    if str(atom1) == str(atom2):
        return True
    if isinstance(atom1, il.App) and isinstance(atom2, il.App):
        if atom1.rep == atom2.rep and len(atom1.args) == len(atom2.args):
            return all(arg1 == arg2 for arg1, arg2 in zip(atom1.args, atom2.args))
    return False




def format_assignment(assignment):
    """Format an assignment for readable output"""
    atoms_list = []
    
    # assignment is an OrderedDict with atoms in the order we want (p's then q's)
    for atom, value in assignment.items():
        if value:
            atoms_list.append(str(atom))  # True atoms as-is
        else:
            atoms_list.append(f"¬{atom}")  # False atoms with negation
    
    return "{" + ", ".join(atoms_list) + "}"

@click.command()
@click.option("-s", "--size", type=int, default=3, help="Set size")
@click.option("-f", "--forall", is_flag=True, help="Use Forall")
def enumerate_orbit(size, forall):
    if forall:
#         qformula = parse_general_formula("forall NODE0,NODE2,NODE1. "
# "~p(NODE0) | ~p(NODE1) | q(NODE0) | q(NODE2) |" 
# "(NODE0 = NODE1) | (NODE0 = NODE2)", size)

        qformula = construct_forall_qformula(size)
    else:
        # qformula = parse_general_formula("forall NODE0,NODE1. NODE0 != NODE1 -> (~p(NODE0) | ~p(NODE1) | (exists NODE2,NODE3. NODE2 != NODE3 & q(NODE2) & q(NODE3)))", size)
        
        qformula = construct_forall_exists_qformula(size)
    print("Formula: ", qformula)
    tran_sys = get_trans_sys(size)
    qformula = remove_quantifiers(qformula, tran_sys)
    print("Quantifier-free: ", qformula)
    enumerate_unsatisfying_assignments(qformula, tran_sys)
    



if __name__ == "__main__":
    enumerate_orbit()