from ivy import ivy_logic as il
from ivy import ivy_logic_utils as ilu
from transition_system import TransitionSystem
from prime import Prime
from verbose import *
from util import FormulaUtility as futil

SIGNATR_DELIM   = '$'
CLASS_DELIM     = '; '
PARTITION_DELIM = ' | '

def add_member_terms_for_dependent_sorts(atoms, tran_sys : TransitionSystem):
    terms = []
    args = set()
    for atom in atoms:
        if isinstance(atom, il.Not):
            atom = atom.args[0] 
        atom_args = atom.args
        if il.is_eq(atom):
            atom_args = [atom_args[1]]
        for arg in atom_args:
            args.add(arg)
    for arg in args:
        if arg.sort in tran_sys.dep_types:
            set_sort = arg.sort
            set_id   = 0
            consts   = tran_sys.sort2consts[set_sort]
            for i, const in enumerate(consts):
                if const == arg:
                    set_id = i
            member_func  = tran_sys.get_dependent_relation(set_sort)
            elements     = tran_sys.get_dependent_elements(set_sort)
            elems_in_set = tran_sys.get_dependent_elements_in_set(set_sort, set_id)
            for elem in elements:
                if elem in args:
                    member_args = [elem, arg]
                    member_symb = il.App(member_func, *member_args)
                    if elem in elems_in_set:
                        terms.append(member_symb)
                    else:
                        terms.append(il.Not(member_symb))
    return terms 

def get_used_qvars(sort2qvars, sort):
    if not sort in sort2qvars:         
        sort2qvars[sort] = []
    return sort2qvars[sort]

def get_next_unused_qvar(sort, qvars):
    qvar_id = len(qvars)
    qvar_name = sort.name.upper() + str(qvar_id)
    qvar      = il.Variable(qvar_name, sort) 
    return qvar

def replace_var_with_qvar(tran_sys : TransitionSystem, terms):
    # relabel each var into qvar with index being order of occurrence
    # e.g. n2 n0 n1 m ---> Qn0 Qn1 Qn2 Qm0
    state =  il.And(*terms) if len(terms) != 0 else il.And()
    var2qvar   = {}
    sort2qvars = {}
    for term in terms:
        if isinstance(term, il.Not):
            term = term.args[0]
        if il.is_eq(term) and il.is_enumerated(term.args[0]):
            term = term.args[1]
        variables  = ilu.used_constants_ast(term)
        for var in sorted(variables, key=str):
            sort = var.sort
            if not sort in tran_sys.sort2consts:
                continue
            qvars  = get_used_qvars(sort2qvars, sort)
            qvar   = get_next_unused_qvar(sort, qvars) 
            qvars.append(qvar)
            var2qvar[var] = qvar

    qstate = il.substitute(state, var2qvar)
    qterms = futil.flatten_cube(qstate)
    return qterms

def get_terms(tran_sys : TransitionSystem, atoms, prime : Prime):
    values = prime.values
    terms = []
    for atom_id, atom in enumerate(atoms):
        val = values[atom_id]
        if val == '0':
            terms.append(il.Not(atom))
        elif val == '1':
            terms.append(atom)
        else:
            assert(val == '-')
    return terms

def get_qterms(tran_sys : TransitionSystem, atoms, prime : Prime):
    terms  = get_terms(tran_sys, atoms, prime) 
    qterms = replace_var_with_qvar(tran_sys, terms)
    return qterms 

def split_term(term):
    if isinstance(term, il.Not):
        return ('1', term.args[0])
    else:
        return ('0', term)

def split_signed_func_name(signed_func_name):
    splitted = signed_func_name.split(SIGNATR_DELIM)
    is_neg  = splitted[0]
    fname   = splitted[1]
    return (is_neg, fname)

def get_func_symbol(atom):
    symbol = None
    if isinstance(atom, il.App):
        symbol = atom.func
    elif il.is_eq(atom):
        lhs = atom.args[0]
        symbol = None
        if isinstance(lhs, il.App):
            symbol = lhs.func
        else:
            symbol = lhs
    else:
        assert(il.is_boolean(atom))
        symbol = atom
    return symbol 

def get_signed_func_name(sign, atom, func_symbol):
    fname = None
    if il.is_eq(atom):
        fname = sign + SIGNATR_DELIM + str(func_symbol) + '='
    elif isinstance(atom, il.App) or il.is_boolean(atom):
        fname = sign + SIGNATR_DELIM + str(func_symbol)
    return fname

def get_unsigned_func_name(atom, func_symbol):
    fname = None
    if il.is_eq(atom):
        fname = str(func_symbol)+'=' 
    elif isinstance(atom, il.App) or il.is_boolean(atom):
        fname = str(func_symbol)
    return fname 

def get_func_args(atom):
    args = None
    if il.is_eq(atom):
        lhs = atom.args[0]
        args = []
        if isinstance(lhs, il.App):
            args += list(lhs.args)
        args.append(atom.args[1])
        args = tuple(args)
    elif isinstance(atom, il.App) or il.is_boolean(atom):
        args = atom.args
    return args

def get_func_args_sort(atom, func_symbol):
    args_sort = None
    if il.is_eq(atom):
        lhs = atom.args[0]
        rhs = atom.args[1]
        args_sort = []
        if isinstance(lhs, il.App):
            # lhs is func_symbol
            args_sort += func_symbol.sort.dom
        args_sort.append(rhs.sort)
        args_sort  = tuple(args_sort)
    elif isinstance(atom, il.App) or il.is_boolean(atom):
        args_sort = func_symbol.sort.dom
    return args_sort

# ...existing code...
def evaluate_ground_formula_on_terms(fmla, terms_set):
    """Evaluate a quantifier-free ivy formula `fmla` against a set of ground literals (strings)."""
    if isinstance(fmla, il.Not):
        return not evaluate_ground_formula_on_terms(fmla.args[0], terms_set)
    # and / or may be represented as il.And/il.Or or as apps to 'and'/'or'
    if isinstance(fmla, il.And):
        return all(evaluate_ground_formula_on_terms(a, terms_set) for a in fmla.args)
    if isinstance(fmla, il.Or):
        return any(evaluate_ground_formula_on_terms(a, terms_set) for a in fmla.args)
    # fallback: treat as atomic formula (App, Equals, etc.)
    return str(fmla) in terms_set

# ...existing code...
def _collect_atomic_occurrences(fmla, pos_set, neg_set):
    """Collect syntactic positive/negated atomic occurrences from a quantifier-free formula.
    This is conservative: it records atomic Apps/Equals seen and direct Not(atom) occurrences.
    """
    if isinstance(fmla, il.Not):
        a = fmla.args[0]
        if isinstance(a, il.App) or il.is_boolean(a) or il.is_eq(a):
            neg_set.add(str(a))
        else:
            # fallback: traverse inside but mark occurrences as negated
            _collect_atomic_occurrences(a, neg_set, pos_set)
    elif isinstance(fmla, il.And) or isinstance(fmla, il.Or):
        for a in fmla.args:
            _collect_atomic_occurrences(a, pos_set, neg_set)
    else:
        # atomic occurrence
        pos_set.add(str(fmla))

# ...existing code...
def coverage_result_to_string(result, tran_sys: TransitionSystem, atoms, max_primes: int = 20) -> str:
    """Convert formula_covers_orbit result into a readable single string."""
    covers, entries = result
    lines = []
    if covers:
        return "Covers orbit: True\n"
    lines.append(f"Covers orbit: False — {len(entries)} failing primes (showing up to {max_primes})")
    for i, (prime, info) in enumerate(entries):
        if i >= max_primes:
            lines.append(f"... ({len(entries)-max_primes} more primes not shown)")
            break
        pid = getattr(prime, 'id', None)
        lines.append('---')
        lines.append(f'Prime id: {pid}')
        # short terms summary (positive atoms)
        try:
            terms = get_terms(tran_sys, atoms, prime)
            pos = [str(t) for t in terms if not isinstance(t, il.Not)]
            if pos:
                lines.append('  terms (positive):')
                for t in pos[:10]:
                    lines.append('    ' + t)
                if len(pos) > 10:
                    lines.append('    ...')
            else:
                lines.append('  terms: <no positive atoms>')
        except Exception:
            lines.append('  terms: <failed to get terms>')
        # info fields
        lines.append(f"  holds: {info.get('holds')}")
        if info.get('missing'):
            lines.append('  missing atoms (formula mentions but prime lacks):')
            for a in info['missing'][:10]:
                lines.append('    ' + a)
            if len(info['missing']) > 10:
                lines.append('    ...')
        if info.get('conflicts'):
            lines.append('  conflicts (formula pos but prime has negation):')
            for a in info['conflicts'][:10]:
                lines.append('    ' + a)
        if info.get('extra_in_prime'):
            lines.append('  extra positive atoms in prime (not in formula):')
            for a in info['extra_in_prime'][:10]:
                lines.append('    ' + a)
    lines.append('')
    return '\n'.join(lines)

def formula_covers_orbit(qformula, orbit, tran_sys: TransitionSystem, atoms, instantiator):
    """
    Return (covers: bool, results: List[(Prime, info)]).
    info is a dict with keys:
      - holds: bool  -- whether the grounded qformula evaluated True on the prime
      - missing: List[str] -- positive atoms present syntactically in grounded formula but not true in prime
      - conflicts: List[str] -- atoms where formula has positive atom but prime has its negation
      - extra_in_prime: List[str] -- positive atoms true in prime but not mentioned positively in grounded formula
    """
    ground = instantiator.instantiate_quantifier(qformula)
    # collect syntactic positive/negated atomic occurrences from the grounded formula
    f_pos_atoms = set()
    f_neg_atoms = set()
    _collect_atomic_occurrences(ground, f_pos_atoms, f_neg_atoms)

    results = []
    all_ok = True
    for prime in orbit.primes:
        terms = get_terms(tran_sys, atoms, prime)   # list of il terms (App or Not(App))
        # split prime into positive and negated atom string sets
        prime_pos = set()
        prime_neg = set()
        for t in terms:
            if isinstance(t, il.Not):
                prime_neg.add(str(t.args[0]))
            else:
                prime_pos.add(str(t))
        # evaluate formula truth on this prime
        holds = evaluate_ground_formula_on_terms(ground, set(str(t) for t in terms))
        # compute differences
        missing = sorted(list(f_pos_atoms - prime_pos))
        conflicts = sorted(list(f_pos_atoms & prime_neg))
        extra_in_prime = sorted(list(prime_pos - f_pos_atoms))
        info = {'holds': holds, 'missing': missing, 'conflicts': conflicts, 'extra_in_prime': extra_in_prime}
        results.append((prime, info))
        if not holds or missing or conflicts:
            all_ok = False
    return (all_ok, results)
# ...existing code...