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

def get_qterms(tran_sys : TransitionSystem, atoms, prime : Prime):
    values = prime.values
    terms = []
    atom_symbols = []
    for atom_id, atom in enumerate(atoms):
        val = values[atom_id]
        if val == '0':
            terms.append(il.Not(atom))
            atom_symbols.append(atom)
        elif val == '1':
            terms.append(atom)
            atom_symbols.append(atom)
        else:
            assert(val == '-')
    terms += add_member_terms_for_dependent_sorts(atom_symbols, tran_sys)
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
    symbol    = None
    if isinstance(atom, il.App):
        symbol = atom.func
    elif il.is_eq(atom):
        lhs = atom.args[0]
        symbol = None
        if isinstance(lhs, il.App):
            symbol = lhs.func
        else:
            symbol = lhs
    return symbol 

def get_signed_func_name(sign, atom, func_symbol):
    fname = None
    if isinstance(atom, il.App):
        fname = sign + SIGNATR_DELIM + str(func_symbol)
    elif il.is_eq(atom):
        fname = sign + SIGNATR_DELIM + str(func_symbol) + '='
    return fname

def get_unsigned_func_name(atom, func_symbol):
    fname = None
    if isinstance(atom, il.App):
        fname = str(func_symbol)
    elif il.is_eq(atom):
        fname = str(func_symbol)+'=' 
    return fname 

def get_func_args(atom):
    args = None
    if isinstance(atom, il.App):
        args = atom.args
    elif il.is_eq(atom):
        lhs = atom.args[0]
        args = []
        if isinstance(lhs, il.App):
            args += list(lhs.args)
        args.append(atom.args[1])
        args = tuple(args)
    return args

def get_func_args_sort(atom, func_symbol):
    args_sort = None
    if isinstance(atom, il.App):
        args_sort = func_symbol.sort.dom
    elif il.is_eq(atom):
        lhs = atom.args[0]
        rhs = atom.args[1]
        args_sort = []
        if isinstance(lhs, il.App):
            # lhs is func_symbol
            args_sort += func_symbol.sort.dom
        args_sort.append(rhs.sort)
        args_sort  = tuple(args_sort)
    return args_sort

from enum import Enum
QuantifierMode  = Enum('QuantifierMode', ['forall', 'exists', 'forall_exists'])
ConstraintMode  = Enum('ConstraintMode', ['merge_absent', 'merge_present', 'no_merge'])
'''
    'merge_absent':   enumerate all partitions of "class_signature" in self.product_arg_partition
                for each arg_partition of qprime, 
                it is also a partition of "class_signature" in self.product_arg_partition
                we add final constraint describing partitions of "class_signature" in self.product_arg_partition 
                that is absent among self.arg_partitions
    'merge_present':  does not enumerate all partitions of "class_signature" in self.product_arg_partition
                we add final constraint describing partitions of "class_signature" 
                that is present in self.arg_partitions
'''