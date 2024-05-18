from typing import List
from pysmt.shortcuts import Symbol, And, Or, EqualsOrIff, Not, ForAll, Exists, Function, TRUE
from frontend.utils import *
from frontend.vmt_parser import TransitionSystem
from prime import Prime 
from util import QrmOptions
from verbose import *
from more_itertools import set_partitions
from itertools import product, permutations

def get_used_qvars(sort2qvars, sort):
    if not sort in sort2qvars:         
        sort2qvars[sort] = []
    qvars = sort2qvars[sort]
    return qvars

def get_next_unused_qvar(tran_sys, sort, qvars):
    qvar_id = len(qvars)
    qvar    = tran_sys._enum2qvar[sort][qvar_id]
    return qvar

def replace_var_with_qvar(tran_sys, terms):
    # relabel each var into qvar with index being order of occurrence
    # e.g. n2 n0 n1 m ---> Qn0 Qn1 Qn2 Qm0
    state =  And(terms) if len(terms) != 0 else TRUE()
    vars = state.get_enum_constants()
    var2qvar   = {}
    sort2qvars = {}
    for var in sorted(vars, key=str):
        sort = var.constant_type()
        if not sort in tran_sys._enum2qvar:
            continue
        qvars  = get_used_qvars(sort2qvars, sort)
        qvar   = get_next_unused_qvar(tran_sys, sort, qvars) 
        qvars.append(qvar)
        var2qvar[var] = qvar

    qstate = state.simple_substitute(var2qvar)
    qterms = flatten_cube(qstate)
    return qterms

def get_qterms(tran_sys, atoms, prime):
    values = prime.values
    terms = []
    for atom_id, atom in enumerate(atoms):
        val = values[atom_id]
        if val == '0':
            terms.append(Not(atom))
        elif val == '1':
            terms.append(atom)
        else:
            assert(val == '-')
    qterms = replace_var_with_qvar(tran_sys, terms)
    return qterms 

def split_term(term):
    if term.is_not():
        return ('1', term.arg(0))
    else:
        return ('0', term)

def split_signed_func_name(func_name):
    splitted = func_name.split('.')
    is_neg  = splitted[0]
    fname   = splitted[1]
    return (is_neg, fname)

def get_signed_func_name(sign, atom):
    return sign + '.' + str(atom.function_name())

class QPrime():
    # static members
    atoms = []
    tran_sys : TransitionSystem

    def __init__(self, qprime, options):
        self.options            = options
        self.qprime             = qprime
        self.func_name2args     = {}
        self.qvar2arg_signatrs  = {}
        self.sort2part_signatrs = {}

    def add_fname_args(self, fname, args):
        if not fname in self.func_name2args: 
            self.func_name2args[fname] = [] 
        self.func_name2args [fname].append(args)

    def set_function_name_to_arguments(self):
        terms = get_qterms(QPrime.tran_sys, QPrime.atoms, self.qprime)
        for term in terms:
            (sign, atom)  = split_term(term)
            if atom.is_function_application():
                fname = get_signed_func_name(sign, atom)
                self.add_fname_args(fname, atom.args())

        vprint_title(self.options, 'QPrime: set_function_name_to_arguments', 5)
        vprint(self.options, f'func_name2args: {self.func_name2args}', 5)

    def _get_arg_signature(self, signed_fname, func_id, arg_id, qvar):
        sort = qvar.symbol_type() 
        signatr = f'{sort}.{signed_fname}.{func_id}.{arg_id}'
        return signatr

    def _add_qvar_signature(self, qvar, signatr):
        if not qvar in self.qvar2arg_signatrs:
            self.qvar2arg_signatrs[qvar] = [] 
        self.qvar2arg_signatrs[qvar].append(signatr)
        
    def set_qvar_to_argument_signatures(self):
        for fname, arg_list in self.func_name2args.items():
            for func_id, func_args in enumerate(arg_list):
                for arg_id, qvar in enumerate(func_args):
                    signatr = self._get_arg_signature(fname, func_id, arg_id, qvar)
                    self._add_qvar_signature(qvar, signatr)
        vprint_title(self.options, 'QPrime: set_qvar_to_argument_signatures', 5)
        vprint(self.options, f'qvar2arg_signatr: {self.qvar2arg_signatrs}', 5)

    def _add_sort_part_signatures(self, qvar, part_signatr):
        sort = qvar.symbol_type()
        if not sort in self.sort2part_signatrs:
            self.sort2part_signatrs[sort] = []
        self.sort2part_signatrs[sort].append(part_signatr)

    def set_sort_to_partition_signatures(self):
        for qvar, arg_signatrs in self.qvar2arg_signatrs.items():
            part_signatr = ', '.join(arg_signatrs)
            self._add_sort_part_signatures(qvar, part_signatr)
        vprint_title(self.options, 'QPrime: set_sort_to_partition_signatures', 5)
        vprint(self.options, f'sort2partition: {self.sort2part_signatrs}', 5)

    def set_qprime_partition_signature(self):
        from itertools import product
        sort_partition_signatrs = []
        for sort, part_signatrs in self.sort2part_signatrs.items():
            signatr = ' | '.join(part_signatrs)
            sort_partition_signatrs.append([signatr])
        self.partition_signatr = list(product(*sort_partition_signatrs))[0]
        vprint_title(self.options, 'QPrime: set_qprime_partition_signatures', 5)
        vprint(self.options, f'sort partition signature: {sort_partition_signatrs}', 5)
        vprint(self.options, f'partition signature: {self.partition_signatr}', 5)

    @staticmethod
    def setup(atoms, tran_sys) -> None:
        QPrime.atoms    = atoms
        QPrime.tran_sys = tran_sys

class Merger():
    # static members
    atoms = []
    tran_sys : TransitionSystem

    def __init__(self, options, suborbit_repr_primes):
        self.options            = options
        self.sub_repr_primes    = suborbit_repr_primes
        self.qprimes            = []
        self.atoms              = []
        self.func_name2args     = {}
        self.func_name2symbol   = {}
        self.func_name2id       = {}
        self.sort_count         = {}
        self.sort2signatrs      = {}
        self.sort_partitions    = []
        self.partitions         = []
        self.partition_signatrs = []
        self.sort2max_num_parts = {}
        self.sort2part_sizes    = {}
        self.sort2qvars         = {}
        self.func_permutations  = []
        self.signatr2qvar       = {}

    def add_fname_args(self, fname, args):
        if not fname in self.func_name2args: 
            self.func_name2args[fname] = [] 
        self.func_name2args [fname].append(args)

    def _set_atom_list(self):
        terms = get_qterms(Merger.tran_sys, Merger.atoms, self.sub_repr_primes[0])
        for term in terms:
            (sign, atom)  = split_term(term)
            if atom.is_function_application():
                self.atoms.append(atom)
                fsymbol = atom.function_name()
                self.func_name2symbol[str(fsymbol)] = fsymbol
                args    = fsymbol.symbol_type()._param_types
                fname   = get_signed_func_name(sign, atom) 
                self.add_fname_args(fname, args)

        vprint_title(self.options, 'Merger: _set_atom_list', 5)
        vprint(self.options, f'terms:  {terms      }', 5)
        vprint(self.options, f'atoms:  {self.atoms }', 5)
        vprint(self.options, f'names:  {self.func_name2args}', 5)

    def _set_qprime_partitions(self):
        for prime in self.sub_repr_primes: 
            qprime = QPrime(prime, self.options)
            qprime.set_function_name_to_arguments()
            qprime.set_qvar_to_argument_signatures()
            qprime.set_sort_to_partition_signatures()
            qprime.set_qprime_partition_signature()
            self.qprimes.append(qprime)

    def _add_sort_max_num_parts(self, sort, part_len):
        if not sort in self.sort2max_num_parts:
            self.sort2max_num_parts[sort]  = 0
        num = self.sort2max_num_parts[sort]
        self.sort2max_num_parts[sort] = max(num, part_len)

    def _add_sort_part_sizes(self, sort, part_signatrs):
        if not sort in self.sort2part_sizes:
            self.sort2part_sizes[sort] = set()
        size_list = []
        for part in part_signatrs:
            elements = part.split(', ')
            size_list.append(len(elements))
        size_list.sort()
        self.sort2part_sizes[sort].add(tuple(size_list))

    def _set_partition_combinations(self):
        for qprime in self.qprimes:
            for sort, part_signatrs in qprime.sort2part_signatrs.items():
                self._add_sort_max_num_parts(sort, len(part_signatrs))
                self._add_sort_part_sizes(sort, part_signatrs)

    def _get_arg_signature(self, sort, fname, func_id, arg_id):
        return f'{sort}.{fname}.{func_id}.{arg_id}'

    def _add_sort_signature(self, sort, signature):
        if not sort in self.sort2signatrs:
            self.sort2signatrs[sort] = []
        self.sort2signatrs[sort].append(signature)

    def _set_argument_signatures(self):
        for fname, arg_list in self.func_name2args.items():
            for func_id, func_args in enumerate(arg_list):
                for arg_id, sort in enumerate(func_args):
                    signature = self._get_arg_signature(sort, fname, func_id, arg_id)
                    self._add_sort_signature(sort, signature)

        vprint_title(self.options, 'Merger: set_arguments_sorts', 5)
        vprint(self.options, f'sort to argument signatures: {self.sort2signatrs}', 5)

    def _get_partitions_signatures(self, partitions):
        partition_signatrs = []
        for partition in partitions: 
            partition.sort()
            signatrs = [', '.join(part) for part in partition]
            signatr  = ' | '.join(signatrs)
            partition_signatrs.append(signatr)
        return partition_signatrs

    def _get_max_num_parts(self, partitions):
        max_num = 1
        for partition in partitions:
           max_num = max(max_num, len(partition)) 
        return max_num

    def _get_sort_partitions(self, sort, signatrs):
        signatr_list = list(signatrs)
        signatr_list.sort()
        max_num_part = self.sort2max_num_parts[sort] 
        partitions = []
        if max_num_part == 1:
            partitions = list(set_partitions(signatr_list, max_num_part))
        else:
            partitions = list(set_partitions(signatr_list))
        # remove = set() 
        # for pid, partition in enumerate(partitions):
        #     size_list = []
        #     for part in partition:
        #         size_list.append(len(part))
        #     size_list.sort()
        #     if not tuple(size_list) in self.sort2part_sizes[sort]:
        #         remove.add(pid)
        
        # reduced_partition = []
        # for pid, partition in enumerate(partitions):
        #     if not pid in remove:
        #         reduced_partition.append(partition)
        # return reduced_partition 
        return partitions

    def _set_argument_partitions(self):
        sort_partition_signatrs = []
        for sort, signatrs in self.sort2signatrs.items():
            partitions = self._get_sort_partitions(sort, signatrs)
            self.sort_count[sort] = self._get_max_num_parts(partitions)
            partition_signatrs    = self._get_partitions_signatures(partitions)
            sort_partition_signatrs.append(partition_signatrs)
        self.partition_signatrs = set(product(*sort_partition_signatrs))

        vprint_title(self.options, 'Merger: set_argument_partitions', 5)
        vprint(self.options, 'partitions signatures:', 5)
        for pid, signatr in enumerate(self.partition_signatrs):
            vprint(self.options, f'[{pid}] {signatr}', 5)
        vprint(self.options, f'sort count: {self.sort_count}', 5)

    def _set_sort2qvars(self):
        for sort, count in self.sort_count.items():
            qvars = Merger.tran_sys._enum2qvar[sort]
            new_qvars = []
            for i in range(len(qvars), count):
                name = 'Q:' + str(sort) + f'{i}'
                new_qvars.append(Symbol(name, sort))
            self.sort2qvars[sort] = (qvars + new_qvars)[:count]
        vprint_title(self.options, 'Merger: set_sort2qvars', 5)
        vprint(self.options, f'sort2qvars: {self.sort2qvars}', 5)

    def _has_single_part(self, sort):
        return len(self.sort2qvars[sort]) == 1

    def _reset_sort_count(self):
        for sort in self.sort_count.keys():
            self.sort_count[sort] = 0
        vprint_title(self.options, 'Merger: _reset_sort_count', 5)
        vprint(self.options, f'sort_count: {self.sort_count}', 5)
                
    def _get_single_qvar(self, sort):
        return self.sort2qvars[sort][0]

    def _get_next_unused_qvar(self, sort):
        count = self.sort_count[sort]
        qvar = self.sort2qvars[sort][count]
        self.sort_count[sort] += 1
        return qvar

    def _get_qvar(self, sort):
        if self._has_single_part(sort):
            return self._get_single_qvar(sort) 
        else:
            return self._get_next_unused_qvar(sort)

    def _get_func_merged_args(self, fname, func_args):
        args = []
        for sort in func_args:
            arg = self._get_qvar(sort)
            args.append(arg)
        vprint_title(self.options, 'Merger: _get_func_merged_args', 5)
        vprint(self.options, f'{fname} args: {args}', 5)
        return args

    def _get_unconstrained_merged_terms(self):
        self._reset_sort_count()
        merged_terms = []
        for signed_fname, arg_list in self.func_name2args.items():
            for func_args in arg_list:
                merged_args = self._get_func_merged_args(signed_fname, func_args)
                (sign, fname) = split_signed_func_name(signed_fname)
                fsymbol = self.func_name2symbol[fname]
                merged_term = Function(fsymbol, merged_args)
                if sign == '1':
                    merged_term = Not(merged_term)
                merged_terms.append(merged_term)
        return merged_terms

    def _get_all_qvars(self):
        qvars_set = set()
        for qvars in self.sort2qvars.values():
            for qvar in qvars:
                qvars_set.add(qvar)
        return qvars_set

    def _get_unconstrained_qclause(self):
        merged_terms = self._get_unconstrained_merged_terms() 
        qvars = self._get_all_qvars()

        qstate = And(merged_terms)
        if len(qvars) != 0: 
            qstate = Exists(qvars, qstate)
        qclause = Not(qstate)
        vprint_title(self.options, 'Merger: _get_unconstrained_qclause', 5)
        vprint(self.options, f'qclause: {qclause}', 5)
        return qclause

    def _set_func_name_permutations(self):
        all_func_permutations = []
        fname_id = 0
        for fname, arg_list in self.func_name2args.items():
            self.func_name2id[fname] = fname_id
            fname_id += 1
            func_ids = list(range(len(arg_list)))
            func_permutations = permutations(func_ids)
            all_func_permutations.append(func_permutations)
        # cartesian product
        self.func_permutations = list(product(*all_func_permutations))
        vprint_title(self.options, 'Merger: set_func_name_permutations', 5)
        vprint(self.options, f'func permutations: {self.func_permutations}', 5)

    def _get_renamed_signatr(self, signatr, func_perm):
        partitions = []
        for sort_signatr in signatr:
            permuted_parts = []
            for part in sort_signatr.split(' | '):
                permuted_args = []
                for arg in part.split(', '):
                    components    = arg.split('.')
                    fname         = components[1] + '.' + components[2]
                    fname_id      = self.func_name2id[fname]
                    func_id       = int(components[3])
                    new_func_id   = func_perm[fname_id][func_id]
                    components[3] = str(new_func_id)
                    permuted_arg = '.'.join(components)
                    permuted_args.append(permuted_arg)
                permuted_args.sort()
                permuted_part = ', '.join(permuted_args)
                permuted_parts.append(permuted_part)
            permuted_parts.sort()
            partition = ' | '.join(permuted_parts)
            partitions.append(partition)
        partitions = tuple(partitions)
        return tuple(partitions)

    def _check_absent_partitions(self):
        for qprime in self.qprimes: 
            signatr = qprime.partition_signatr
            vprint(self.options, f'qprime signatr: {signatr}', 5)
            for func_perm in self.func_permutations:
                permuted_signatr = self._get_renamed_signatr(signatr, func_perm)
                if permuted_signatr in self.partition_signatrs:
                    self.partition_signatrs.remove(permuted_signatr)
        
        vprint_title(self.options, 'Merger: check_absent_partitions', 5)
        vprint(self.options, f'absent partitions: {self.partition_signatrs}', 5)

    def _map_arg_signature_to_qvar(self):
        self._reset_sort_count()
        for fname, arg_list in self.func_name2args.items():
            for func_id, func_args in enumerate(arg_list):
                for arg_id, sort in enumerate(func_args):
                    qvar = self._get_qvar(sort)
                    signatr = self._get_arg_signature(sort, fname, func_id, arg_id)
                    self.signatr2qvar[signatr] = qvar
        vprint_title(self.options, 'map_arg_signature_to_qvar', 5)
        vprint(self.options, f'signatr2qvar: {self.signatr2qvar}', 5)

    def _get_func_mapped_args(self, signed_fname, func_id, func_args):
        args = []
        for arg_id, sort in func_args:
            signatr = self._get_arg_signature(sort, signed_fname, func_id, arg_id)
            qvar = self.signatr2qvar[signatr]
            args.append(qvar)
        return args

    def _get_merged_terms(self):
        self._reset_sort_count()
        merged_terms = []
        for signed_fname, arg_list in self.func_name2args.items():
            for func_id, func_args in enumerate(arg_list):
                args = self._get_func_mapped_args(signed_fname, func_id, func_args)
                (sign, fname) = split_signed_func_name(signed_fname)
                fsymbol = self.func_name2symbol[fname]
                merged_term = Function(fsymbol, args)
                if sign == '1':
                    merged_term = Not(merged_term)
                merged_terms.append(merged_term)
        return merged_terms

    def _get_eq_class_qvars_constraint(self, eq_class):
        vprint_title(self.options, 'Merger: _get_eq_class_qvars_constraint', 5)
        args = eq_class.split(', ')
        qvars = []
        vprint(self.options, f'args: {args}', 5)
        for arg in args: 
            qvar = self.signatr2qvar[arg]
            qvars.append(qvar)
        vprint(self.options, f'qvars: {qvars}', 5)
        
        neq_terms = [] 
        for i in range(len(qvars)-1):
            for j in range(i+1, len(qvars)):
                if str(qvars[i]) != str(qvars[j]):
                    neq_qvars = [qvars[i], qvars[j]]
                    neq = Not(EqualsOrIff(neq_qvars[0], neq_qvars[1]))
                    neq_terms.append(neq)
        return neq_terms

    def _get_partition_qvars_constraint(self, partition):
        vprint_title(self.options, 'Merger: get_partition_qvars_constraint', 5)
        vprint(self.options, f'partition: {partition}', 5)
        constraint   = []
        for sort_partition in partition:
            vprint(self.options, f'sort partition: {sort_partition}', 5)
            eq_classes = sort_partition.split(' | ')
            for eq_class in eq_classes:
                vprint(self.options, f'eq class: {eq_class}', 5)
                constraint += self._get_eq_class_qvars_constraint(eq_class)
        vprint(self.options, f'constraint: {constraint}', 5)
        return constraint

    def _remove_redundant_qvars_constraint(self, constraints):
        vprint_title(self.options, 'Merger: _remove_redundant_qvars_constraint', 5)
        constraints_str = []
        for constraint in constraints:
            constraints_str.append(set([str(term) for term in constraint]))
        vprint(self.options,  f'constraint str representation: {constraints_str}', 5)
      
        fixed_point = False
        while len(constraints) >= 2 and not fixed_point:
            fixed_point = True
            remove = []
            for i  in range(1, len(constraints)):
                if constraints_str[0].issubset(constraints_str[i]):
                    remove.append(i)
                    fixed_point = False
            new_constraints     = []
            new_constraints_str = []
            i = 0
            for j in remove:
                if i<j :
                    new_constraints += constraints[i:j]
                    new_constraints_str += constraints_str[i:j]
                i = j+1
            constraints     = new_constraints
            constraints_str = new_constraints_str
        return constraints

    def _get_eq_constraints(self):
        # constraints:[[neq1, neq2, ...], [neq3, neq4, .... ]]
        constraints = [] 
        for partition in self.partition_signatrs:
            # constraint: [neq1, neq2, ...]
            constraint = self._get_partition_qvars_constraint(partition)
            constraints.append(constraint)
        constraints.sort(key=lambda constraint: len(constraint))
        vprint_title(self.options, 'Merger: get_eq_constraints', 5)
        vprint(self.options, f'partition signatrs: {self.partition_signatrs}', 5)  
        vprint(self.options, f'before remove constraints: {constraints}', 5)
        constraints = self._remove_redundant_qvars_constraint(constraints)
        vprint(self.options, f'after remove constraints: {constraints}', 5)
        return constraints

    def _get_constrained_qclause(self):
        self._map_arg_signature_to_qvar()
        merged_terms = self._get_unconstrained_merged_terms() 
        constraints = self._get_eq_constraints()
        qvars = self._get_all_qvars()

        # constraints:[[neq1, neq2, ...], [neq3, neq4, .... ]]
        neq_constraint_list = []
        for constraint in constraints:
            # constraint = [neq1, neq2,...]
            # neq_constraint = neq1 | neq2
            if len(constraint):
                neq_constraint = Or(constraint)
                neq_constraint_list.append(neq_constraint)
        # neq_constraint = (neq1 | neq2) & (neq3 | neq4)
        if len(neq_constraint_list):
            neq_constraint = And(neq_constraint_list)
            merged_terms.append(neq_constraint)

        # qstate: exist Q (merge_terms & ((neq1 | neq2) & (neq3 | neq4)) )
        qstate = And(merged_terms)
        if len(qvars) != 0: 
            qstate = Exists(qvars, qstate)
        # qstate: forall Q ( ~merge_terms | (eq1 & eq2) | (eq3 & eq4) )
        qclause = Not(qstate)
        vprint_title(self.options, 'Merger: _get_constrained_qclause', 5)
        vprint(self.options, f'qclause: {qclause}', 5)
        return qclause 

    def merge(self):
        self._set_atom_list()
        self._set_qprime_partitions()
        self._set_partition_combinations()
        self._set_argument_signatures()
        self._set_argument_partitions()
        self._set_sort2qvars()
        if len(self.partition_signatrs) == len(self.qprimes):
            qclause = self._get_unconstrained_qclause() 
            vprint_title(self.options, 'merge_qclauses', 5)
            vprint(self.options, f'qclause: {pretty_print_str(qclause)}', 5)
            return qclause

        self._set_func_name_permutations()
        self._check_absent_partitions()
        qclause = self._get_constrained_qclause()
        vprint_title(self.options, 'merge_qclauses', 5)
        vprint(self.options, f'qclause: {pretty_print_str(qclause)}', 5)
        return qclause

    @staticmethod
    def setup(atoms, tran_sys) -> None:
        Merger.atoms    = atoms
        Merger.tran_sys = tran_sys
        QPrime.setup(atoms, tran_sys)