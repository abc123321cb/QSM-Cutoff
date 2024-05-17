from typing import List
from pysmt.shortcuts import Symbol, And, Or, EqualsOrIff, Not, ForAll, Exists, Function, TRUE
from frontend.utils import *
from frontend.vmt_parser import TransitionSystem
from prime import Prime 
from util import QrmOptions
from verbose import *
from more_itertools import set_partitions
from itertools import product, permutations

def get_flattened_terms(formula):
    assert(formula.is_not())
    formulaNeg = formula.arg(0)
    assert(formulaNeg.is_exists())
    matrix = formulaNeg.arg(0)
    terms = list(flatten_and(matrix))
    return terms

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

class QClause():
    def __init__(self, qclause, options):
        self.options            = options
        self.qclause            = qclause
        self.func_name2args     = {}
        self.qvar2arg_signatrs  = {}
        self.sort2part_signatrs = {}

    def add_fname_args(self, fname, args):
        if not fname in self.func_name2args: 
            self.func_name2args[fname] = [] 
        self.func_name2args [fname].append(args)

    def set_function_name_to_arguments(self):
        terms = get_flattened_terms(self.qclause)
        for term in terms:
            (sign, atom)  = split_term(term)
            if atom.is_function_application():
                fname = get_signed_func_name(sign, atom)
                self.add_fname_args(fname, atom.args())

        vprint_title(self.options, 'QClause: set_function_name_to_arguments', 5)
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
        vprint_title(self.options, 'QClause: set_qvar_to_argument_signatures', 5)
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
        vprint_title(self.options, 'QClause: set_sort_to_partition_signatures', 5)
        vprint(self.options, f'sort2partition: {self.sort2part_signatrs}', 5)

    def set_qclause_partition_signature(self):
        from itertools import product
        sort_partition_signatrs = []
        for sort, part_signatrs in self.sort2part_signatrs.items():
            signatr = ' | '.join(part_signatrs)
            sort_partition_signatrs.append([signatr])
        self.partition_signatr = list(product(*sort_partition_signatrs))[0]
        vprint_title(self.options, 'QClause: set_qclause_partition_signatures', 5)
        vprint(self.options, f'sort partition signature: {sort_partition_signatrs}', 5)
        vprint(self.options, f'partition signature: {self.partition_signatr}', 5)

class QClauseMerger():
    def __init__(self, options, tran_sys, sub_qclauses):
        self.options            = options
        self.tran_sys           = tran_sys
        self.sub_qclauses       = sub_qclauses 
        self.qclauses           = []
        self.atoms              = []
        self.func_name2args     = {}
        self.func_name2symbol   = {}
        self.func_name2id       = {}
        self.sort_count         = {}
        self.sort2signatrs      = {}
        self.sort_partitions    = []
        self.partitions         = []
        self.partition_signatrs = []
        self.sort2qvars         = {}
        self.func_permutations  = []
        self.signatr2qvar       = {}

    def add_fname_args(self, fname, args):
        if not fname in self.func_name2args: 
            self.func_name2args[fname] = [] 
        self.func_name2args [fname].append(args)

    def _set_atom_list(self):
        terms = get_flattened_terms(self.sub_qclauses[0])
        for term in terms:
            (sign, atom)  = split_term(term)
            if atom.is_function_application():
                self.atoms.append(atom)
                fsymbol = atom.function_name()
                self.func_name2symbol[str(fsymbol)] = fsymbol
                args    = fsymbol.symbol_type()._param_types
                fname   = get_signed_func_name(sign, atom) 
                self.add_fname_args(fname, args)

        vprint_title(self.options, 'QClauseMerger: _set_atom_list', 5)
        vprint(self.options, f'terms:  {terms      }', 5)
        vprint(self.options, f'atoms:  {self.atoms }', 5)
        vprint(self.options, f'names:  {self.func_name2args}', 5)

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

        vprint_title(self.options, 'QClauseMerger: set_arguments_sorts', 5)
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

    def _set_argument_partitions(self):
        sort_partition_signatrs = []
        for sort, signatrs in self.sort2signatrs.items():
            signatr_list = list(signatrs)
            signatr_list.sort()
            partitions   = list(set_partitions(signatr_list))
            self.sort_count[sort] = self._get_max_num_parts(partitions)
            partition_signatrs    = self._get_partitions_signatures(partitions)
            sort_partition_signatrs.append(partition_signatrs)
        self.partition_signatrs = set(product(*sort_partition_signatrs))

        vprint_title(self.options, 'QClauseMerger: set_argument_partitions', 5)
        vprint(self.options, 'partitions signatures:', 5)
        for pid, signatr in enumerate(self.partition_signatrs):
            vprint(self.options, f'[{pid}] {signatr}', 5)
        vprint(self.options, f'sort count: {self.sort_count}', 5)

    def _set_sort2qvars(self):
        for sort, count in self.sort_count.items():
            qvars = self.tran_sys._enum2qvar[sort]
            new_qvars = []
            for i in range(len(qvars), count):
                name = 'Q:' + str(sort) + f'{i}'
                new_qvars.append(Symbol(name, sort))
            self.sort2qvars[sort] = (qvars + new_qvars)[:count]
        vprint_title(self.options, 'QClauseMerger: set_sort2qvars', 5)
        vprint(self.options, f'sort2qvars: {self.sort2qvars}', 5)

    def _has_single_part(self, sort):
        return len(self.sort2qvars[sort]) == 1

    def _reset_sort_count(self):
        for sort in self.sort_count.keys():
            self.sort_count[sort] = 0
        vprint_title(self.options, 'QClauseMerger: _reset_sort_count', 5)
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
        vprint_title(self.options, 'QClauseMerger: _get_func_merged_args', 5)
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
        vprint_title(self.options, 'QClauseMerger: _get_unconstrained_qclause', 5)
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
        vprint_title(self.options, 'QClauseMerger: set_func_name_permutations', 5)
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

    def _set_qclause_partitions(self):
        for sub_qclause in self.sub_qclauses: 
            qclause = QClause(sub_qclause, self.options)
            qclause.set_function_name_to_arguments()
            qclause.set_qvar_to_argument_signatures()
            qclause.set_sort_to_partition_signatures()
            qclause.set_qclause_partition_signature() 
            self.qclauses.append(qclause)
        
    def _check_absent_partitions(self):
        for qclause in self.qclauses: 
            signatr = qclause.partition_signatr
            vprint(self.options, f'qclause signatr: {signatr}', 5)
            for func_perm in self.func_permutations:
                permuted_signatr = self._get_renamed_signatr(signatr, func_perm)
                if permuted_signatr in self.partition_signatrs:
                    self.partition_signatrs.remove(permuted_signatr)
        vprint_title(self.options, 'QClauseMerger: check_absent_partitions_among_qclauses', 5)
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
        vprint_title(self.options, 'QClauseMerger: _get_eq_class_qvars_constraint', 5)
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
                neq_qvars = [qvars[i], qvars[j]]
                neq = Not(EqualsOrIff(neq_qvars[0], neq_qvars[1]))
                neq_terms.append(neq)
        return neq_terms

    def _get_partition_qvars_constraint(self, partition):
        vprint_title(self.options, 'QClauseMerger: get_partition_qvars_constraint', 5)
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
        vprint_title(self.options, 'QClauseMerger: _remove_redundant_qvars_constraint', 5)
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
            for i in remove:
                del constraints_str[i]
                del constraints[i] 
        return constraints

    def _get_eq_constraints(self):
        # constraints:[[neq1, neq2, ...], [neq3, neq4, .... ]]
        constraints = [] 
        for partition in self.partition_signatrs:
            # constraint: [neq1, neq2, ...]
            constraint = self._get_partition_qvars_constraint(partition)
            constraints.append(constraint)
        constraints.sort(key=lambda constraint: len(constraint))
        vprint_title(self.options, 'QClauseMerger: get_eq_constraints', 5)
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
            neq_constraint = Or(constraint)
            neq_constraint_list.append(neq_constraint)
        # neq_constraint = (neq1 | neq2) & (neq3 | neq4)
        neq_constraint = And(neq_constraint_list)
        merged_terms.append(neq_constraint)

        # qstate: exist Q (merge_terms & ((neq1 | neq2) & (neq3 | neq4)) )
        qstate = And(merged_terms)
        if len(qvars) != 0: 
            qstate = Exists(qvars, qstate)
        # qstate: forall Q ( ~merge_terms | (eq1 & eq2) | (eq3 & eq4) )
        qclause = Not(qstate)
        vprint_title(self.options, 'QClauseMerger: _get_constrained_qclause', 5)
        vprint(self.options, f'qclause: {qclause}', 5)
        return qclause 

    def merge(self):
        self._set_atom_list()
        self._set_argument_signatures()
        self._set_argument_partitions()
        self._set_sort2qvars()
        if len(self.partition_signatrs) == len(self.sub_qclauses):
           qclause = self._get_unconstrained_qclause() 
           return qclause

        self._set_func_name_permutations()
        self._set_qclause_partitions()
        self._check_absent_partitions()
        qclause = self._get_constrained_qclause()
        return qclause

def merge_qclauses(options, tran_sys, sub_results):
    vprint_title(options, 'merge_qclauses', 5)
    if len(sub_results) == 1:
        qclause = sub_results[0][0]
        vprint(options, f'qclause: {pretty_print_str(qclause)}', 5)
        return qclause 

    sub_qclauses = []
    for result in sub_results:
        qclause = result[0]
        qtype   = result[1]
        if qtype != 'forall':
            vprint(options, '[QI ERROR]: Cannot handle non universal suborbit merging')
            sys.exit(1) 
        vprint(options, f'qclause: {pretty_print_str(qclause)}', 5)
        sub_qclauses.append(qclause)

    merger = QClauseMerger(options, tran_sys, sub_qclauses)
    qclause = merger.merge()
    vprint(options, f'qclause: {pretty_print_str(qclause)}', 5)
    return qclause