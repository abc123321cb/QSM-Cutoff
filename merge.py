from ivy import ivy_logic as il
from ivy import ivy_logic_utils as ilu
from transition_system import TransitionSystem
from prime import Prime 
from util import QrmOptions
from util import FormulaUtility as futil
from verbose import *
from more_itertools import set_partitions
from itertools import product, permutations

def get_used_qvars(sort2qvars, sort):
    if not sort in sort2qvars:         
        sort2qvars[sort] = []
    qvars = sort2qvars[sort]
    return qvars

def get_next_unused_qvar(tran_sys : TransitionSystem, sort, qvars):
    qvar_id = len(qvars)
    qvar_name = sort.name[0].upper() + str(qvar_id)
    qvar      = il.Variable(qvar_name, sort) 
    return qvar

def replace_var_with_qvar(tran_sys : TransitionSystem, terms):
    # relabel each var into qvar with index being order of occurrence
    # e.g. n2 n0 n1 m ---> Qn0 Qn1 Qn2 Qm0
    state =  il.And(*terms) if len(terms) != 0 else il.And()
    variables  = ilu.used_constants_ast(state)
    var2qvar   = {}
    sort2qvars = {}
    for var in sorted(variables, key=str):
        sort = var.sort
        if not sort in tran_sys.sort2consts:
            continue
        qvars  = get_used_qvars(sort2qvars, sort)
        qvar   = get_next_unused_qvar(tran_sys, sort, qvars) 
        qvars.append(qvar)
        var2qvar[var] = qvar

    qstate = il.substitute(state, var2qvar)
    qterms = futil.flatten_cube(qstate)
    return qterms

def add_member_terms_for_dependent_sorts(atoms, tran_sys : TransitionSystem):
    terms = []
    args = set()
    for atom in atoms:
        atom_args = atom.args
        if il.is_equals(atom):
            atom_args = [atom_args[1]]
        for arg in atom_args:
            args.add(arg)
    for arg in args:
        if arg.sort in tran_sys.dep_types:
            set_sort = arg.sort
            set_id   = 0
            consts   = Merger.tran_sys.sort2consts[set_sort]
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

def split_signed_func_name(func_name):
    splitted = func_name.split('.')
    is_neg  = splitted[0]
    fname   = splitted[1]
    return (is_neg, fname)

def get_signed_func_name(sign, fname : str, is_equals=False):
    if is_equals:
        return sign + '.' + fname + '=' 
    else:
        return sign + '.' + fname

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
        self.signatr2qvar       = {}

    def add_fname_args(self, fname, args):
        if not fname in self.func_name2args: 
            self.func_name2args[fname] = [] 
        self.func_name2args [fname].append(args)

    def set_function_name_to_arguments(self):
        terms = get_qterms(QPrime.tran_sys, QPrime.atoms, self.qprime)
        for term in terms:
            (sign, atom)  = split_term(term)
            if il.is_app(atom):
                fsymbol = atom.func
                fname = get_signed_func_name(sign, str(fsymbol))
                self.add_fname_args(fname, atom.args)
            elif il.is_equals(atom):
                lhs = atom.args[0]
                # func_name2symbol
                fsymbol = None
                if il.is_app(lhs):
                    fsymbol = lhs.func
                else:
                    fsymbol = lhs
                args = []
                if il.is_app(lhs):
                    args += fsymbol.sort.dom
                args.append(atom.args[1])
                fname = get_signed_func_name(sign, str(fsymbol), is_equals=True) 
                self.add_fname_args(fname, tuple(args))

        vprint_title(self.options, 'QPrime: set_function_name_to_arguments', 5)
        vprint(self.options, f'terms: {terms}', 5)
        vprint(self.options, f'func_name2args: {self.func_name2args}', 5)

    def _get_arg_signature(self, signed_fname, func_id, arg_id, qvar):
        sort = qvar.sort
        signatr = f'{sort.name}.{signed_fname}.{func_id}.{arg_id}'
        return signatr

    def _add_qvar_signature(self, qvar, signatr):
        if not qvar in self.qvar2arg_signatrs:
            self.qvar2arg_signatrs[qvar] = [] 
        self.qvar2arg_signatrs[qvar].append(signatr)
        self.signatr2qvar[signatr] = qvar
        
    def set_qvar_to_argument_signatures(self):
        for fname, arg_list in self.func_name2args.items():
            for func_id, func_args in enumerate(arg_list):
                for arg_id, qvar in enumerate(func_args):
                    signatr = self._get_arg_signature(fname, func_id, arg_id, qvar)
                    self._add_qvar_signature(qvar, signatr)
        vprint_title(self.options, 'QPrime: set_qvar_to_argument_signatures', 5)
        vprint(self.options, f'qvar2arg_signatr: {self.qvar2arg_signatrs}', 5)
        vprint(self.options, f'signatr2qvar: {self.signatr2qvar}', 5)

    def _add_sort_part_signatures(self, qvar, part_signatr):
        sort = qvar.sort
        if not sort in self.sort2part_signatrs:
            self.sort2part_signatrs[sort] = []
        self.sort2part_signatrs[sort].append(part_signatr)

    def set_sort_to_partition_signatures(self):
        for qvar, arg_signatrs in self.qvar2arg_signatrs.items():
            arg_signatrs.sort()
            part_signatr = ', '.join(arg_signatrs)
            self._add_sort_part_signatures(qvar, part_signatr)
        vprint_title(self.options, 'QPrime: set_sort_to_partition_signatures', 5)
        vprint(self.options, f'sort2partition: {self.sort2part_signatrs}', 5)

    def set_qprime_partition_signature(self):
        from itertools import product
        sort_partition_signatrs = []
        for sort, part_signatrs in self.sort2part_signatrs.items():
            part_signatrs.sort()
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
        # basics
        self.atoms              = []
        self.func_name2args     = {}
        self.func_name2symbol   = {}
        self.func_name2id       = {}
        # qprimes partition
        self.qprimes            = []
        # argument signatures 
        self.sort2signatrs        = {}
        self.sort2signatr_classes = {}
        # partitions
        self.sort2partitions      = {}
        self.sort_count           = {}
        self.sort2qvars           = {}
        self.use_absent           = True
        self.partition_signatrs   = set() 
        self.absent_signatrs      = set() 
        self.present_signatrs     = set() 
        self.func_permutations    = []
        self.signatr2qvar         = {}

    def _add_fname_args(self, fname, args):
        if not fname in self.func_name2args: 
            self.func_name2args[fname] = [] 
        self.func_name2args[fname].append(args)

    def initialize(self):
        # set: (1) self.atoms, (2) self.func_name2symbol, (3) self.func2name_args
        terms = get_qterms(Merger.tran_sys, Merger.atoms, self.sub_repr_primes[0])
        for term in terms:
            (sign, atom)  = split_term(term)
            # atoms
            self.atoms.append(atom)
            if il.is_app(atom):
                # func_name2symbol
                fsymbol = atom.func
                self.func_name2symbol[str(fsymbol)] = fsymbol
                # func_name2args
                args    = fsymbol.sort.dom
                fname   = get_signed_func_name(sign, str(fsymbol)) 
                self._add_fname_args(fname, args)
            elif il.is_equals(atom):
                lhs = atom.args[0]
                # func_name2symbol
                fsymbol = None
                if il.is_app(lhs):
                    fsymbol = lhs.func
                else:
                    fsymbol = lhs
                self.func_name2symbol[str(fsymbol)+'='] = fsymbol
                # func_name2args
                args = []
                if il.is_app(lhs):
                    args += fsymbol.sort.dom
                args.append(atom.arg(1))
                fname = get_signed_func_name(sign, str(fsymbol), is_equals=True) 
                self._add_fname_args(fname, tuple(args))

        vprint_title(self.options, 'Merger: _set_atom_list', 5)
        vprint(self.options, f'terms:  {terms      }', 5)
        vprint(self.options, f'atoms:  {self.atoms }', 5)
        vprint(self.options, f'names:  {self.func_name2args}', 5)

    def set_qprime_partitions(self):
        for prime in self.sub_repr_primes: 
            qprime = QPrime(prime, self.options)
            qprime.set_function_name_to_arguments()
            qprime.set_qvar_to_argument_signatures()
            qprime.set_sort_to_partition_signatures()
            qprime.set_qprime_partition_signature()
            self.qprimes.append(qprime)

    def _get_qvar_signature(self, signature):
        qvars = []
        for qid, qprime in enumerate(self.qprimes):
            qvar = qprime.signatr2qvar[signature]
            qvars.append(f'{str(qvar)}.{qid}')
        return '.'.join(qvars)

    def _get_arg_signature(self, sort, fname, func_id, arg_id):
        return f'{sort.name}.{fname}.{func_id}.{arg_id}'

    def _add_sort_signature(self, sort, arg_signature):
        if not sort in self.sort2signatr_classes:
            self.sort2signatr_classes[sort] = {} 
        qvar_signatr = self._get_qvar_signature(arg_signature)
        if not qvar_signatr in self.sort2signatr_classes[sort]:
            self.sort2signatr_classes[sort][qvar_signatr] = []
        self.sort2signatr_classes[sort][qvar_signatr].append(arg_signature)

    def _collapse_signature_classes(self):
        # collapse arg signatures with same qvar signature (appears the same eq class in qprimes)
        for sort, signatr_classes in self.sort2signatr_classes.items():
            signatrs = []
            for signatr_class in signatr_classes.values():
                signatr_class.sort()
                signatrs.append(', '.join(signatr_class))
            signatrs.sort()
            self.sort2signatrs[sort] = signatrs

    def _set_partition_universe(self):
        for fname, arg_list in self.func_name2args.items():
            for func_id, func_args in enumerate(arg_list):
                for arg_id, sort in enumerate(func_args):
                    arg_signature = self._get_arg_signature(sort, fname, func_id, arg_id)
                    self._add_sort_signature(sort, arg_signature)
        self._collapse_signature_classes()
        
    def _are_all_eq_classes_singletons(self, eq_classes, singletons):
        for eq_class in eq_classes: 
            if not eq_class in singletons:
                return False
        return True
    
    def _need_enumerate_partitions(self, sort):
        sort_size    = len(Merger.tran_sys.sort2consts[sort])
        num_signatrs = len(self.sort2signatrs[sort])
        vprint_title(self.options, 'need_enumerate_partitions', 5)
        vprint(self.options, f'sort size: {sort_size}', 5)
        vprint(self.options, f'num signatures: {num_signatrs}', 5)
        if num_signatrs >= 6: # enumerate all partitions will be infeasible
            vprint(self.options, 'False', 5)
            return False
        for qprime in self.qprimes: 
            eq_classes = qprime.sort2part_signatrs[sort]
            if len(eq_classes) == min(sort_size, num_signatrs):
                vprint(self.options, f'eq classes: {eq_classes}', 5)
                vprint(self.options, 'True', 5)
                return True 
        vprint(self.options, 'False', 5)
        return False 

    def _enumerate_sort_partitions(self, signatrs):
        signatr_list = list(signatrs)
        signatr_list.sort()
        partitions   = list(set_partitions(signatr_list))
        return partitions

    def _make_singletons_partition(self, signatrs):
        signatr_list = list(signatrs)
        parts = []
        for element in signatr_list:
            parts.append([element])
        partitions = [parts]
        return partitions

    def _set_sort_to_partitions(self):
        for sort, signatrs in self.sort2signatrs.items():
            partitions = self._enumerate_sort_partitions(signatrs)
            self.use_absent = True
            partitions = []
            if self._need_enumerate_partitions(sort):
                partitions = self._enumerate_sort_partitions(signatrs)
                self.use_absent = True
            else:
                partitions = self._make_singletons_partition(signatrs)
                self.use_absent = False 
            self.sort2partitions[sort] = partitions

    def _get_max_num_parts(self, partitions):
        max_num = 1
        for partition in partitions:
           max_num = max(max_num, len(partition)) 
        return max_num

    def _set_sort_count(self):
        for sort, partitions in self.sort2partitions.items():
            self.sort_count[sort] = self._get_max_num_parts(partitions)

    def _set_sort2qvars(self):
        self._set_sort_count()
        for sort, count in self.sort_count.items():
            qvars = [] 
            for qvar_id in range(len(qvars), count):
                qvar_name = sort.name[0].upper() + str(qvar_id)
                qvars.append(il.Variable(qvar_name, sort))
            self.sort2qvars[sort] = qvars

    def _remove_infeasible_partition(self):
        for sort, partitions in self.sort2partitions.items():
            sort_size = len(Merger.tran_sys.sort2consts[sort])
            remove = set()
            for pid, partition in enumerate(partitions):
                if len(partition) > sort_size:
                    remove.add(pid)
            reduced_partitions = []
            for pid, partition in enumerate(partitions):
                if not pid in remove:
                    reduced_partitions.append(partition)
            self.sort2partitions[sort] = reduced_partitions

    def _get_partitions_signatures(self, partitions):
        vprint_title(self.options, 'get_partitions_signatures', 5)
        vprint(self.options, f'partitions: {partitions}', 5)
        for partition in partitions:
            for part in partition:
                part.sort()
            partition.sort()
        vprint(self.options, f'partitions: {partitions}', 5)

        partition_signatrs = []
        for partition in partitions: 
            signatrs = []
            for part in partition:
                part_str  = ', '.join(part)
                part_list = part_str.split(', ')
                part_list.sort()
                signatrs.append(', '.join(part_list))
            signatr  = ' | '.join(signatrs)
            partition_signatrs.append(signatr)
        return partition_signatrs

    def _set_partition_signatures(self):
        sort_partition_signatrs = []
        for sort, partitions in self.sort2partitions.items():
            partition_signatrs  = self._get_partitions_signatures(partitions)
            sort_partition_signatrs.append(partition_signatrs)
        self.partition_signatrs = set(product(*sort_partition_signatrs))

    def set_partitions(self):
        self._set_partition_universe()
        self._set_sort_to_partitions()
        self._set_sort2qvars()
        if self.use_absent:
            self._remove_infeasible_partition()
        self._set_partition_signatures()

        vprint_title(self.options, 'Merger: set_partitions', 5)
        vprint(self.options, f'sort to argument signatures: {self.sort2signatrs}', 5)
        vprint(self.options, 'partitions signatures:', 5)
        for pid, signatr in enumerate(self.partition_signatrs):
            vprint(self.options, f'[{pid}] {signatr}', 5)
        vprint(self.options, f'sort count: {self.sort_count}', 5)
        vprint(self.options, f'sort2qvars: {self.sort2qvars}', 5)

    def can_infer_unconstrained(self):
        can_infer =  ( len(self.partition_signatrs) == len(self.qprimes) ) 
        vprint_title(self.options, 'can_infer_unconstrained', 5)
        vprint(self.options, can_infer, 5)
        return can_infer

    def _reset_sort_count(self):
        for sort in self.sort_count.keys():
            self.sort_count[sort] = 0
        vprint_title(self.options, 'Merger: _reset_sort_count', 5)
        vprint(self.options, f'sort_count: {self.sort_count}', 5)
                
    def _get_next_unused_qvar(self, sort):
        count = self.sort_count[sort]
        qvar = self.sort2qvars[sort][count]
        self.sort_count[sort] += 1
        return qvar

    def _map_arg_signature_to_qvar(self):
        self._reset_sort_count()
        for sort, signatr_classes in self.sort2signatr_classes.items():
            for arg_signatrs in signatr_classes.values():
                qvar = self._get_next_unused_qvar(sort)
                for signatr in arg_signatrs:
                    self.signatr2qvar[signatr] = qvar
        vprint_title(self.options, 'map_arg_signature_to_qvar', 5)
        vprint(self.options, f'signatr2qvar: {self.signatr2qvar}', 5)

    def _get_func_mapped_args(self, signed_fname, func_id, func_args):
        args = []
        for arg_id, sort in enumerate(func_args):
            signatr = self._get_arg_signature(sort, signed_fname, func_id, arg_id)
            qvar = self.signatr2qvar[signatr]
            args.append(qvar)
        return args

    def _get_merged_term(self, signed_fname, func_id, func_args):
        args = self._get_func_mapped_args(signed_fname, func_id, func_args)
        (sign, fname) = split_signed_func_name(signed_fname)
        fsymbol = self.func_name2symbol[fname]
        merged_term = None
        if fname.endswith('='):
            lhs = None
            if len(args) > 1:
                lhs = il.App(fsymbol, *args[:-1])
            else: 
                lhs = fsymbol
            rhs = args[-1]
            merged_term = il.Equals(lhs,rhs)
        else:
            merged_term = il.App(fsymbol, *args)
        if sign == '1':
            merged_term = il.Not(merged_term)
        return merged_term

    def _get_merged_terms(self):
        self._map_arg_signature_to_qvar()
        merged_terms = []
        for signed_fname, arg_list in self.func_name2args.items():
            for func_id, func_args in enumerate(arg_list):
                merged_term = self._get_merged_term(signed_fname, func_id, func_args)
                merged_terms.append(merged_term)
        return merged_terms

    def get_unconstrained_qclause(self):
        merged_terms = self._get_merged_terms() 
        qvars = self._get_all_qvars()

        qstate = il.And(*merged_terms)
        if len(qvars) != 0: 
            qstate = il.Exists(qvars, qstate)
        qclause = il.Not(qstate)
        vprint_title(self.options, 'Merger: _get_unconstrained_qclause', 5)
        vprint(self.options, f'qclause: {str(qclause)}', 5) 
        return qclause

    def _get_all_qvars(self):
        qvars_set = set()
        for qvars in self.sort2qvars.values():
            for qvar in qvars:
                qvars_set.add(qvar)
        return qvars_set

    def set_func_name_permutations(self):
        all_func_permutations = []
        fname_id = 0
        for fname, arg_list in self.func_name2args.items():
            self.func_name2id[fname] = fname_id
            fname_id += 1
            func_ids  = list(range(len(arg_list)))
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

    def set_absent_present_partitions(self):
        self.absent_signatrs    = self.partition_signatrs.copy()
        self.present_signatrs   = set()
        self.partition_signatrs = set()
        for qprime in self.qprimes: 
            signatr = qprime.partition_signatr
            for func_perm in self.func_permutations:
                permuted_signatr = self._get_renamed_signatr(signatr, func_perm)
                if permuted_signatr in self.absent_signatrs:
                    self.absent_signatrs.remove(permuted_signatr)
                self.present_signatrs.add(permuted_signatr)
        
        vprint_title(self.options, 'Merger: check_absent_partitions', 5)
        vprint(self.options, 'absent partitions:', 5)
        for signatr in self.absent_signatrs:
            vprint(self.options, f'{signatr}', 5)
        vprint(self.options, 'present partitions:', 5)
        for signatr in self.present_signatrs:
            vprint(self.options, f'{signatr}', 5)

    def _get_eq_class_qvars_constraint(self, eq_class):
        vprint_title(self.options, 'Merger: _get_eq_class_qvars_constraint', 5)
        args = eq_class.split(', ')
        qvars = []
        vprint(self.options, f'args: {args}', 5)
        for arg in args: 
            qvar = self.signatr2qvar[arg]
            qvars.append(qvar)
        vprint(self.options, f'qvars: {qvars}', 5)
        
        neq_terms = set()
        for i in range(len(qvars)-1):
            for j in range(i+1, len(qvars)):
                if str(qvars[i]) != str(qvars[j]):
                    neq_qvars = [qvars[i], qvars[j]]
                    neq = il.Not(il.Equals(neq_qvars[0], neq_qvars[1]))
                    neq_terms.add(neq)
        return list(neq_terms)

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
        vprint_title(self.options, 'Merger: remove_redundant_qvars_constraint', 5)
        vprint(self.options, f'partition signatrs: {self.absent_signatrs}', 5)  
        vprint(self.options, f'before remove constraints: {constraints}', 5)

        constraints_str = []
        for constraint in constraints:
            constraints_str.append(set([str(term) for term in constraint]))
      
        fixed_point = False
        while len(constraints) >= 2 and not fixed_point:
            fixed_point = True
            remove = set() 
            for i  in range(1, len(constraints)):
                if constraints_str[0].issubset(constraints_str[i]):
                    remove.add(i)
                    fixed_point = False
            reduced_constraints     = [constraints[0]]
            reduced_constraints_str = [constraints_str[0]]
            for i in range(1, len(constraints)):
                if not i in remove:
                    reduced_constraints.append(constraints[i])
                    reduced_constraints_str.append(constraints_str[i])
            constraints     = reduced_constraints
            constraints_str = reduced_constraints_str

        vprint(self.options, f'after remove constraints: {constraints}', 5)
        return constraints

    def _get_eq_constraints(self):
        # constraints:[[neq1, neq2, ...], [neq3, neq4, .... ]]
        constraints = [] 
        use_signatrs = self.absent_signatrs if self.use_absent else self.present_signatrs
        for partition in use_signatrs:
            # constraint: [neq1, neq2, ...]
            constraint = self._get_partition_qvars_constraint(partition)
            constraints.append(constraint)
        constraints.sort(key=lambda constraint: len(constraint))
        if self.use_absent:
            constraints = self._remove_redundant_qvars_constraint(constraints)
        return constraints

    def get_constrained_qclause(self): 
        merged_terms = self._get_merged_terms() 
        constraints = self._get_eq_constraints()
        qvars = self._get_all_qvars()

        # constraints:[[neq1, neq2, ...], [neq3, neq4, .... ]]
        neq_constraint_list = []
        for constraint in constraints:
            # constraint = [neq1, neq2,...]
            # neq_constraint = neq1 | neq2
            if len(constraint):
                neq_constraint = il.Or(*constraint)
                neq_constraint_list.append(neq_constraint)
        # neq_constraint = (neq1 | neq2) & (neq3 | neq4)
        if len(neq_constraint_list):
            neq_constraint = il.And(*neq_constraint_list)
            if self.use_absent:
                merged_terms.append(neq_constraint)
            else:
                merged_terms.append(il.Not(neq_constraint))

        # qstate: exist Q (merge_terms & ((neq1 | neq2) & (neq3 | neq4)) )
        qstate = il.And(*merged_terms)
        if len(qvars) != 0: 
            qstate = il.Exists(qvars, qstate)
        # qstate: forall Q ( ~merge_terms | (eq1 & eq2) | (eq3 & eq4) )
        qclause = il.Not(qstate)
        vprint_title(self.options, 'Merger: _get_constrained_qclause', 5)
        vprint(self.options, f'qclause: {str(qclause)}', 5)
        return qclause 

    def merge(self):
        self.initialize()
        self.set_qprime_partitions() 
        self.set_partitions()
        if self.can_infer_unconstrained():
            qclause = self.get_unconstrained_qclause()
            qclause = futil.de_morgan(qclause)
            return qclause 
        else:
            self.set_func_name_permutations()
            self.set_absent_present_partitions()
            qclause = self.get_constrained_qclause()
            qclause = futil.de_morgan(qclause)
            return qclause 

    @staticmethod
    def setup(atoms, tran_sys) -> None:
        Merger.atoms    = atoms
        Merger.tran_sys = tran_sys
        QPrime.setup(atoms, tran_sys)