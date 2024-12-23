from ivy import ivy_logic as il
from ivy import ivy_logic_utils as ilu
from transition_system import TransitionSystem
from prime import Prime 
from util import QrmOptions
from util import FormulaUtility as futil
from verbose import *
from qutil import *
from itertools import product, permutations
from signature import *
from qformula import QFormula, ConstraintMode, QuantifierMode
from finite_ivy_instantiate import *

class QPrime():
    # static members
    atoms = []
    tran_sys : TransitionSystem

    def __init__(self, prime : Prime, options : QrmOptions):
        self.options        = options
        self.prime          = prime
        self.terms          = get_terms(QPrime.tran_sys, QPrime.atoms, self.prime)
        vprint_title(self.options, 'QPrime', 5)
        self.binding        = ConstArgBinding(self.terms, self.options)
        self.arg_partition  = ArgPartition(self.binding, self.options)

    @staticmethod
    def setup(atoms, tran_sys) -> None:
        QPrime.atoms    = atoms
        QPrime.tran_sys = tran_sys

class AbsentConstraint():
    def __init__(self, pap : ProductArgPartition, ap_list: List[ArgPartition], options : QrmOptions):
        self.options : QrmOptions         = options
        self.pap : ProductArgPartition    = pap
        self.ap_list : List[ArgPartition] = ap_list
        # sort2partitions
        self.sort2partitions : Dict[il.EnumeratedSort, List[SortPartitionSignature]] = {}
        self._set_sort_to_partitions()

        # partitions
        self.partitions : List[PartitionSignature] = []
        self._set_partitions()  

    def _set_sort_to_partitions(self) -> None:
        for sort, part_sig in self.pap.sort2part_sig.items():
            partitions : List[SortPartitionSignature] = enumerate_sort_partitions(sort, part_sig.class_signatures)
            self.sort2partitions[sort] = partitions
        vprint_title(self.options, 'ConstraintMerger: _set_sort_to_partitions', 5)
        vprint(self.options, f'sort2partitions: {self.sort2partitions}', 5)

    def _set_partitions(self) -> None:
        self.partitions = get_partitions_from_sort_partititions(self.sort2partitions)
        vprint_title(self.options, f'ConstraintMerger: _set_partitions', 5)
        vprint(self.options, f'partitions: {self.partitions}', 5)
        vprint(self.options, f'number of partitions: {len(self.partitions)}', 5)

    def _set_func_permutations(self) -> None:
        all_func_permutations = []
        fname_id = 0
        self.sign_func_name2id : Dict[str, int]= {}
        for sfname, count in self.pap.sig_gen.sign_func_name2count.items():
            self.sign_func_name2id[sfname] = fname_id
            fname_id += 1
            func_ids  = list(range(count))
            func_permutations = permutations(func_ids)
            all_func_permutations.append(func_permutations)
        # cartesian product
        self.func_permutations = list(product(*all_func_permutations))
        vprint(self.options, f'sign_func_name2id: {self.sign_func_name2id}', 5)
        vprint(self.options, f'func permutations: {self.func_permutations}', 5)

    def _set_absent_partitions(self) -> None:
        for sig in self.partitions:
            self.absent_signatures[str(sig)] = sig
        for arg_partition in self.ap_list: 
            part_sig = arg_partition.part_sig
            for func_perm in self.func_permutations:
                permuted_sig = get_permuted_signature(part_sig, self.sign_func_name2id, func_perm)
                if str(permuted_sig) in self.absent_signatures:
                    del self.absent_signatures[str(permuted_sig)]
        
        vprint_title(self.options, 'QInference: _set_absent_partitions', 5)
        vprint(self.options, 'absent partitions:', 5)
        for sig in self.absent_signatures:
            vprint(self.options, f'{sig}', 5)

    #------------------------------------------------
    # public methods
    #------------------------------------------------
    def get_absent_partition_signatures(self) -> List[PartitionSignature]:
        # func_permutations 
        self.sign_func_name2id : Dict[str, int]= {}
        self.func_permutations = None
        self._set_func_permutations()

        # absent_signatures
        self.absent_signatures : Dict[str, PartitionSignature] = {}
        self._set_absent_partitions()
        return list(self.absent_signatures.values())

class QInference():
    # static members
    atoms = []
    tran_sys : TransitionSystem

    def __init__(self, qprimes: List[QPrime], instantiator : FiniteIvyInstantiator, options : QrmOptions):
        self.options = options
        self.instantiator = instantiator
        self.qprimes = qprimes
        self.terms   = get_terms(QInference.tran_sys, QInference.atoms, self.qprimes[0].prime)

        self.sig_gen = SigGenerator(self.terms, self.options)
        self.bindings       : List[ConstArgBinding]  = [qprime.binding for qprime in self.qprimes] 
        self.arg_partitions : List[ArgPartition]     = [qprime.arg_partition for qprime in self.qprimes]
        self.prod_arg_partition  = ProductArgPartition(self.sig_gen, self.bindings, self.options)

        # sort2infer_mode
        self.sort2qmode : Dict[il.EnumeratedSort, QuantifierMode] = {}
        self._set_sort_to_quantifier_mode()
        self.cmode : ConstraintMode 
        self._set_constraint_mode()

        # qformula
        self.qformula = QFormula(self.prod_arg_partition, self.sort2qmode, self.options)

        # quantifier inference
        self.qclause = None
        self._set_qclause()

    def _map_argument_to_exists_var_id(self, arg_signatures: List[ArgumentSignature]):
        sfname2arg_ids      = {}
        red_arg_sig2var_id  = {}
        for arg_sig in arg_signatures:
            if arg_sig.get_reduced_signature() in red_arg_sig2var_id:
                continue
            sfname  = arg_sig.signed_fname
            if not sfname in sfname2arg_ids:
                sfname2arg_ids[sfname] = set() 
            arg_ids = sfname2arg_ids[sfname]
            red_arg_sig2var_id[arg_sig.get_reduced_signature()] = len(arg_ids)
            arg_ids.add(arg_sig.arg_id)
        return red_arg_sig2var_id

    def _map_var_id_to_argument_signature(self, arg_signatures, red_arg_sig2var_id, max_var_id):
        var_id2arg_sigs = {var_id : [] for var_id in range(max_var_id+1)}
        for arg_sig in arg_signatures:
            var_id = red_arg_sig2var_id[arg_sig.get_reduced_signature()]
            var_id2arg_sigs[var_id].append(arg_sig)
        return var_id2arg_sigs

    def _get_substituted_terms(self, sign_func_name2args):
        qterms = set() 
        for sfname, args_lists in sign_func_name2args.items():
            (sign, fname) = split_signed_func_name(sfname)
            fsymbol = self.sig_gen.func_name2symbol[fname]
            for args in args_lists:
                if args == None:
                    continue
                qterm = None
                if fname.endswith('='):
                    lhs = None
                    if len(args) > 1:
                        lhs = il.App(fsymbol, *args[:-1])
                    else: 
                        lhs = fsymbol
                    rhs = args[-1]
                    qterm = il.Equals(lhs,rhs)
                elif len(args) >= 1:
                    qterm = il.App(fsymbol, *args)
                else:
                    qterm = fsymbol
                if sign == '1':
                    qterm = il.Not(qterm)
                qterms.add(qterm)
        qterms = list(qterms)
        return qterms

    def _substituted_terms_arguments_with_exists_vars(self, arg_signatures : List[ArgumentSignature], red_arg_sig2var_id, exist_vars):
        sign_func_name2args  = {}
        sign_func_name2count = {}
        arg_signatures = set([str(arg_sig) for arg_sig in arg_signatures])
        for term  in self.terms:
            (sign,atom) = split_term(term)
            func_symbol = get_func_symbol(atom)
            sfname      = get_signed_func_name(sign, atom, func_symbol) 
            if not sfname in sign_func_name2count:
                sign_func_name2count[sfname] = 0
                sign_func_name2args[sfname]  = []
            else:
                sign_func_name2count[sfname] += 1
            func_id  = sign_func_name2count[sfname]
            args     = get_func_args(atom) 
            new_args = []
            for arg_id, arg in enumerate(args):
                arg_sig = ArgumentSignature(arg.sort, sfname, func_id, arg_id)
                if str(arg_sig) in arg_signatures:
                    var_id = red_arg_sig2var_id[arg_sig.get_reduced_signature()]
                    new_args.append(exist_vars[var_id])
                else:
                    new_args.append(arg)
            sign_func_name2args[sfname].append(new_args)
        return self._get_substituted_terms(sign_func_name2args) 

    def _get_equality_constraint(self, qterms, exists_vars):
        used_constants = set()
        for qterm in qterms:
            used_constants.update(ilu.used_constants_ast(qterm))
        eqs = []
        for const in used_constants:
            for var in exists_vars:
                eq = il.Equals(const, var)
                eqs.append(eq)
        return il.Or(*eqs)

    def _try_infer_exists(self, sort, part_sig : SortPartitionSignature_) -> bool:
        assert(len(part_sig.identical_multi_classes) == 1)
        arg_signatures = list(part_sig.identical_multi_classes.values())[0]

        red_arg_sig2var_id = self._map_argument_to_exists_var_id(arg_signatures)
        max_var_id = max([var_id for var_id in red_arg_sig2var_id.values()])
        exist_vars = [il.Variable(f'{sort.name.upper()}{i}', sort) for i in range(max_var_id+1)]
        var_id2arg_sigs = self._map_var_id_to_argument_signature(arg_signatures, red_arg_sig2var_id, max_var_id)
        qterms = self._substituted_terms_arguments_with_exists_vars(arg_signatures, red_arg_sig2var_id, exist_vars)
        eq_constraint = self._get_equality_constraint(qterms, exist_vars)

        instantiated_qterms = []
        for qterm in qterms:
            qformula = il.ForAll(exist_vars, il.Or(*[qterm, eq_constraint])) # only compare the set of literals, so either forall/exists is fine
            qformula =  self.instantiator.instantiate_quantifier(qformula)
            instantiated_qterms += futil.flatten_cube(qformula)
        original_terms = ' '.join(sorted([str(t) for t in self.terms]))
        substituted_terms = ' '.join(sorted([str(t) for t in instantiated_qterms]))
        if original_terms != substituted_terms:
            return False
        part_sig.exists_class_sigs = [ClassSignature(arg_sigs) for arg_sigs in var_id2arg_sigs.values()] 
        part_sig.forall_class_sigs = [class_sig for class_sig in part_sig.identical_single_classes.values()]
        return True

    def _can_infer_exists(self, sort, part_sig : SortPartitionSignature_) -> bool:
        num_class = len(part_sig.identical_classes)
        if num_class == 1: # all variables of this sort appear in exactly same positions:
            return self._try_infer_exists(sort, part_sig)
        return False

    def _can_infer_forall_exists(self, sort, part_sig : SortPartitionSignature_) -> bool:
        num_single_class  = len(part_sig.identical_single_classes)
        num_multi_class   = len(part_sig.identical_multi_classes)
        num_class         = len(part_sig.identical_classes)
        if num_multi_class == 1 and (num_class == num_multi_class + num_single_class) and num_class > 1:
            return self._try_infer_exists(sort, part_sig)
        return False

    def _get_sort_quantifier_mode(self, sort, part_sig : SortPartitionSignature_) -> QuantifierMode:
        # currently merging qprime only considers forall
        if len(self.qprimes) > 1:
            return QuantifierMode.forall
        if len(part_sig.class_signatures) < sort.card or sort.card == 1:
            return QuantifierMode.forall
        assert(len(part_sig.class_signatures) == sort.card)
        if self._can_infer_exists(sort, part_sig):
            return QuantifierMode.exists
        elif self._can_infer_forall_exists(sort, part_sig):
            return QuantifierMode.forall_exists
        return QuantifierMode.forall

    def _set_sort_to_quantifier_mode(self) -> None:
        vprint_title(self.options, 'QInference: _set_sort_to_quantifier_mode', 5)
        for sort, part_sig in self.prod_arg_partition.sort2part_sig.items():
            qmode : QuantifierMode = self._get_sort_quantifier_mode(sort, part_sig)
            vprint(self.options, f'quantifier mode: {sort.name}: {qmode}', 5)
            self.sort2qmode[sort] = qmode

    def _has_sort_with_too_many_classes(self) -> bool:
        for sort, part_sig in self.prod_arg_partition.sort2part_sig.items():
            if len(part_sig.class_signatures) >= 6:
                return True 
        return False

    def _has_qprime_with_many_classes(self) -> bool:
        for sort, part_sig in self.prod_arg_partition.sort2part_sig.items():
            for arg_partition in self.arg_partitions: 
                class_sigs = arg_partition.sort2class_sigs[sort]
                if len(class_sigs) == min(sort.card, len(part_sig.class_signatures)):
                    return True         
        return False

    def _set_constraint_mode(self) -> None:
        if len(self.qprimes) == 1:
            self.cmode = ConstraintMode.no_merge
        elif self._has_sort_with_too_many_classes(): # enumerate all partitions for class signatures will be infeasible
            self.cmode = ConstraintMode.merge_present
        elif self._has_qprime_with_many_classes(): # use absent constraint result in more succint representation
            self.cmode = ConstraintMode.merge_absent
        else: # all qprimes have small number of classes, use present constraint result in more succinct representation
            self.cmode = ConstraintMode.merge_present
        vprint_title(self.options, 'QInference: _set_constraint_mode', 5)
        vprint(self.options, f'constraint mode: {self.cmode}', 5)

    def _need_eq_constraints(self) -> None:
        if len(self.constraint.partitions) == len(self.qprimes) and len(self.qprimes) > 1:              
            vprint_title(self.options, 'QInference: _need_eq_constraints: ', 5)
            vprint(self.options, f'{False}', 5)
            return False
        return True

    def _set_qclause(self):
        if self.cmode == ConstraintMode.merge_absent:
            self.constraint = AbsentConstraint(self.prod_arg_partition, self.arg_partitions, self.options)
            if self._need_eq_constraints():
                part_sigs : List[PartitionSignature] = self.constraint.get_absent_partition_signatures()
                self.qformula.set_merge_constraints(part_sigs, self.cmode)

        elif self.cmode == ConstraintMode.merge_present:
            part_sigs : List[PartitionSignature] = [arg_part.part_sig for arg_part in self.arg_partitions]
            self.qformula.set_merge_constraints(part_sigs, self.cmode)

        elif self.cmode == ConstraintMode.no_merge:
            self.qformula.set_no_merge_constraints()

        self.qclause = self.qformula.get_qclause()

    #------------------------------------------------   
    # public methods
    #------------------------------------------------
    def get_qclause(self):
        return self.qclause

    @staticmethod
    def setup(atoms, tran_sys) -> None:
        QInference.atoms    = atoms
        QInference.tran_sys = tran_sys
        QPrime.setup(atoms, tran_sys)
