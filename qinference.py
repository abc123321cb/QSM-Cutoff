from ivy import ivy_logic as il
from ivy import ivy_logic_utils as ilu
from transition_system import TransitionSystem
from prime import Prime, PrimeOrbit
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

    def __init__(self, prime : Prime, options : QrmOptions, add_member_terms=True):
        self.options        = options
        self.prime          = prime
        self.terms          = get_terms(QPrime.tran_sys, QPrime.atoms, self.prime)
        if add_member_terms:
            self.terms += add_member_terms_for_dependent_sorts(self.terms, QPrime.tran_sys)
        vprint_title(self.options, 'QPrime', 5)
        self.binding        = ConstArgBinding(self.terms, self.options)
        self.arg_partition  = ArgPartition(self.binding, self.options)

    @staticmethod
    def setup(atoms, tran_sys) -> None:
        QPrime.atoms    = atoms
        QPrime.tran_sys = tran_sys

class QInference():
    # static members
    atoms = []
    tran_sys : TransitionSystem
    instantiator : FiniteIvyInstantiator

    def __init__(self, orbit : PrimeOrbit, options : QrmOptions):
        self.options = options
        # terms
        add_member_terms = (len(orbit.suborbit_repr_primes) == 1)
        self.qprimes = [QPrime(prime, self.options, add_member_terms) for prime in orbit.suborbit_repr_primes]
        self.terms   = get_terms(QInference.tran_sys, QInference.atoms, self.qprimes[0].prime)
        if add_member_terms:
            self.terms  += add_member_terms_for_dependent_sorts(self.terms, QInference.tran_sys)
        # signatures
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
        self.qformula = QFormula(orbit.id, self.prod_arg_partition, self.sort2qmode, self.options)

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

    def _get_equality_constraint(self, sort, qterms, exists_vars):
        used_constants = set()
        for qterm in qterms:
            used_constants.update(ilu.used_constants_ast(qterm))
        used_sort_constants = []
        domain_constants = set(sort.constructors)
        for const in used_constants:
            if const.sort == sort and const in domain_constants:
                used_sort_constants.append(const)
        eqs = []
        for const in used_sort_constants:
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
        eq_constraint = self._get_equality_constraint(sort, qterms, exist_vars)

        instantiated_qterms = []
        for qterm in qterms:
            qformula = il.ForAll(exist_vars, il.Or(*[qterm, eq_constraint])) # only compare the set of literals, so either forall/exists is fine
            qformula =  QInference.instantiator.instantiate_quantifier(qformula)
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

    def _set_constraint_mode(self) -> None:
        if len(self.qprimes) == 1:
            self.cmode = ConstraintMode.no_merge
        else: 
            self.cmode = ConstraintMode.merge
        vprint_title(self.options, 'QInference: _set_constraint_mode', 5)
        vprint(self.options, f'constraint mode: {self.cmode}', 5)

    def _set_qclause(self):
        if self.cmode == ConstraintMode.merge:
            self.qformula.set_merge_constraints(self.sig_gen, self.arg_partitions, QInference.instantiator, QInference.tran_sys)
        elif self.cmode == ConstraintMode.no_merge:
            self.qformula.set_no_merge_constraints()

        self.qclause = self.qformula.get_qclause()

    #------------------------------------------------   
    # public methods
    #------------------------------------------------
    def get_qclause(self):
        return self.qclause

    @staticmethod
    def setup(atoms, tran_sys : TransitionSystem, instantiator : FiniteIvyInstantiator) -> None:
        QInference.atoms    = atoms
        QInference.tran_sys = tran_sys
        QInference.instantiator = instantiator
        QPrime.setup(atoms, tran_sys)
        ConstraintPartitionSignature.setup(tran_sys)
