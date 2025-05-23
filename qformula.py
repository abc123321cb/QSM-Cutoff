from ivy import ivy_logic as il
from ivy import ivy_logic_utils as ilu
from ivy import ivy_solver as slv
from util import QrmOptions
from verbose import *
from qutil import *
from util import FormulaUtility as futil 
from signature import *
from finite_ivy_instantiate import FiniteIvyInstantiator
from constraint_merge import ConstraintMerger

from enum import Enum
QuantifierMode  = Enum('QuantifierMode', ['forall', 'exists', 'forall_exists'])
ConstraintMode  = Enum('ConstraintMode', ['merge', 'no_merge'])

class QFormula():
    def __init__(self,orbit_id, pap : ProductArgPartition, sort2qmode : Dict[il.EnumeratedSort, QuantifierMode], options : QrmOptions):
        self.orbit_id = orbit_id
        self.options  = options
        self.sort2qmode       : Dict[il.EnumeratedSort, QuantifierMode] = sort2qmode
        self.pap              : ProductArgPartition = pap
        # sort2class_sigs: each class_sig in will be represented by a distinct qvar
        self.sort2class_sigs  : Dict[il.EnumeratedSort, List[ClassSignature]] = {}
        self._set_sort_to_class_signatures()
        # exists_arg_sigs
        self.exists_arg_sigs  : Set[str] = set()
        self._set_existential_argument_sigs()
        # sort2count
        self.sort2count       : Dict[il.EnumeratedSort, int] = {}
        self._set_sort_to_count()
        # sort2qvars
        self.sort2qvars       : Dict[il.EnumeratedSort, List[il.Variable]]    = {}
        self._set_sort_to_qvars()
        # arg_sig2qvar, qvar2arg_sigs
        self.arg_sig2qvar   : Dict[str, il.Variable] = {}
        self.qvar2arg_sigs  : Dict[il.Variable, List[ArgumentSignature]] = {}
        self._set_signature_to_qvar()
        # qvars
        self.forall_qvars : Set[il.Variable] = set()
        self.exists_qvars : Set[il.Variable] = set()
        self._set_qvars()
        # sign_func_name2args
        self.sign_func_name2args : Dict[str, List[il.Variable]] = {}  # signed function name -> [arg_list1, arg_list2]
        self._set_signed_func_name_to_args()
        # qterms
        self.qterms = []
        self._set_qterms()

        # constraint
        self.forall_constraint = None
        self.forall_exists_constraint = None
        self.sub_exists_vars : Set[il.Variable] = set()

    def _set_sort_to_class_signatures(self) -> None:
        for sort, part_sig in self.pap.sort2part_sig.items():
            qmode = self.sort2qmode[sort]
            if qmode == QuantifierMode.forall:
                self.sort2class_sigs[sort] = part_sig.class_signatures
            else:
                self.sort2class_sigs[sort] = part_sig.exists_class_sigs + part_sig.forall_class_sigs

    def _set_existential_argument_sigs(self) -> None:
        for sort, part_sig in self.pap.sort2part_sig.items():
            qmode = self.sort2qmode[sort]
            if qmode != QuantifierMode.forall:
                for class_sig in part_sig.exists_class_sigs:
                    for arg_sig in class_sig.arg_signatures:
                        self.exists_arg_sigs.add(str(arg_sig))

    def _set_sort_to_count(self) -> None:
        for sort, class_sigs in self.sort2class_sigs.items():
            self.sort2count[sort] = len(class_sigs) 

    def _set_sort_to_qvars(self) -> None:
        for sort, count in self.sort2count.items():
            qvars = []
            for qvar_id in range(count):
                qvar_name = sort.name.upper() + str(qvar_id)
                qvars.append(il.Variable(qvar_name, sort))
            self.sort2qvars[sort] = qvars

    def _reset_sort_to_count(self) -> None:
        for sort in self.sort2count.keys():
            self.sort2count[sort] = 0
                
    def _get_next_unused_qvar(self, sort) -> None:
        count = self.sort2count[sort]
        qvar = self.sort2qvars[sort][count]
        self.sort2count[sort] += 1
        return qvar

    def _set_signature_to_qvar(self) -> None:
        self._reset_sort_to_count()
        class_sigs = []
        for sort, class_sigs in self.sort2class_sigs.items():
            for class_sig in class_sigs:
                qvar = self._get_next_unused_qvar(sort)
                for arg_sig in class_sig.arg_signatures:
                    self.arg_sig2qvar[str(arg_sig)] = qvar
                self.qvar2arg_sigs[qvar] = class_sig.arg_signatures
                
    def _set_qvars(self) -> None:
        for arg_sig, qvar in self.arg_sig2qvar.items():
            if arg_sig in self.exists_arg_sigs:
                self.exists_qvars.add(qvar)
            else:
                self.forall_qvars.add(qvar)
        vprint_title(self.options, 'QFormula: _set_qvars', 5)
        vprint(self.options, f'forall_qvars: {self.forall_qvars}', 5)
        vprint(self.options, f'exists_qvars: {self.exists_qvars}', 5)

    def _reset_signed_func_name_to_args(self) -> None:
        sig_gen : SigGenerator = self.pap.sig_gen
        for sfname, func_count in sig_gen.sign_func_name2count.items():
            args_sort = sig_gen._get_args_sort_from_signed_func_name(sfname)
            args_lists = []
            for i in range(func_count):
                args_lists.append([None]*len(args_sort))
            self.sign_func_name2args[sfname] = args_lists

    def _init_signed_func_name_to_args(self) -> None:
        sig_gen : SigGenerator = self.pap.sig_gen
        for sig in sig_gen.generate_argument_signature():
            if str(sig) in self.arg_sig2qvar:
                qvar = self.arg_sig2qvar[str(sig)]
                self.sign_func_name2args[sig.signed_fname][sig.func_id][sig.arg_id] = qvar

    def _remove_uninitialized_args(self) -> None:
        for sfname, args_lists in self.sign_func_name2args.items():
            init_args = []
            for args in args_lists:
                is_init = True
                for arg in args:
                    if arg == None:
                        is_init = False
                        break
                if is_init:
                    init_args.append(args)
            self.sign_func_name2args[sfname] = init_args 

    def _set_signed_func_name_to_args(self) -> None:
        self._reset_signed_func_name_to_args()
        self._init_signed_func_name_to_args()
        self._remove_uninitialized_args()
        vprint_title(self.options, 'QFormula: _set_signed_func_name_to_args', 5)
        vprint(self.options, f'signed_func_name2args: {self.sign_func_name2args}', 5)

    def _set_qterms(self) -> None:
        sig_gen : SigGenerator = self.pap.sig_gen
        qterms = set()
        for sfname, args_lists in self.sign_func_name2args.items():
            (sign, fname) = split_signed_func_name(sfname)
            fsymbol = sig_gen.func_name2symbol[fname]
            for args in args_lists:
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
        self.qterms = list(qterms)
        vprint_title(self.options, 'QFormula: _set_qterms', 5)
        vprint(self.options, f'qterms: {[str(term) for term in self.qterms]}', 5)

    #------------------------------------------------
    # public methods
    #------------------------------------------------
    def set_merge_constraints(self, sig_gen : SigGenerator, arg_partitions : List[ArgPartition], instantiator : FiniteIvyInstantiator, tran_sys : TransitionSystem) -> None:
        # constraints
        constraint_sigs   = ConstraintSignatures(sig_gen, arg_partitions)
        constraint_merger = ConstraintMerger(self.orbit_id, self.arg_sig2qvar, self.qvar2arg_sigs, self.forall_qvars, self.options)
        constraint_merger.set_constraint_to_minimize(constraint_sigs, instantiator.dep_axioms_fmla)
        if constraint_merger.no_need_constraint():
            return
        if self.options.minimize_equality:
            constraint_merger.set_variables_for_minimization(self.sort2qvars)
            constraint_merger.write_smt2_for_minimization(tran_sys)
            constraint_merger.extract_prime_implicants()
            minimized_constraint = constraint_merger.minimize_prime_implicants(instantiator.dep_axioms_fmla)
            self.qterms.append(minimized_constraint)
        else:
            reduced_present_constraints = constraint_merger.get_constraint_list(constraint_sigs.get_reduced_constraint_signatures()) 
            reduced_present_cost        = sum([len(c) for c in reduced_present_constraints])
            reduced_absent_cost         = 0
            res = slv.z3.sat
            while(res == slv.z3.sat):
                absent_part_sig      = constraint_merger.convert_sat_model_to_absent_partition_signature() 
                absent_part_sigs     = constraint_sigs.add_absent_signatures(absent_part_sig)
                reduced_absent_cost += sum([len(c) for c in constraint_merger.get_constraint_list([absent_part_sig]) ])
                if reduced_present_cost <= reduced_absent_cost:
                    break
                constraint_merger.block_constraint(absent_part_sigs)
                res = constraint_merger.solver.check() 
            if reduced_present_cost <= reduced_absent_cost:
                cterm = constraint_merger.disjunct_constraint_list(reduced_present_constraints)
                self.qterms.append(cterm)
                vprint(self.options, 'use present constraint', 5)
            else:
                cterm = il.Not(constraint_merger.get_disjunctive_constraint_term(constraint_sigs.get_reduced_absent_signatures()))
                self.qterms.append(cterm)
                vprint(self.options, 'use absent constraint', 5)

    def _set_forall_constraint(self):
        neq_terms = set()
        for sort, qvars in self.sort2qvars.items():
            qvars = set(qvars)
            forall_qvars = list(qvars.intersection(self.forall_qvars))
            for i in range(len(forall_qvars)-1):
                for j in range(i+1, len(forall_qvars)):
                    assert(str(forall_qvars[i]) != str(forall_qvars[j]))
                    neq_qvars = [forall_qvars[i], forall_qvars[j]]
                    neq_qvars.sort(key=lambda x: str(x))
                    neq = il.Not(il.Equals(neq_qvars[0], neq_qvars[1]))
                    neq_terms.add(neq)
        neq_terms = list(neq_terms)
        if len(neq_terms):
            self.forall_constraint = il.And(*neq_terms) # neq1 & neq2 & neq3

    def _set_forall_exists_constraint(self):
        eq_terms = set()
        for sort, qvars in self.sort2qvars.items():
            qvars = set(qvars)
            forall_qvars = list(qvars.intersection(self.forall_qvars))
            exists_qvars = list(qvars.intersection(self.exists_qvars))
            for fvar in forall_qvars:
                for evar in exists_qvars:
                    assert(str(fvar) != str(evar))
                    eq_qvars = [fvar, evar]
                    eq_qvars.sort(key=lambda x: str(x))
                    eq = il.Equals(eq_qvars[0], eq_qvars[1])
                    eq_terms.add(eq)
                    self.sub_exists_vars.add(evar)
        eq_terms = list(eq_terms)
        if len(eq_terms):
            self.forall_exists_constraint = il.Or(*eq_terms) 

    def _set_exists_sub_term(self):
        qterms     = []
        sub_qterms = []
        for term in self.qterms:
            (_, atom) = split_term(term)
            args = get_func_args(atom)
            is_sub_qterm = False
            for arg in args:
                if arg in self.sub_exists_vars:
                    is_sub_qterm = True
            if is_sub_qterm:
                sub_qterms.append(term)
            else:
                qterms.append(term)
        sub_qterms = [il.And(*sub_qterms), self.forall_exists_constraint]
        qterms.append(il.ForAll(self.sub_exists_vars, il.Or(*sub_qterms)))
        for evar in self.sub_exists_vars:
            self.exists_qvars.remove(evar)
        self.qterms = qterms

    def set_no_merge_constraints(self) -> None:
        self._set_forall_exists_constraint()
        if self.forall_exists_constraint != None:
            self._set_exists_sub_term()
        self._set_forall_constraint()
        if self.forall_constraint != None:
            self.qterms.append(self.forall_constraint)

    def get_qclause(self): 
        qstate = il.And(*self.qterms)
        if len(self.exists_qvars) > 0:
            qstate = il.ForAll(self.exists_qvars, qstate)
        if len(self.forall_qvars) > 0: 
            qstate = il.Exists(self.forall_qvars, qstate)
        qclause = il.Not(qstate)
        qclause = futil.de_morgan(qclause)
        vprint_title(self.options, 'QFormula: get_qclause', 5)
        vprint(self.options, f'qclause: {str(qclause)}', 5)
        return qclause 