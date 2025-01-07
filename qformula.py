from ivy import ivy_logic as il
from ivy import ivy_logic_utils as ilu
from ivy import ivy_solver as slv
from util import QrmOptions
from verbose import *
from qutil import *
from util import FormulaUtility as futil 
from signature import *
from finite_ivy_instantiate import FiniteIvyInstantiator

from enum import Enum
QuantifierMode  = Enum('QuantifierMode', ['forall', 'exists', 'forall_exists'])
ConstraintMode  = Enum('ConstraintMode', ['merge', 'no_merge'])

class QFormula():
    def __init__(self, pap : ProductArgPartition, sort2qmode : Dict[il.EnumeratedSort, QuantifierMode], options : QrmOptions):
        self.options = options
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

        # merge constraints
        self.constraint_sigs : ConstraintSignatures

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
    # QFormula: merging constraints
    #------------------------------------------------
    def _get_class_constraint(self, class_sig : ClassSignature):
        qvars = set() 
        for arg_sig in class_sig.arg_signatures: 
            qvar = self.arg_sig2qvar[str(arg_sig)]
            qvars.add(qvar)
        qvars = sorted(list(qvars))

        eq_terms = set()
        qvar = qvars[0] 
        for j in range(1, len(qvars)):
            assert(str(qvar) != str(qvars[j]))
            eq = il.Equals(qvar, qvars[j])
            eq_terms.add(eq)
        vprint_title(self.options, 'QFormula: _get_class_constraint', 5)
        vprint(self.options, f'qvars: {[str(q) for q in qvars]}', 5)
        vprint(self.options, f'eq_terms: {[str(t) for t in eq_terms]}')
        return list(eq_terms)

    def _get_diff_class_constraint(self, class_sigs : List[ClassSignature]):
        qvars = set()
        for class_sig in class_sigs:
            qvar = self.arg_sig2qvar[str(class_sig.arg_signatures[0])]
            qvars.add(qvar)
        qvars = list(qvars)
        neq_terms = set()
        for i in range(len(qvars)-1):
            for j in range(i+1, len(qvars)):
                assert(str(qvars[i]) != str(qvars[j]))
                neq_qvars = [qvars[i], qvars[j]]
                neq_qvars.sort(key=lambda x: str(x))
                neq = il.Not(il.Equals(neq_qvars[0], neq_qvars[1]))
                neq_terms.add(neq)
        vprint_title(self.options, 'QFormula: _get_diff_class_constraint', 5)
        vprint(self.options, f'qvars: {[str(q) for q in qvars]}', 5)
        vprint(self.options, f'eq_terms: {[str(t) for t in neq_terms]}')
        return list(neq_terms)

    def _get_member_constraints(self, mem_sigs : List[MemberRelationSignature]):
        terms = []
        for mem_sig in mem_sigs:
            for (elem_class_sig, set_class_sig) in mem_sig.member_relations:
                elem_qvar = self.arg_sig2qvar[str(elem_class_sig.arg_signatures[0])] 
                set_qvar  = self.arg_sig2qvar[str(set_class_sig.arg_signatures[0])] 
                terms.append(il.App(mem_sig.member_symbol, *[elem_qvar, set_qvar]))
            for (elem_class_sig, set_class_sig) in mem_sig.non_member_relations:
                elem_qvar = self.arg_sig2qvar[str(elem_class_sig.arg_signatures[0])] 
                set_qvar  = self.arg_sig2qvar[str(set_class_sig.arg_signatures[0])] 
                terms.append(il.Not(il.App(mem_sig.member_symbol, *[elem_qvar, set_qvar])))
        return terms

    def _get_partition_constraint(self, partition : ConstraintPartitionSignature): 
        vprint_title(self.options, 'QFormula: _get_partition_constraint', 5)
        vprint(self.options, f'partition: {partition}', 5)
        constraint   = []
        for sort, sort_sig in partition.sort2signature.items():
            vprint(self.options, f'sort partition signature: {sort_sig}', 5)
            for class_sig in sort_sig.class_signatures:
                vprint(self.options, f'class signature: {class_sig}', 5)
                constraint  += self._get_class_constraint(class_sig)
            constraint += self._get_diff_class_constraint(sort_sig.class_signatures)
        constraint += self._get_member_constraints(partition.member_sigs)
        vprint(self.options, f'constraint: {[str(c) for c in constraint]}', 5)
        return constraint

    def _convert_sat_model_to_absent_partition_signature(self, model) -> PartitionSignature:
        qvar2value  : Dict[str, str] = {}
        for decl in model.decls():
            qvar_name = str(decl.name()).split('!')[0]
            value = str(model.get_interp(decl))
            qvar2value[qvar_name] = value
        const2qvars : Dict[str, List[il.Variable]] = {}
        for qvar in self.forall_qvars:
            if str(qvar) in qvar2value:
                const = qvar2value[str(qvar)] 
                if not const in const2qvars:
                    const2qvars[const] = []
                const2qvars[const].append(qvar)

        # sort2part_sig
        sort2class_sigs : Dict[il.EnumeratedSort, List[ClassSignature]] = {}
        for qvars in const2qvars.values():
            sort = qvars[0].sort
            arg_sigs = []
            for qvar in qvars:
                arg_sigs += self.qvar2arg_sigs[qvar]
            if not sort in sort2class_sigs:
                sort2class_sigs[sort] = []
            sort2class_sigs[sort].append(ClassSignature(arg_sigs))
        sort2part_sig : Dict[il.EnumeratedSort, List[SortPartitionSignature]] = {}
        for sort, class_sigs in sort2class_sigs.items():
            sort2part_sig[sort] = SortPartitionSignature(class_sigs)
        part_sig = ConstraintPartitionSignature(sort2part_sig) 
        # sig2const_str
        class_sig2const : Dict[str,str] = {}
        for class_sigs in sort2class_sigs.values():
            for class_sig in class_sigs:
                arg_sig = class_sig.arg_signatures[0]
                qvar  = self.arg_sig2qvar[str(arg_sig)]
                assert(str(qvar) in qvar2value)
                const = qvar2value[str(qvar)]
                class_sig2const[str(class_sig)] = const
        part_sig.init_member_relations_from_model(class_sig2const)
        return part_sig

    def _get_constraints(self, part_sigs : List[ConstraintPartitionSignature]):
        constraints = [] 
        for part_sig in part_sigs: 
            constraint = self._get_partition_constraint(part_sig)
            constraints.append(constraint)
        constraints.sort(key=lambda constraint: len(constraint))
        return constraints

    def _get_constraint_term(self, constraints):
        terms = []
        for constraint in constraints:
            if len(constraint):
                term = il.And(*constraint)
                terms.append(term)
        if len(terms):
            return il.Or(*terms)    
        return None

    #------------------------------------------------
    # public methods
    #------------------------------------------------
    def set_merge_constraints(self, sig_gen : SigGenerator, arg_partitions : List[ArgPartition], instantiator : FiniteIvyInstantiator) -> None:
        self.constraint_sigs = ConstraintSignatures(sig_gen)
        self.constraint_sigs.add_present_signatures(arg_partitions) 
        present_constraints = self._get_constraints(self.constraint_sigs.get_present_signatures())
        present_cterm = self._get_constraint_term(present_constraints)  
        assert(present_cterm != None)
        present_constraints = self._get_constraints(self.constraint_sigs.get_reduced_present_signatures()) 
        present_cost = sum([len(c) for c in present_constraints])
        # present_cterm is a disjuction of eq constraints for each sub-orbit 
        fmlas  = instantiator.dep_axioms_fmla + [il.Not(present_cterm)]
        absent_fmla  = il.Exists(self.forall_qvars, il.And(*fmlas)) 
        solver = slv.z3.Solver()
        solver.add(slv.formula_to_z3(absent_fmla))
        res = solver.check() 
        if res == slv.z3.unsat: # no constraints needed if unsat
            return
        absent_cost = 0
        while(res == slv.z3.sat):
            model = slv.get_model(solver)
            absent_part_sig   = self._convert_sat_model_to_absent_partition_signature(model)
            absent_part_sigs  = self.constraint_sigs.add_absent_signatures(absent_part_sig)
            absent_cost += sum([len(c) for c in self._get_constraints([absent_part_sig]) ])
            if present_cost <= absent_cost:
                break
            block_constraints = self._get_constraints(absent_part_sigs)
            block_cterm       = self._get_constraint_term(block_constraints)
            fmla_body         = il.And(*[absent_fmla.body, il.Not(block_cterm)])
            absent_fmla = il.Exists(self.forall_qvars, fmla_body)
            solver = slv.z3.Solver()
            solver.add(slv.formula_to_z3(absent_fmla))
            res = solver.check() 
        if present_cost <= absent_cost:
            cterm = self._get_constraint_term(present_constraints)
            self.qterms.append(cterm)
        else:
            absent_constraints  = self._get_constraints(self.constraint_sigs.get_reduced_absent_signatures()) 
            cterm = il.Not(self._get_constraint_term(absent_constraints))
            self.qterms.append(cterm)

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