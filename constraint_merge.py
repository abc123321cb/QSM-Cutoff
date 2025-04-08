import os
import subprocess
from ivy import ivy_logic as il
from ivy import ivy_logic_utils as ilu
from ivy import ivy_solver as slv
from util import QrmOptions
from verbose import *
from qutil import *
from util import FormulaUtility as futil 
from signature import *
from finite_ivy_instantiate import FiniteIvyInstantiator
from transition_system import TransitionSystem

from constraint_minimize import ConstraintMinimizer, ConstraintPrime


class ConstraintMerger():
    def __init__(self, orbit_id, arg_sig2qvar : Dict[str, il.Variable], qvar2arg_sigs : Dict[il.Variable, List[ArgumentSignature]], forall_qvars, options):
        self.options  = options
        self.arg_sig2qvar    = arg_sig2qvar
        self.qvar2arg_sigs   = qvar2arg_sigs
        self.minimize_fmla   = None
        self.qvars = list(forall_qvars)
        self.qvars.sort(key=lambda v: str(v))
        self.var2const    = {qvar : il.Symbol(str(qvar), qvar.sort) for qvar in self.qvars}
        self.const2var    = {const: qvar for qvar,const in self.var2const.items()}
        self.member_terms = set()
        # filenames
        self.smt_filename = self.options.instance_name + f'.merge{orbit_id}.smt2'
        self.mus_filename = self.options.instance_name + f'.merge{orbit_id}.mus'

        # for minimization
        self.eq_vars      = []
        self.member_vars  = [] 
        self.all_vars     = []
        self.primes : List[ConstraintPrime] = []
        slv.clear() 
        self.solver = slv.z3.Solver()

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
        return list(neq_terms)

    def _get_member_constraints(self, mem_sigs : List[MemberRelationSignature]):
        terms = []
        for mem_sig in mem_sigs:
            for (elem_class_sig, set_class_sig) in mem_sig.member_relations:
                elem_qvar = self.arg_sig2qvar[str(elem_class_sig.arg_signatures[0])] 
                set_qvar  = self.arg_sig2qvar[str(set_class_sig.arg_signatures[0])] 
                term      = il.App(mem_sig.member_symbol, *[elem_qvar, set_qvar])
                self.member_terms.add(term)
                terms.append(term)
            for (elem_class_sig, set_class_sig) in mem_sig.non_member_relations:
                elem_qvar = self.arg_sig2qvar[str(elem_class_sig.arg_signatures[0])] 
                set_qvar  = self.arg_sig2qvar[str(set_class_sig.arg_signatures[0])] 
                term      = il.App(mem_sig.member_symbol, *[elem_qvar, set_qvar])
                self.member_terms.add(term)
                terms.append(il.Not(term))
        return terms

    def _get_partition_constraint(self, partition : ConstraintPartitionSignature): 
        constraint   = []
        for sort, sort_sig in partition.sort2signature.items():
            for class_sig in sort_sig.class_signatures:
                constraint  += self._get_class_constraint(class_sig)
            constraint += self._get_diff_class_constraint(sort_sig.class_signatures)
        constraint += self._get_member_constraints(partition.member_sigs)
        return constraint

    def get_constraint_list(self, part_sigs : List[ConstraintPartitionSignature]):
        constraints = [] 
        for part_sig in part_sigs: 
            constraint = self._get_partition_constraint(part_sig)
            constraints.append(constraint)
        constraints.sort(key=lambda constraint: len(constraint))
        return constraints

    def disjunct_constraint_list(self, constraints):
        terms = []
        for constraint in constraints:
            if len(constraint):
                term = il.And(*constraint)
                terms.append(term)
        if len(terms):
            return il.Or(*terms)    
        return None

    def get_disjunctive_constraint_term(self, part_sigs : List[ConstraintPartitionSignature]):
        constraints = self.get_constraint_list(part_sigs)
        return self.disjunct_constraint_list(constraints)
    
    def convert_sat_model_to_absent_partition_signature(self) -> PartitionSignature:
        model = slv.get_model(self.solver)
        qvar2value  : Dict[str, str] = {}
        for decl in model.decls():
            qvar_name = str(decl.name()).split('!')[0]
            value = str(model.get_interp(decl))
            qvar2value[qvar_name] = value
        const2qvars : Dict[str, List[il.Variable]] = {}
        for qvar in self.qvars:
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

    def block_constraint(self, absent_part_sigs):
        block_cterm = self.get_disjunctive_constraint_term(absent_part_sigs)
        block_cterm = il.substitute(block_cterm, self.var2const)
        self.solver.add(slv.formula_to_z3(il.Not(block_cterm)))

    def set_constraint_to_minimize(self, constraint_sigs : ConstraintSignatures, dep_axioms_fmla):
        # set disjunctive constraint term
        constraint = constraint_sigs.get_constraint_signatures() #including symmetric constraints
        disjunctive_constraint_term = self.get_disjunctive_constraint_term(constraint)
        assert(disjunctive_constraint_term != None)
        self.minimize_fmla = il.And(*dep_axioms_fmla + [il.Not(disjunctive_constraint_term)]) 
        self.minimize_fmla = il.substitute(self.minimize_fmla, self.var2const)

    def no_need_constraint(self) -> bool:
        self.solver.add(slv.formula_to_z3(self.minimize_fmla))
        res = self.solver.check() 
        if res == slv.z3.unsat: # no constraints needed if unsat
            return True
        else:
            return False

    def set_variables_for_minimization(self, sort2qvars):
        for sort, qvars in sort2qvars.items():
            qvars.sort(key=lambda x: str(x))
            constants = [self.var2const[qvar] for qvar in qvars]
            for i in range(len(constants)-1):
                for j in range(i+1, len(constants)):
                    ni = constants[i]
                    nj = constants[j]
                    eq = il.Equals(ni,nj)
                    self.eq_vars.append(eq)
        for term in self.member_terms:
            self.member_vars.append(il.substitute(term, self.var2const))
        self.all_vars = [None] + self.eq_vars + self.member_vars

    def write_smt2_for_minimization(self, tran_sys : TransitionSystem):
        for var in self.eq_vars + self.member_vars:
                self.solver.add(slv.formula_to_z3(var))
                self.solver.add(slv.formula_to_z3(il.Not(var)))
        lines = self.solver.to_smt2().split('\n')
        # fix the buggy to_smt2()
        for i, line in enumerate(lines):
            if line.startswith('(declare-datatypes'):
                sort_name = line.split()[1][2:]
                sort = tran_sys.sorts[sort_name]
                constant_names = [f'({str(c)})' for c in sort.constructors]
                line = f'(declare-datatypes () (({sort_name} {' '.join(constant_names)})))'
                lines[i] = line

        smt_file = open(self.smt_filename, "w")
        smt_file.write('\n'.join(lines))
        smt_file.close()

    def _parse_prime_implicant(self, line):
        clause_ids = set([int(i) for i in line.strip().split()[1:]])
        if not 1 in clause_ids:  # mus that are not prime implicant: n & ~n, violating transitivity, or infeasible partition
            return
        clause_ids.remove(1)
        lits    = []
        lit_ids = []
        for i in clause_ids: 
            is_neg = i & 1
            var_id = (i>>1)
            if is_neg:
                lits.append(il.Not(self.all_vars[var_id]))
                lit_ids.append(-1*var_id)
            else: 
                lits.append(self.all_vars[var_id])
                lit_ids.append(var_id)
        prime = ConstraintPrime(prime_id=len(self.primes), lit_ids=lit_ids, fmla=il.And(*lits), cost=len(lits))
        self.primes.append(prime)

    def extract_prime_implicants(self):
        # MARCO
        mus_file = open(self.mus_filename, 'w')
        marco_args = ['./MARCO/marco.py', self.smt_filename, '-v', '-b', 'MUSes']
        try:
            subprocess.run(marco_args, text=True, check=True, stdout=mus_file, timeout=self.options.qrm_to) 
        except subprocess.CalledProcessError as error:
            sys.stdout.flush()
            if error.returncode == 1:
                vprint(self.options, f'[MARCO RESULT]: FAIL ... exit with return code {error.returncode}')
            else:
                vprint(self.options, f'[MARCO RESULT]: ABORT ... exit with return code {error.returncode}')
            return False
        except subprocess.TimeoutExpired:
            sys.stdout.flush()
            vprint(self.options, f'[MARCO TO]: Timeout after {self.options.qrm_to}')
            return False
        sys.stdout.flush()
        mus_file.close()
        # parse mus file
        with open(self.mus_filename, 'r') as mus_file: 
            for line in mus_file:
                if line.startswith('U'):
                    self._parse_prime_implicant(line) 


    def minimize_prime_implicants(self, dep_axioms_fmla):
        minimizer = ConstraintMinimizer(self.options, self.primes, self.minimize_fmla, self.all_vars, dep_axioms_fmla)
        minimizer.minimize()
        minimized_constraint = minimizer.get_minimized_constraints()
        return il.substitute(minimized_constraint, self.const2var)
