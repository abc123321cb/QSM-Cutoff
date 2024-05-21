from typing import List
from pysmt.shortcuts import Symbol, And, Or, EqualsOrIff, Not, ForAll, Exists, Function, TRUE
from frontend.utils import *
from frontend.vmt_parser import TransitionSystem
from prime import Prime 
from util import QrmOptions
from verbose import *
 

min_size = 2

class QInference():
    # static members
    atoms = []
    tran_sys : TransitionSystem

    def __init__(self, prime: Prime, options : QrmOptions, is_orbit_size_1 : bool) -> None:
        self.options = options
        # original
        self.prime      = prime
        self.is_orbit_size_1 = is_orbit_size_1
        self.repr_state = TRUE()
        self.relations  = []
        self.vars       = []
        # mapping
        self.var2qvar   = dict()
        self.sort2qvars = dict()
        # instantiated
        self.sort2ivars = dict()
        self.ivars_set  = set()
        # quantified
        self.qvars_set  = set()
        self.qstate     = TRUE()
        self.qterms     = set()
        self.neq_constraints    = dict()
        self.full_occur_sorts   = []
        # partition, change for each sort in full_occur_sorts
        self.norm_terms       = set()
        self.qvar2terms       = {}
        self.qvar2_norm_terms = {}
        self.qvars_partition  = {}
        self.single_class     = []
        self.multi_class      = []
        self.num_sing_class   = 0 
        self.num_mult_class   = 0 
        self.num_class        = 0 
        # inferred, change for each sort in full_occur_sorts
        self.infr_state = TRUE() 
        self.infr_terms = set()
        self.infr_qvars_set = set()
        # eq propagation
        self.eqMap  = dict()
        # result
        self.results = list()
        vprint_title(self.options, 'QInference', 5)
        vprint(self.options, f'prime: {str(self.prime)}', 5)

    def set_repr_state(self):
        values = self.prime.values
        literals = []
        for atom_id, atom in enumerate(self.atoms):
            val = values[atom_id]
            if val == '0':
                literals.append(Not(atom))
            elif val == '1':
                literals.append(atom)
            else:
                assert(val == '-')
        self.repr_state =  And(literals) if len(literals) != 0 else TRUE()
        vprint_title(self.options, 'set_repr_state', 5)
        vprint(self.options, f'repr_state: {pretty_print_str(self.repr_state)}', 5)

    def _get_used_qvars(self, sort):
        if not sort in self.sort2qvars:         
            self.sort2qvars[sort] = []
        qvars = self.sort2qvars[sort]
        return qvars

    def _get_next_unused_qvar(self, sort, qvars):
        qvar_id = len(qvars)
        qvar    = QInference.tran_sys._enum2qvar[sort][qvar_id]
        return qvar

    def record_sort_occurrence_in_vars(self):
        # relabel each var into qvar with index being order of occurrence
        # e.g. n2 n0 n1 m ---> Qn0 Qn1 Qn2 Qm0
        vprint_title(self.options, 'record_sort_occurrence_in_vars' , 5)
        for var in sorted(self.vars, key=str):
            sort = var.constant_type()
            if not sort in QInference.tran_sys._enum2qvar:
                continue
            qvars  = self._get_used_qvars(sort)
            qvar   = self._get_next_unused_qvar(sort, qvars) 
            qvars.append(qvar)
            self.var2qvar[var] = qvar
            self.qvars_set.add(qvar)
            
            vprint(self.options, f'var: {str(var)}', 5)
            vprint(self.options, f'sort: {str(sort)}', 5)
            vprint(self.options, f'qvar: {str(qvar)}', 5)
            vprint(self.options, '', 5)
            
        vprint(self.options, f'qvars_set: {str(self.qvars_set)}', 5) 
        vprint(self.options, f'sort2qvars: {str(self.sort2qvars)}', 5)
        vprint(self.options, f'var2qvar: {str(self.var2qvar)}', 5)
            

    def record_fully_occuring_sorts(self):
        for sort, qvars in self.sort2qvars.items():
            sort_size = len(QInference.tran_sys._enum2qvar[sort])
            if  ( (len(qvars) >= min_size) and 
                  (len(qvars) == sort_size) ):
                self.full_occur_sorts.append([sort, qvars])
        vprint_title(self.options, 'record_fully_occuring_sorts', 5)
        vprint(self.options, f'full_occur_sorts: {str(self.full_occur_sorts)}' , 5)

    def set_qvar_pairwise_neq_constraints(self):
        vprint_title(self.options, 'set_qvar_pairwise_neq_constraints', 5)
        for sort, qvars in self.sort2qvars.items():
            self.neq_constraints[sort] = []
            for i in range(len(qvars) - 1):
                for j in range(i+1, len(qvars)):
                    neq = Not(EqualsOrIff(qvars[i], qvars[j]))
                    self.neq_constraints[sort].append(neq)
                    vprint(self.options, pretty_print_str(neq), 5)

    def _get_instantiated_vars(self, sort):
        if sort not in self.sort2ivars:
            self.sort2ivars[sort] = list()
        return self.sort2ivars[sort]

    def _create_inst_var(self, sort, ivars):
        ivar_id = len(ivars)
        name = str(sort) + ':i' + str(ivar_id)
        return Symbol(name, sort)

    def _instantiate_qstate(self):
        for var in self.qstate.quantifier_vars():
            if var not in self.var2qvar:
                sort = var.symbol_type()
                ivars = self._get_instantiated_vars(sort)
                ivar  = self._create_inst_var(sort, ivars)
                ivars.append(ivar)
                self.ivars_set.add(ivar)
                self.var2qvar[var] = ivar 
                self.qvars_set.add(ivar)
        self.qstate = self.qstate.args()[0]

    def set_qstate(self):
        self.qstate = self.repr_state 
        if self.qstate.is_exists(): 
            self._instantiate_qstate()
        self.qstate = self.qstate.simple_substitute(self.var2qvar)
        self.qterms = flatten_cube(self.qstate)
        vprint_title(self.options, 'set_qstate', 5)
        vprint(self.options, f'qstate: {pretty_print_str(self.qstate)}', 5)
        vprint(self.options, f'qterms: {pretty_print_set(self.qterms)}', 5)

    def _split_eq(self, eq_term):
        lhs = eq_term.arg(0)
        rhs = eq_term.arg(1)
        if (not rhs.is_symbol()) or (lhs in self.qvars_set):
            lhs, rhs = rhs, lhs
        return (lhs, rhs)

    def _is_propagatable(self, eq_term):
        lhs, rhs = self._split_eq(eq_term)
        if ( (rhs.is_symbol)     and 
             (rhs in self.qvars_set) and 
             (not lhs.is_function_application()) ):
            rhst = rhs.symbol_type()
            if rhst.is_enum_type() and rhs not in self.eqMap:
                self.eqMap[rhs] = lhs
                self.qvars_set.discard(rhs)
                return True 
            elif rhs in self.ivars_set and rhs not in self.eqMap:
                self.eqMap[rhs] = lhs
                self.qvars_set.discard(rhs)
                return True 
        return False

    def _get_non_propagatable_terms(self):
        self.eqMap  = dict() # reset
        nprop_terms = set()
        for term in self.qterms:
            is_prop = False
            if term.is_equals():
                is_prop = self._is_propagatable(term)
            if not is_prop: 
                nprop_terms.add(term)
        return nprop_terms

    def _has_propagatable_terms(self):
        return len(self.eqMap) > 0

    def _propagate_until_fixpoint(self):
        assert(len(self.eqMap))
        fixed = False 
        while not fixed:
            fixed = True
            for lhs, rhs in self.eqMap.items():
                new_rhs = rhs.simple_substitute(self.eqMap)
                if new_rhs != rhs:
                    fixed = False
                self.eqMap[lhs] = new_rhs

    def _substitute_non_propagatable(self, nprop_terms):
        new_qterms = set()
        for term in nprop_terms:
            new_term = term.simple_substitute(self.eqMap)
            new_qterms.add(new_term)
        self.qterms = new_qterms

    def _substitute_neq_constraints(self):
        new_neq_constraints = dict()
        for sort, neqs in self.neq_constraints.items():
            new_neqs = []
            for neq in neqs:
                new_neq = neq.simple_substitute(self.eqMap)
                new_neqs.append(new_neq)
            new_neq_constraints[sort] = new_neqs
        self.neq_constraints = new_neq_constraints

    def _substitute_fully_occuring_sorts(self):
        new_full_occur_sorts = []
        for fs in self.full_occur_sorts:
            sort  = fs[0]
            qvars = fs[1]
            new_qvars = []
            for qvar in qvars:
                if qvar in self.eqMap:
                    qvar = self.eqMap[qvar]
                new_qvars.append(qvar)
            new_full_occur_sorts.append([sort,new_qvars])
        self.full_occur_sorts = new_full_occur_sorts

    def propagate_eq_constraints(self):
        vprint_title(self.options, 'propagate_eq_constraints', 5)
        vprint(self.options, f'qterms: {self.qterms}', 5)
        vprint(self.options, f'qterms before propagate: {self.qterms}', 5)
        nprop_terms = self._get_non_propagatable_terms() 
        if self._has_propagatable_terms():
            self._propagate_until_fixpoint()
            self._substitute_non_propagatable(nprop_terms)
            self._substitute_neq_constraints()
            self._substitute_fully_occuring_sorts()
        vprint(self.options, f'qterms after propagate: {self.qterms}', 5)

    def _get_state_from_terms(self, qterms):
        vprint_title(self.options, 'get_state_from_terms', 5)
        vprint(self.options, f'{qterms}', 5)
        qstate = And(qterms)
        vprint(self.options, f'qstate before exist: {pretty_print_str(qstate)}', 5)
        if len(self.qvars_set) != 0: 
            qstate = Exists(self.qvars_set, qstate)
        vprint(self.options, f'qstate after exist: {pretty_print_str(qstate)}', 5)
        return qstate

    def conjunct_qstate_with_neq_constraints(self):
        # append all pairwise neq constraints
        vprint_title(self.options, 'conjunct_qstate_with_neq_constraints', 5)
        constrained_qterms = self.qterms.copy()
        vprint(self.options, f'qterms: {self.qterms}', 5)
        vprint(self.options, f'constrained_qterms: {constrained_qterms}', 5)
        for neqs in self.neq_constraints.values():
            for neq in neqs:
                constrained_qterms.add(neq)
        constrained_qstate = self._get_state_from_terms(constrained_qterms)
        return constrained_qstate

    def can_infer_univ(self):
        can_infer  =  ( (QInference.tran_sys.gen == 'univ')
                       or (len(self.full_occur_sorts) == 0)
                       # or (len(self.relations) <= 1) 
                       or (len(self.qterms) < min_size) 
                      )
        vprint_title(self.options, 'can_infer_univ', 5)
        vprint(self.options, str(can_infer), 5)
        return can_infer

    def infer_univ(self):
        qstate = self.conjunct_qstate_with_neq_constraints()
        self.results.append((qstate, 'forall'))
        vprint_title(self.options, 'infer_univ', 5)
        vprint(self.options, pretty_print_str(qstate), 5)

    def init_infer(self):
        vprint_title(self.options, 'init_infer', 5)
        self.infr_qvars_set = set()
        self.infr_terms     = self.qterms.copy()
 
    def _create_normalized_qvar(self, sort):
        return Symbol('V:' +str(sort), sort)

    def _init_partition(self, qvars):
        self.norm_terms       = set()
        self.qvar2terms       = {}
        self.qvar2_norm_terms = {}
        self.qvars_partition  = {}
        for qvar in qvars:
            self.qvar2terms[qvar]       = set()
            self.qvar2_norm_terms[qvar] = set()

    def _get_term_qvars(self, term, qvars_set):
        term_fvars  = term.get_free_variables()
        term_qvars  = term_fvars.intersection(qvars_set)
        return term_qvars

    def _normalize_qvar_in_term(self, term, qvar, norm_qvar):
        subst = {}
        subst[qvar] = norm_qvar
        return term.substitute(subst)

    def _record_qvars_occurrence_in_terms(self, sort, qvars):
        # e.g. Qn0, Qn1, Qn2 ... -> Qn (norm_qvar)
        # terms: p(Qn0) q(Qn1) q(Qn2) q(Qn0)
        # qvar2term: Qn0 -> p(Qn0), q(Qn0); Qn1 -> q(Qn1); Qn2 -> q(Qn2)
        # qvar2_norm_terms: Qn0 -> p(Qn),q(Qn); Qn1 -> q(Qn); Qn2 -> q(Qn)
        self.norm_qvar  = self._create_normalized_qvar(sort)
        qvars_set = set(qvars)
        for term in self.qterms:
            term_qvars = self._get_term_qvars(term, qvars_set)
            for qvar in term_qvars:
                norm_term = self._normalize_qvar_in_term(term, qvar, self.norm_qvar)
                self.norm_terms.add(norm_term)
                self.qvar2terms[qvar].add(term)
                self.qvar2_norm_terms[qvar].add(norm_term)

    def _is_unique_qvar(self, qvar, norm_terms):
        return  ( len(norm_terms) == 0
                  or qvar in QInference.tran_sys.curr._states
                )
    
    def _add_key_qvar_to_partition(self, key, qvar):
        if key not in self.qvars_partition:
            self.qvars_partition[key] = set()
        self.qvars_partition[key].add(qvar)

    def _add_qvar_to_uniq_class(self, qvar, uniq_id):
        uniq_key =  (uniq_id, TRUE())
        self._add_key_qvar_to_partition(uniq_key, qvar)

    def _get_norm_key(self, norm_terms):
        # qvars that occur identically result in identical key
        sorted_norm_terms = sorted(norm_terms, key=str)
        norm_state = And(sorted_norm_terms)
        return (0, norm_state)  

    def _add_qvar_to_norm_class(self, qvar, norm_terms):
        norm_key = self._get_norm_key(norm_terms)
        self._add_key_qvar_to_partition(norm_key,qvar)

    def _finalize_partition(self):
        uniq_id = 1
        for qvar, norm_terms in self.qvar2_norm_terms.items():
            if self._is_unique_qvar(qvar, norm_terms):
                self._add_qvar_to_uniq_class(qvar, uniq_id)
                uniq_id += 1
            else:
                self._add_qvar_to_norm_class(qvar, norm_terms)
        
    def _partition_qvars_in_terms(self, sort, qvars):
        self._init_partition(qvars)
        self._record_qvars_occurrence_in_terms(sort, qvars) 
        self._finalize_partition() 
        vprint_title(self.options, 'partition_qvars_in_terms', 5)
        vprint(self.options, f'qvars_partition: {self.qvars_partition.values()}', 5)

    def _collect_singles_multiples_in_partition(self):
        self.single_class = []
        self.multi_class  = []
        for key, qvars in self.qvars_partition.items():
            if len(qvars) == 1:
                self.single_class.append(key)
            elif len(qvars) >= min_size:
                self.multi_class.append(key)
        self.num_sing_class  = len(self.single_class)
        self.num_mult_class  = len(self.multi_class)
        self.num_class       = len(self.qvars_partition)
        vprint_title(self.options, 'collect_singles_multiples_in_partition', 5)
        vprint(self.options, f'single class: {self.single_class}', 5)
        vprint(self.options, f'number single class: {self.num_sing_class}', 5)
        vprint(self.options, f'multi class: {self.multi_class}', 5)
        vprint(self.options, f'number multi class: {self.num_mult_class}', 5)

    def _check_single_partition(self, all_qvars):
        for qvars_class in self.qvars_partition.values():
            if len(qvars_class) != len(all_qvars):
                print("found single part with incomplete instances")
                return False 
        return True

    def _remove_qvars(self, qvars):
        for qvar in qvars:
            self.qvars_set.discard(qvar)

    def _remove_qvars_neq_constraints(self, sort):
        self.neq_constraints.pop(sort, None)

    def _get_first_qvar(self, qvars, sort=False):
        if sort:
            return sorted(qvars, key=str)[0]
        else:
            return qvars[0]

    def _add_first_qvar(self, first_qvar):
        if first_qvar.is_symbol():
            self.infr_qvars_set.add(first_qvar)

    def _get_renamed_norm_terms(self, norm_state, first_qvar):
        subst = {}
        subst[self.norm_qvar] = first_qvar 
        renamed_state = norm_state.simple_substitute(subst)
        return flatten_cube(renamed_state)

    def _replace_qvars_with_first_qvar(self, first_qvar):
        for terms in self.qvar2terms.values():
            for term in terms:
                self.infr_terms.discard(term)
        for _, norm_state in self.qvars_partition.keys():
            renamed_terms = self._get_renamed_norm_terms(norm_state, first_qvar)
            for term in renamed_terms:
                self.infr_terms.add(term)       
        self.qterms = self.infr_terms 

    def _infer_exists(self, sort, qvars):
        assert(self._check_single_partition(qvars))
        # {v0,v1,v2}---> \exists v0
        self._remove_qvars(qvars)
        self._remove_qvars_neq_constraints(sort)
        first_qvar = self._get_first_qvar(qvars)
        self._add_first_qvar(first_qvar)
        self._replace_qvars_with_first_qvar(first_qvar)

    def _get_term_func_names_with_sort(self):
        func_names = set()
        for terms in self.qvar2terms.values():
            for term in terms:
                is_neg = False
                if term.is_not():
                    is_neg = True
                    term = term.arg(0)
                func_name = term.function_name()
                func_names.add((is_neg, func_name))
        return list(func_names)

    def _get_sort_count(self, sort, func_names):
        sort_count = 0
        for (is_neg, func) in func_names:
            for arg_sort in func.symbol_type()._param_types:
                assert(arg_sort == sort)
                sort_count += 1
        return sort_count

    def _add_sort_qvars(self, sort, sort_count):
        qvars = QInference.tran_sys._enum2qvar[sort]
        if (len(qvars) < sort_count):
            new_qvars = []
            for i in range(len(qvars), sort_count):
                name = 'Q:' + str(sort) + f'{i}'
                new_qvars.append(Symbol(name, sort))
            qvars += new_qvars
        else:
            qvars = qvars[:sort_count]
        for qvar in qvars:
            self.infr_qvars_set.add(qvar)
        return qvars

    def _replace_qvars_with_multi_qvars(self, sort, func_names):
        for terms in self.qvar2terms.values():
            for term in terms:
                self.infr_terms.discard(term)

        sort_count = self._get_sort_count(sort, func_names)
        sort_qvars = self._add_sort_qvars(sort, sort_count) 
        sort_count = 0
        for (is_neg, func) in func_names:
            args = []
            for _ in func.symbol_type()._param_types:
                qvar = sort_qvars[sort_count]
                sort_count += 1
                args.append(qvar)
            term = Function(func, args)
            if is_neg:
                term = Not(term)
            self.infr_terms.add(term)       
        self.qterms = self.infr_terms 

    def _infer_multi_exists(self, sort, qvars):
        self._remove_qvars(qvars)
        self._remove_qvars_neq_constraints(sort)
        func_names = self._get_term_func_names_with_sort()
        self._replace_qvars_with_multi_qvars(sort, func_names)

    def _get_single_qvars_list(self):
        single_qvars = []
        for key in self.single_class:
            assert(key in self.qvars_partition)
            qclass = self.qvars_partition[key]
            assert(len(qclass) == 1)
            for qvar in qclass:
                single_qvars.append(qvar)
        return single_qvars

    def _get_multi_qvars_set(self, qvars, single_qvars):
        multi_qvars  = None
        for key in self.multi_class:
            assert(key in self.qvars_partition)
            qclass = self.qvars_partition[key]
            assert(len(qclass) >= min_size)
            if len(qclass) == (len(qvars) - len(single_qvars)):
                multi_qvars = qclass 
        return multi_qvars

    def _can_infer_forall_exists(self, single_qvars_list, multi_qvars_set):
        return len(single_qvars_list) != 0 and multi_qvars_set != None

    def _get_neqs_without_multi_qvars(self, sort, multi_qvars):
        neqs = []
        for neq in self.neq_constraints[sort]:
            neq_fvars   = neq.get_free_variables()
            common_vars = neq_fvars.intersection(multi_qvars)
            if len(common_vars) == 0:
                neqs.append(neq)
        return neqs 

    def _update_qvars_neq_constraints(self, sort, multi_qvars):
        if sort in self.neq_constraints:
            neqs = self._get_neqs_without_multi_qvars(sort, multi_qvars)
            self.neq_constraints.pop(sort, None)
            if len(neqs) != 0:
                self.neq_constraints[sort] = neqs 

    def _get_renamed_mult_term(self, term, first_mult_qvar):
        subst = {}
        subst[self.norm_qvar] = first_mult_qvar 
        return term.simple_substitute(subst)

    def _first_mult_equals_some_sing(self, first_mult_qvar, sing_qvars):
        eq_list = []
        for qvar in sing_qvars:
            eq_list.append(EqualsOrIff(qvar, first_mult_qvar))
        return Or(eq_list)

    def _replace_multi_qvars_with_first_multi_qvar(
            self, single_qvars, multi_qvars, first_mult_qvar):
        for qvar in multi_qvars:
            for term in self.qvar2terms[qvar]:
                self.infr_terms.discard(term)
        # {v1, v2}, {v3, v4} ----> \forall v1, v2 \exists v3
        # (v1 <-> v3) + (v2 <-> v3) + mult_term(v3)
        eq_sing =  self._first_mult_equals_some_sing(first_mult_qvar, single_qvars)
        for term in self.qvar2_norm_terms[first_mult_qvar]:
            mult_term = self._get_renamed_mult_term(term, first_mult_qvar)
            eq_or_mult = Or(eq_sing, mult_term)
            self.infr_terms.add(eq_or_mult)
        self.qterms = self.infr_terms

    def _infer_forall_exists(self, sort, qvars):
        # {v1, v2}, {v3, v4} ----> \forall v1,v2, \exists v3
        single_qvars = self._get_single_qvars_list() 
        multi_qvars  = self._get_multi_qvars_set(qvars, single_qvars)
        if self._can_infer_forall_exists(single_qvars, multi_qvars):
            self._remove_qvars(multi_qvars)
            self._update_qvars_neq_constraints(sort, multi_qvars)
            first_mult_qvar = self._get_first_qvar(multi_qvars, sort=True)
            self._add_first_qvar(first_mult_qvar)
            self._replace_multi_qvars_with_first_multi_qvar(
                single_qvars, multi_qvars, first_mult_qvar)

    def infer_fully_occur_sort(self, sort, qvars):
        self._partition_qvars_in_terms(sort, qvars) # pi(\psi, qvars)
        self._collect_singles_multiples_in_partition()
        vprint_title(self.options, 'infer_fully_occur_sort', 5)
        if self.num_class == 1:  # single class partition 
            vprint(self.options, 'infer exists', 5)
            self._infer_exists(sort, qvars)
        elif self.num_mult_class == 0 and self.is_orbit_size_1: # some relation has multiple parameter with type sort  
            vprint(self.options, 'infer multiple exists (for many-arity)', 5)
            self._infer_multi_exists(sort, qvars)
        elif ( self.num_class == (self.num_sing_class + self.num_mult_class)
               and self.num_mult_class == 1
               # and self.num_sing_class == 1 # FIXME ??????
             ): 
            vprint(self.options, 'infer forall exists', 5)
            self._infer_forall_exists(sort, qvars)
        vprint(self.options, f'number of multi-class: {self.num_mult_class}', 5)

    def add_required_neq_constraints(self):
        for neqs in self.neq_constraints.values():
            for neq in neqs:
                self.qterms.add(neq)

    def _separate_infr_terms(self):
        pre_terms  = set()
        post_terms = set()
        if len(self.infr_qvars_set) == 0:
            post_terms = self.qterms 
        else:
            for term in self.qterms:
                argvars = term.get_free_variables()
                argvars = argvars.intersection(self.infr_qvars_set)
                if len(argvars) == 0:
                    pre_terms.add(term)
                else:
                    post_terms.add(term)
        post_terms = sorted(post_terms, key=str)
        pre_terms  = sorted(pre_terms,  key=str)
        return pre_terms, post_terms

    def finalize_infer(self):
        # \exists qvars, pre_terms \forall infr_qvars post_terms
        # will be later negated to become  \forall qvars, pre_terms \exists infr_qvars post_terms
        pre_terms, post_terms = self._separate_infr_terms()
        qstate  = And(post_terms)
        if len(self.infr_qvars_set) != 0:
            qstate = ForAll(self.infr_qvars_set, qstate)
        if len(pre_terms) != 0:
            qstate = And(And(pre_terms), qstate)
        if len(self.qvars_set) != 0: 
            qstate = Exists(self.qvars_set, qstate)
        qtype = 'forall'
        if len(self.qvars_set) == 0 and len(self.infr_qvars_set) != 0:
            qtype = 'exists'
        if len(self.qvars_set) != 0 and len(self.infr_qvars_set) != 0:
            qtype = 'forall_exists'
        self.results.append((qstate, qtype))

    def _update_qvars_qterms(self, qstate):
        self.qvars_set = set()
        if qstate.is_exists():
            qvars = qstate.quantifier_vars()
            for qvar in qvars:
                self.qvars_set.add(qvar)
            qstate = qstate.args()[0]
        self.qterms = flatten_and(qstate)

    def _is_propagatable2(self, eq_term):
        lhs, rhs = self._split_eq(eq_term)
        if rhs.is_symbol and rhs in self.qvars_set:
            if rhs not in self.eqMap:
                self.eqMap[rhs] = lhs
                self.qvars_set.discard(rhs)
                return True 
        return False

    def _get_non_propagatable_terms2(self):
        self.eqMap = dict()
        nprop_terms = set()
        for term in self.qterms:
            is_prop = False
            if term.is_equals():
                is_prop = self._is_propagatable2(term)
            if not is_prop: 
                nprop_terms.add(term)
        return nprop_terms

    def _propagate_qstate_eq_constraints(self, qstate):
        new_qstate = qstate 
        self._update_qvars_qterms(qstate)
        nprop_terms = self._get_non_propagatable_terms2()
        if self._has_propagatable_terms():
            self._propagate_until_fixpoint()
            self._substitute_non_propagatable(nprop_terms)
            new_qstate = self._get_state_from_terms(self.qterms)
        return new_qstate 

    def propagate_results_eq_constraints(self):
        for (i, result) in enumerate(self.results):
            qstate = self._propagate_qstate_eq_constraints(result[0])
            self.results[i] = (qstate, result[1])

    def negate_qstates_in_results(self):
        vprint_title(self.options, 'negate_qstates_in_results', 5)
        for (i, result) in enumerate(self.results):
            qstate = result[0]
            qstate = Not(qstate)
            self.results[i] = (qstate, result[1])
            vprint(self.options, f'({pretty_print_str(qstate)}, {result[1]})', 5)

    def infer_quantifier(self):
        # original
        self.set_repr_state()
        self.vars      = self.repr_state.get_enum_constants() # sorts, quorums
        self.relations = self.repr_state.get_free_variables() # relations
        # mapping
        self.record_sort_occurrence_in_vars()
        self.record_fully_occuring_sorts()
        # quantified
        self.set_qstate()
        self.set_qvar_pairwise_neq_constraints()
        # if common.gopts.const > 0:
        #     self.propagate_eq_constraints()
        # infer quantifier
        if self.can_infer_univ():  # case: #(\psi, s) < |s|, for each sort s
            self.infer_univ()
        else: # case: #(\psi, s) = |s|, for some sort s 
            self.init_infer()
            for fs in self.full_occur_sorts:
                self.infer_fully_occur_sort(sort=fs[0], qvars=fs[1])
            self.add_required_neq_constraints()
            self.finalize_infer()
        # if common.gopts.const > 0:
        #     self.propagate_results_eq_constraints()
        self.negate_qstates_in_results()
        assert(len(self.results) == 1)
        result  = self.results[0]
        qclause = result[0]
        return qclause 

    @staticmethod
    def setup(atoms, tran_sys) -> None:
        QInference.atoms    = atoms
        QInference.tran_sys = tran_sys