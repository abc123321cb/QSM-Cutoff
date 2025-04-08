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
from minimize import remove_target_from_source

class SelVar():
    def __init__(self, var_id, symbol):
        self.var_id  = var_id
        self.plit    = symbol 
        self.nlit    = il.Not(symbol)
        self.z3_plit = slv.formula_to_z3(symbol)
        self.z3_nlit = slv.formula_to_z3(il.Not(symbol))

class ConstraintPrime():
    def __init__(self, prime_id, lit_ids, fmla, cost) -> None:
        self.prime_id   = prime_id
        self.lit_ids    = lit_ids  # pos/neg of var_ids for all_vars 
        self.fmla       = fmla
        self.cost       = cost

class StackLevel():
    def __init__(self, level: int, start_idx: int) -> None:
        self.level                = level
        self.solution_start_idx   = start_idx
        self.prime_id             = -1 
        self.include_prime        = True 
        self.unpended : List[int] = [] 

    def _switch_branch(self) -> None:
        self.include_prime = not self.include_prime

class ConstraintMinimizer():
    def __init__(self, options : QrmOptions, primes: List[ConstraintPrime], minimize_fmla, all_vars, dep_axioms_fmla) -> None: 
        self.options = options
        self.primes        = primes
        self.minimize_fmla = minimize_fmla
        self.all_vars      = all_vars # indexing starts at 1
        self.max_cost      = 1 + sum([prime.cost for prime in primes])
        self.ubound        = self.max_cost
        self.bnb_max_depth = 0
        self.decision_stack : List[StackLevel] = []
        self.pending    : List[int] = list(range(len(primes)))
        self.solution   : List[int] = []
        self.optimal_solutions : List[List[int]] = []

        # select vars for primes
        self.sel_prime_vars : List[SelVar] = []
        # select vars for literals
        self.sel_lit_vars   : List[SelVar] = []
        # minimizing fmla
        self.select_fmla = None 
        slv.clear() 
        self.solver = slv.z3.Solver()

        # init
        self._init_select_vars()
        self._init_select_fmla(dep_axioms_fmla)

    #------------------------------------------------------------
    # Minimizer: initialization 
    #------------------------------------------------------------
    def _init_select_vars(self):
        for var_id, v in enumerate(self.all_vars):
            symbol = il.Symbol(f'v{var_id}', il.BooleanSort())
            svar   = SelVar(var_id, symbol)
            self.sel_lit_vars.append(svar)

        for prime_id, prime in enumerate(self.primes):
            symbol = il.Symbol(f'p{prime_id}', il.BooleanSort())
            svar   = SelVar(prime_id, symbol)
            self.sel_prime_vars.append(svar)

    def _init_select_fmla(self, dep_axioms_fmla):
        fmlas = []
        for var_id, v in enumerate(self.all_vars):
            if var_id != 0: 
                sel_symbol = self.sel_lit_vars[var_id].plit
                fmlas.append(il.Equals(v,sel_symbol))
        for prime_id, prime in enumerate(self.primes):
            sel_symbol = self.sel_prime_vars[prime_id].plit
            fmlas.append(il.Implies(sel_symbol, il.Not(prime.fmla)))
        fmlas += dep_axioms_fmla
        self.select_fmla = slv.formula_to_z3(il.And(*fmlas))
        self.solver.add(self.select_fmla)
    #------------------------------------------------------------
    # Minimizer: minimization 
    #------------------------------------------------------------
    def _is_essential(self, prime : ConstraintPrime):
        sel_lits =  [self.sel_lit_vars[l].z3_plit if l > 0 else self.sel_lit_vars[-1*l].z3_nlit for l in prime.lit_ids]
        for i in self.solution + self.pending:
            if i != prime.prime_id:
                sel_lits.append(self.sel_prime_vars[i].z3_plit)
        result = self.solver.check(sel_lits)
        return result == slv.z3.sat

    def _is_covered(self, prime : ConstraintPrime):
        sel_lits =  [self.sel_lit_vars[l].z3_plit if l > 0 else self.sel_lit_vars[-1*l].z3_nlit for l in prime.lit_ids]
        for i in self.solution:
            assert(i != prime.prime_id)
            sel_lits.append(self.sel_prime_vars[i].z3_plit)
        result = self.solver.check(sel_lits)
        return result == slv.z3.unsat

    #------------------------------------------------------------
    # Minimizer: minimization 
    #------------------------------------------------------------
    def _get_cost(self) -> int:
        s = sum([self.primes[i].cost for i in self.solution])
        return s

    def _get_min_cost_id(self) -> int:
        min_id   = self.pending[0]
        min_cost = self.primes[min_id].cost
        for i in self.pending:
            prime    = self.primes[i]
            if prime.cost < min_cost:
                min_cost = prime.cost
                min_id  = i
        assert(min_cost > 0 and min_id >=0)
        return min_id

    def _get_initial_phase(self) -> bool:
        # hot start
        return True

    def _invert_decision(self) -> None:
        assert(len(self.decision_stack))
        top = self.decision_stack[-1]
        if top.include_prime:
            assert(top.prime_id == self.solution.pop())
        top._switch_branch()
        if top.include_prime:
            self.solution.append(top.prime_id)

    def _new_level(self) -> None:
        level    = len(self.decision_stack)
        start_id = len(self.solution)
        self.bnb_max_depth = max(level, self.bnb_max_depth)
        self.decision_stack.append(StackLevel(level,start_id))

    def _decide(self) -> None:
        # decide prime id and initial phase
        assert(len(self.decision_stack))
        top = self.decision_stack[-1]
        top.prime_id      = self._get_min_cost_id() 
        top.include_prime = self._get_initial_phase() 
        # update pending and solution accordingly
        top.unpended.append(top.prime_id)
        self.pending.remove(top.prime_id)
        if top.include_prime:
            self.solution.append(top.prime_id)

    def _backtrack(self) -> None:
        assert(len(self.decision_stack))
        top = self.decision_stack[-1]
        # restore pending and solution
        self.pending.extend(top.unpended)
        if len(self.solution) > top.solution_start_idx:
            del self.solution[top.solution_start_idx:]
        self.decision_stack.pop()
    
    def _collect_essentials(self) -> Set[int]:
        essentials = set()
        for i in self.pending:
            prime = self.primes[i]
            if(self._is_essential(prime)):
                essentials.add(i)
        return essentials

    def _collect_covered(self) -> Set[int]:
        covered = set()
        for i in self.pending:
            prime = self.primes[i]
            if self._is_covered(prime):
                covered.add(i)
        return covered

    def _unpend(self, to_unpend : Set[int]) -> None:
        removed = remove_target_from_source(source=self.pending, target=to_unpend) 
        assert(len(self.decision_stack))
        top = self.decision_stack[-1]
        top.unpended.extend(removed)
    
    def _add_essentials(self) -> bool:
        essentials = self._collect_essentials()
        self.solution += list(essentials)
        self._unpend(essentials)
        return len(essentials) > 0
    
    def _remove_covered(self) -> bool:
        covered = self._collect_covered()
        self._unpend(covered)
        return len(covered) > 0

    def _reduce(self) -> None:
        has_essential = self._add_essentials()
        has_covered   = self._remove_covered()
        if has_essential or has_covered:
            self._reduce()

    def minimize(self):
        self._new_level()
        self._reduce() 
        cost = self._get_cost()
        if len(self.pending) == 0: 
            if cost < self.ubound:
                self.ubound = cost
                self.optimal_solutions = [self.solution.copy()] 
                self._backtrack()
                return cost 
            else:
                self._backtrack()
                return self.max_cost 
        if cost >= self.ubound:
            self._backtrack()
            return self.max_cost
        self._decide()
        cost1 = self.minimize()
        if(cost1 == cost):
            self._backtrack()
            return cost1
        self._invert_decision()
        cost2 = self.minimize()
        self._backtrack()
        return min(cost1,cost2)

    def get_minimized_constraints(self):
        assert(len(self.optimal_solutions) == 1)
        sol = self.optimal_solutions[0]
        fmlas = [self.primes[i].fmla for i in sol]
        return il.Or(*fmlas)