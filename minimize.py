from typing import Dict,List,Set
from pysat.solvers import Glucose4 as SatCounter 
from pysat.solvers import Cadical153 as SatSolver
from pysat.allies.approxmc import Counter
from prime import *
from util import QrmOptions, UseMC
from verbose import *

def remove_target_from_source(source : list, target : set) -> list:
    temp = source.copy()
    source.clear()
    removed = []
    for x in temp:
        if x in target:
            removed.append(x)
        else:
            source.append(x)
    return removed

class StackLevel():
    def __init__(self, level: int, start_idx: int) -> None:
        self.level                = level
        self.solution_start_idx   = start_idx
        self.orbit_id             = -1 
        self.include_orbit        = True 
        self.unpended : List[int] = [] 

    def _switch_branch(self) -> None:
        self.include_orbit = not self.include_orbit

class CoverConstraints():
    def __init__(self, orbits : List[PrimeOrbit], useMC : UseMC) -> None:
        self.sat_solver     = SatSolver() 
        self.sat_counter    = SatCounter()
        self.approx_counter = None 
        self.useMC         = useMC
        self.atom_vars : List[int] = []
        self.orbit_vars: List[int] = []
        self.coverage  : List[int] = [-1]*len(orbits) 
        self.clauses       = []
        
        self._init_vars(orbits)
        self._init_solver(orbits)

    def get_prime_literals(self, prime : Prime, negate=False) -> List[int]:
        literals = []
        for (id, val) in enumerate(prime.values):
            lit = self.atom_vars[id]
            if (val == '1' and negate) or (val == '0' and not negate):
                literals.append(-1*lit) 
            elif (val == '1' and not negate) or (val == '0' and negate):
                literals.append(lit)
        return literals

    def _init_vars(self, orbits : List[PrimeOrbit]) -> None:
        atom_num = len(orbits[0].repr_prime.values)
        for atom_id in range(atom_num):
            self.atom_vars.append(atom_id+1)
        for orbit_id in range(len(orbits)):
            self.orbit_vars.append(atom_num + 1 + orbit_id)

    def _init_solver(self, orbits : List[PrimeOrbit]) -> None:
        for (orbit_id, orbit) in enumerate(orbits):
            orbit_var = self.orbit_vars[orbit_id]
            for prime in orbit.primes:
                clause = self.get_prime_literals(prime, negate=True) 
                clause.append(-1*orbit_var)
                self.sat_solver.add_clause(clause)
                self.clauses.append(clause)
                self.sat_counter.add_clause(clause)

    def _count_atom_var(self, assigned) -> int:
        count = 0
        for lit in assigned:
            var = abs(lit)
            if var <= len(self.atom_vars):
                count +=1
        return count

    def reset_coverage(self) -> None:
        for (i, _) in enumerate(self.coverage):
            self.coverage[i] = -1

    def is_essential(self, orbit : PrimeOrbit, pending, solution) -> bool:
        result = False
        for repr_prime in orbit.suborbit_repr_primes:
            assumptions = self.get_prime_literals(repr_prime)
            assumptions += [self.orbit_vars[i] for i in pending  if i != orbit.id]
            assumptions += [self.orbit_vars[i] for i in solution if i != orbit.id]
            result = self.sat_solver.solve(assumptions)
            if result:
                break
        return result

    def get_coverage(self, orbit : PrimeOrbit, solution) -> int:
        for repr_prime in orbit.suborbit_repr_primes:
            assumptions = self.get_prime_literals(repr_prime)
            assumptions += [self.orbit_vars[i] for i in solution]
            result = self.sat_counter.solve(assumptions)
            self.coverage[orbit.id] = 0
            if result:
                result, assigned = self.sat_counter.propagate(assumptions)
                atom_count = self._count_atom_var(assigned)
                len_assigned = len(self.atom_vars) +1 - atom_count

                if self.useMC == UseMC.sat:
                    self.coverage[orbit.id] += len_assigned 
                else:
                    cnf  = self.clauses                                                                    
                    cnf += [[a] for a in assumptions]
                    self.approx_counter = Counter(formula=cnf, epsilon=0.50, delta=0.50)
                    result = self.approx_counter.count()
                    self.coverage[orbit.id] += max(len_assigned, result)
                    self.approx_counter.delete()
                    self.approx_counter = None
            else:
                self.coverage[orbit.id] += 0 # covered by existing solution 
        return self.coverage[orbit.id] 

class Minimizer():
    def __init__(self, orbits: List[PrimeOrbit], options : QrmOptions) -> None: 
        self.orbits = orbits
        self.cover  = CoverConstraints(orbits, options.useMC)
        self.max_cost = 1 + sum([orbit.qcost for orbit in orbits])
        self.ubound = self.max_cost
        self.decision_stack : List[StackLevel] = []
        self.pending  : List[int] = list(range(len(orbits)))
        self.solution : List[int] = []
        self.optimal_solutions : List[List[int]] = []
        self.options = options

    def _get_cost(self) -> int:
        s = sum([self.orbits[i].qcost for i in self.solution])
        vprint(self.options, f'\nSolution : {self.solution} has cost {s}.', 5)
        return s

    def _get_max_coverage_id(self) -> int:
        max_val = 0
        max_id  = -1
        for id in self.pending:
            orbit = self.orbits[id]
            coverage = self.cover.coverage[id]
            if coverage > max_val:
                max_val = coverage
                max_id  = id
        assert(max_val > 0 and max_id >=0)
        return max_id

    def _get_initial_phase(self) -> bool:
        # hot start
        return True

    def _invert_decision(self) -> None:
        assert(len(self.decision_stack))
        top = self.decision_stack[-1]
        if top.include_orbit:
            assert(top.orbit_id == self.solution.pop())
        top._switch_branch()
        if top.include_orbit:
            self.solution.append(top.id)
        vprint(self.options, f'\nInvert decision for {top.orbit_id} at level {top.level}', 5)

    def _new_level(self) -> None:
        level    = len(self.decision_stack)
        start_id = len(self.solution)
        self.decision_stack.append(StackLevel(level,start_id))
        vprint(self.options, f'\nNew level: {level}\n pending : {self.pending}\n solution : {self.solution}', 5)

    def _decide(self) -> None:
        # decide orbit id and initial phase
        assert(len(self.decision_stack))
        top = self.decision_stack[-1]
        top.orbit_id      = self._get_max_coverage_id() 
        top.include_orbit = self._get_initial_phase() 
        vprint(self.options, f'\nDecide in level {top.level} among pending : {self.pending}', 5)
        vprint(self.options, f'Coverage : {[(i,c) for (i,c) in enumerate(self.cover.coverage)]}', 5)
        vprint(self.options, f'Decide {top.orbit_id} with phase {top.include_orbit} at level {top.level}', 5)
        # update pending and solution accordingly
        top.unpended.append(top.orbit_id)
        self.pending.remove(top.orbit_id)
        if top.include_orbit:
            self.solution.append(top.orbit_id)
        vprint(self.options, f'After decision at level {top.level}\n pending : {self.pending}\n solution : {self.solution}', 5)

    def _backtrack(self) -> None:
        assert(len(self.decision_stack))
        top = self.decision_stack[-1]
        vprint(self.options,f'\nBefore backtrack at level {top.level}\n pending : {self.pending}\n solution : {self.solution}', 5)
        # restore pending and solution
        self.pending.extend(top.unpended)
        if len(self.solution) > top.solution_start_idx:
            del self.solution[top.solution_start_idx:]
        self.decision_stack.pop()
        vprint(self.options, f'After backtrack at level {top.level}\n pending : {self.pending}\n solution : {self.solution}', 5)
    
    def _collect_essentials(self) -> Set[int]:
        essentials = set()
        for id in self.pending:
            orbit = self.orbits[id]
            if(self.cover.is_essential(orbit, self.pending, self.solution)):
                essentials.add(id)
        if self.options.verbosity >=5:
            assert(len(self.decision_stack))
            top = self.decision_stack[-1]
            vprint(self.options, f'Essensial at level {top.level} : {essentials}', 5)
        return essentials

    def _collect_covered(self) -> Set[int]:
        vprint(self.options, f'Before removed\n coverage : {[(i,c) for (i,c) in enumerate(self.cover.coverage)]}', 5)
        covered = set()
        self.cover.reset_coverage()
        for id in self.pending:
            orbit = self.orbits[id]
            coverage = self.cover.get_coverage(orbit, self.solution)
            if coverage == 0:
                covered.add(id)
        if self.options.verbosity >=5:
            assert(len(self.decision_stack))
            top = self.decision_stack[-1]
            vprint(self.options, f'After removed\n coverage : {[(i,c) for (i,c) in enumerate(self.cover.coverage)]}', 5)
            vprint(self.options, f'Covered at level {top.level} : {covered}', 5)
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
        vprint(self.options, f'\nBefore reduction : \n pending  : {self.pending}\n solution : {self.solution}', 5)
        has_essential = self._add_essentials()
        has_covered   = self._remove_covered()
        vprint(self.options, f'After reduction : \n pending  : {self.pending}\n solution : {self.solution}', 5)
        if has_essential or has_covered:
            self._reduce()

    def _solve_one(self) -> int: 
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
        cost1 = self._solve_one()
        if(cost1 == cost):
            self._backtrack()
            return cost1
        self._invert_decision()
        cost2 = self._solve_one()
        self._backtrack()
        return min(cost1,cost2)

    def _solve_all(self) -> None:
        self._new_level()
        self._reduce() 
        cost = self._get_cost()
        if len(self.pending) == 0: 
            if cost < self.ubound:
                self.ubound = cost
                self.optimal_solutions = [self.solution.copy()] 
                self._backtrack()
                return 
            elif cost == self.ubound:
                self.optimal_solutions.append(self.solution.copy()) 
                self._backtrack()
                return 
        if cost > self.ubound:
            self._backtrack()
            return
        self._decide()
        self._solve_all()
        self._invert_decision()
        self._solve_all()
        self._backtrack()
        return 

    def print_final_solutions(self) -> None:
        vprint_step_banner(self.options, f'[MIN RESULT]: Minimized Invariants on [{self.options.instance_name}: {self.options.size_str}]', 3)
        for (sid, solution) in enumerate(self.optimal_solutions):
            vprint(self.options, f'Solution {sid} : {solution} (length = {len(solution)})', 3)
            costs = [self.orbits[i].qcost for i in solution]
            vprint(self.options, f'Total cost : {sum(costs)} (individual cost : {costs})', 3)
            for id in solution: 
                vprint(self.options, f'invariant [invar_{id}] {self.orbits[id].quantified_form} # qcost: {self.orbits[id].qcost}', 3)
            vprint(self.options, '\n', 3)
        vprint(self.options, f'[MIN NOTE]: number of minimal solution found: {len(self.optimal_solutions)}', 2)

    def remove_quorum_invariants(self, tran_sys):
        solution = self.optimal_solutions[0]
        remove = []
        for id in solution:
            qclause = self.orbits[id].qclause
            qvars = qclause.get_quantifier_variables()
            qvars_sorts = set()
            for qvar in qvars:
                qvars_sorts.add(qvar.symbol_type())
            for qsymbol in tran_sys._quorums_symbols:
                member_func = qsymbol.symbol_type()
                assert(len(member_func.param_types) == 2)
                sort0 = member_func.param_types[0]
                sort1 = member_func.param_types[1]
                if sort0 in qvars_sorts and sort1 in qvars_sorts:
                    remove.append(id)
        for id in remove: 
            vprint(self.options, f'[MIN NOTE]: remove invariant [invar_{id}] {self.orbits[id].quantified_form} # qcost: {self.orbits[id].qcost}', 2)
            solution.remove(id)
        
    def get_final_invariants(self) -> List[str]:
        invariants = []
        assert(len(self.optimal_solutions) >=1 )
        solution = self.optimal_solutions[0]
        total_cost = 0
        for id in solution:
            total_cost += self.orbits[id].qcost
            line = f'invariant [invar_{id}] {self.orbits[id].quantified_form} # qcost: {self.orbits[id].qcost}'
            invariants.append(line)
        vprint(self.options, f'[MIN NOTE]: number of invariants in minimal solution: {len(solution)}', 2)
        vprint(self.options, f'[MIN NOTE]: total qcost: {total_cost}', 2)
        return invariants

    def get_minimal_invariants(self, tran_sys) -> List[str]:
        if self.options.all_solutions:
            self._solve_all()
        else:
            self._solve_one()
        self.remove_quorum_invariants(tran_sys)
        self.print_final_solutions()
        return self.get_final_invariants()
