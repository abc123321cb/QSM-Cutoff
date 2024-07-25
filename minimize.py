from typing import List,Set
from transition_system import TransitionSystem
from prime import *
from cover_constraints import CoverConstraints
from prime_check import PrimeChecker
from util import QrmOptions
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

class Minimizer():
    def __init__(self, options : QrmOptions, tran_sys : TransitionSystem, instantiator : FiniteIvyInstantiator, orbits: List[PrimeOrbit]) -> None: 
        self.tran_sys = tran_sys
        self.orbits   = orbits
        self.cover    = CoverConstraints(tran_sys, instantiator, orbits, options.useMC)
        self.prime_checker  = PrimeChecker(options, tran_sys, instantiator)
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
            for def_symbol, def_ast in self.tran_sys.definitions.items():
                vprint(self.options, f'invariant [def_{str(def_symbol)}] {format(def_ast)} # definition', 3)
            vprint(self.options, '\n', 3)
        vprint(self.options, f'[MIN NOTE]: number of minimal solution found: {len(self.optimal_solutions)}', 2)
        
    def get_final_invariants(self) -> List[str]:
        invariants = []
        assert(len(self.optimal_solutions) >=1 )
        solution = self.optimal_solutions[0]
        total_cost = 0
        for id in solution:
            total_cost += self.orbits[id].qcost
            line = f'invariant [invar_{id}] {self.orbits[id].quantified_form} # qcost: {self.orbits[id].qcost}'
            invariants.append(line)
        for def_symbol, def_ast in self.tran_sys.definitions.items():
            line = f'invariant [def_{str(def_symbol)}] {format(def_ast)} # definition'
            invariants.append(line)
        vprint(self.options, f'[MIN NOTE]: number of invariants in minimal solution: {len(solution)}', 2)
        vprint(self.options, f'[MIN NOTE]: total qcost: {total_cost}', 2)
        return invariants

    def get_minimal_invariants(self) -> List[str]:
        if self.options.all_solutions:
            self._solve_all()
        else:
            self._solve_one()
        self.print_final_solutions()
        return self.get_final_invariants()

    def reduce_redundant_prime_orbits(self):
        self._new_level()
        self._reduce() 