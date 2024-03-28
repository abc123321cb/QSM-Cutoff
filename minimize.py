from typing import Dict,List,Set
from pysat.solvers import Glucose4 as GluSolver 
from pysat.solvers import Cadical153 as SatSolver
from pysat.allies.approxmc import Counter
from prime import *
from util import *
from verbose import *

def minus(target : list, source : set) -> list:
    temp = target.copy()
    target.clear()
    removed = []
    for x in temp:
        if x not in source:
            target.append(x)
        else:
            removed.append(x)
    return removed

class StackLevel():
    def __init__(self, level: int, start: int) -> None:
        self.level      = level
        self.start      = start 
        self.orbit_id   = -1 
        self.include    = True 
        self.unpended : List[int] = [] 

    def _switch_branch(self) -> None:
        self.include = not self.include

class CoverConstraints():
    def __init__(self, orbits : List[PrimeOrbit], atom_num : int, useMC : UseMC) -> None:
        self.sat_solver    = SatSolver() 
        self.model_counter = GluSolver() if useMC == UseMC.sat  else Counter()
        self.useMC         = useMC
        self.atom_vars : List[int] = []
        self.orbit_vars: List[int] = []
        self.coverage  : List[int] = [] 
        
        for atom_id in range(atom_num):
            self.atom_vars.append(atom_id+1)
        for orbit_id in range(len(orbits)):
            self.orbit_vars.append(atom_num + 1 + orbit_id)
        self.coverage = [-1]*len(orbits)
        self._init_clauses(orbits)

    def _atom_id(self, atom_var : int) -> int:
        return _atom_var -1
    def _orbit_id(self, orbit_var : int) -> int:
        return orbit_var - 1 - self.atom_num
    
    def reset_coverage(self) -> None:
        for (i, _) in enumerate(self.coverage):
            self.coverage[i] = -1

    def get_prime_literals(self, prime : Prime, negate=False) -> List[int]:
        literals = []
        for (id, val) in enumerate(prime.values):
            lit = self.atom_vars[id]
            if (val == '1' and negate) or (val == '0' and not negate):
                literals.append(-1*lit) 
            elif (val == '1' and not negate) or (val == '0' and negate):
                literals.append(lit)
        return literals

    def _init_clauses(self, orbits : List[PrimeOrbit]) -> None:
        for (orbit_id, orbit) in enumerate(orbits):
            orbit_var = self.orbit_vars[orbit_id]
            for prime in orbit.primes:
                clause = self.get_prime_literals(prime, negate=True) 
                clause.append(-1*orbit_var)
                self.sat_solver.add_clause(clause)
                self.model_counter.add_clause(clause)

    def is_essential(self, orbit : PrimeOrbit, pending, solution) -> bool:
        assumptions = self.get_prime_literals(orbit.repr_prime)
        assumptions += [self.orbit_vars[i] for i in pending  if i != orbit.id]
        assumptions += [self.orbit_vars[i] for i in solution if i != orbit.id]
        result = self.sat_solver.solve(assumptions)
        return result

    def get_coverage(self, orbit : PrimeOrbit, solution) -> int:
        assumptions = self.get_prime_literals(orbit.repr_prime)
        assumptions += [self.orbit_vars[i] for i in solution]
        if self.useMC == UseMC.sat:
            result, assigned = self.model_counter.propagate(assumptions)
            if result:
                self.coverage[orbit.id] = len(self.coverage) + 1 - len(assigned) 
            else:
                self.coverage[orbit.id] = 0 # covered by existing solution 
        return self.coverage[orbit.id] 

class Minimizer():
    def __init__(self, orbits: List[PrimeOrbit], options : QrmOptions) -> None: 
        atom_num = len(orbits[0].repr_prime.values) 
        self.orbits = orbits
        self.cover  = CoverConstraints(orbits, atom_num, options.useMC)
        self.max_cost = 1 + sum([orbit.qcost for orbit in orbits])
        self.ubound = self.max_cost
        self.decision_stack : List[StackLevel] = []
        self.pending  : List[int] = list(range(len(orbits)))
        self.solution : List[int] = []
        self.optimal_solutions : List[List[int]] = []
        self.options = options

    def _pverbose(self, line : str) -> None:
        if (self.options.verbose):
            print(line)
    
    def _get_cost(self) -> int:
        s = sum([self.orbits[i].qcost for i in self.solution])
        self._pverbose(f'Solution : {self.solution} has cost {s}.')
        return s

    def _invert_decision(self) -> None:
        top = self.decision_stack[-1]
        if top.include:
            assert(top.id == self.solution.pop())
        top._switch_branch()
        if top.include:
            self.solution.append(top.id)
        self._pverbose(f'Invert decision for {top.id} at level {top.level}')

    def _new_level(self) -> None:
        level = len(self.decision_stack)
        start = len(self.solution)
        self.decision_stack.append(StackLevel(level,start))
        self._pverbose(f'New level: {level}\n pending : {self.pending}\n solution : {self.solution}')

    def _decide_orbit(self) -> None:
        top = self.decision_stack[-1]
        self._pverbose(f'Decide in level {top.level} among pending : {self.pending}')
        max_val = 0
        max_id  = -1
        for id in self.pending:
            orbit = self.orbits[id]
            coverage = self.cover.coverage[id]
            if coverage > max_val:
                max_val = coverage
                max_id  = id
        assert(max_val > 0 and max_id >=0)
        top.id = max_id
        top.unpended.append(max_id)
        self.pending.remove(max_id)
        if top.include:
            self.solution.append(max_id)
        self._pverbose(f'Coverage : {[(i,c) for (i,c) in enumerate(self.cover.coverage)]}')
        self._pverbose(f'Decide {top.id} at level {top.level}')

    def _backtrack(self) -> None:
        top = self.decision_stack[-1]
        self._pverbose(f'Before backtrack at level {top.level}\n pending : {self.pending}\n solution : {self.solution}')
        self.pending.extend(top.unpended)
        if (len(self.solution) > top.start):
            del self.solution[top.start:]
        self.decision_stack.pop()
        self._pverbose(f'After backtrack at level {top.level}\n pending : {self.pending}\n solution : {self.solution}')
    
    def _reduce(self) -> None:
        self._pverbose(f'Before reduction : \n pending  : {self.pending}\n solution : {self.solution}')
        has_essential = self._add_essentials()
        has_covered   = self._remove_covered()
        self._pverbose(f'After reduction : \n pending  : {self.pending}\n solution : {self.solution}')
        if has_essential or has_covered:
            self._reduce()
    
    def _add_essentials(self) -> bool:
        essentials = set()
        for id in self.pending:
            orbit = self.orbits[id]
            if(self.cover.is_essential(orbit, self.pending, self.solution)):
                essentials.add(id)
        self.solution += list(essentials)
        removed = minus(self.pending, essentials)
        top = self.decision_stack[-1]
        top.unpended.extend(removed)
        self._pverbose(f'Essensial at level {top.level} : {essentials}')
        return len(essentials) > 0
    
    def _remove_covered(self) -> bool:
        covered = set()
        self.cover.reset_coverage()
        for id in self.pending:
            orbit = self.orbits[id]
            coverage = self.cover.get_coverage(orbit, self.solution)
            if coverage == 0:
                covered.add(id)
        removed = minus(self.pending, covered)
        top = self.decision_stack[-1]
        top.unpended.extend(removed)
        self._pverbose(f'Covered at level {top.level} : {covered}')
        return len(covered) > 0

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
        self._decide_orbit()
        cost1 = self._solve_one()
        if(cost1 == cost):
            self._backtrack()
            return cost1
        self._invert_decision()
        cost0 = self._solve_one()
        self._backtrack()
        return min(cost1,cost0)

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
        self._decide_orbit()
        self._solve_all()
        self._invert_decision()
        self._solve_all()
        self._backtrack()
        return 

    def solve(self) -> None:
        if self.options.all_solutions:
            self._solve_all()
        else:
            self._solve_one()

        print_banner('Final solutions')
        for (sid, solution) in enumerate(self.optimal_solutions):
            print(f'Solution {sid} : {solution} (length = {len(solution)})')
            costs = [self.orbits[i].qcost for i in solution]
            print(f'Total cost : {sum(costs)} (individual cost : {costs})')
            for id in solution: 
                print(f'invariant [I{id}] {self.orbits[id].quantified_form}')
            print('\n')
        

    
        
            

    
    