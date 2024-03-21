from typing import Dict,List,Set
from pysat.solvers import Cadical153 as SatSolver 
from prime import *

def add(target : list, source : set) -> None:
    target.extend(list(source))

def minus(target : list, source : set) -> None:
    temp = target.copy()
    target.clear()
    for x in temp:
        if x not in source:
            target.append(x)
 
class CoverConstraints():
    def __init__(self, orbits : List[PrimeOrbit], atom_num : int) -> None:
        self.sat_solver    = SatSolver() 
        self.model_counter = # TODO 
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
        for (i, _) = enumerate(self.coverage):
            self.coverage[i] = -1

    def get_prime_literals(self, prime : Prime, negate=False) -> List[int]:
        literals = []
        for (id, val) in enumerate(prime.values):
            lit = self._atom_var[id]
            if (val == '1' and negate) or (val == '0' and !negate):
                literals.append(-1*lit) 
            else:
                literals.append(lit)
        return literals

    def _init_clauses(self, orbits : List[PrimeOrbit]) -> None:
        for (orbit_id, orbit) in enumerate(orbits)
            orbit_var = self._orbit_var[orbit_id]
            for prime in orbit.primes:
                clause = self.get_prime_literals(prime, negate=True) 
                clause.append(-1*orbit_var)
                self.sat_solver.add_clause(clause)

    def is_essential(self, orbit : PrimeOrbit, pending, solution) -> bool:
        orbit_var = self.orbit_vars[orbit.id]
        assumptions = self.get_prime_literals(orbit.repr_prime)
        assumptions += [self.orbit_vars[i] for i in pending if self.orbit_vars[i] != orbit_var]
        assumptions += [self.orbit_vars[i] for i in solultion if self.orbit_vars[i] != orbit_var]
        result = self.sat_solver.solve(assumptions)
        return result

    def get_coverage(self, orbit : PrimeOrbit, solution) -> int:
        orbit_var = self.orbit_vars[orbit.id]
        assumptions = self.get_prime_literals(orbit.repr_prime)
        assumptions += [self.orbit_vars[i] for i in solultion if self.orbit_vars[i] != orbit_var]
        result = self.model_counter.solve(assumptions)
        self.coverage[orbid.id] = result
        return result

class Minimizer():
    def __init__(self, orbits : List[PrimeOrbit], atom_num : int) -> None: 
        atom_num = len(orbits[0].values) 
        self.orbits = orbits
        self.cover  = CoverConstraints(orbits, atom_num)
        self.ubound  = 1 + sum([orbit.qcost for orbit in orbits])
    
    def _get_cost(self, solution) -> int:
        return sum([self.orbits[i].qcost for i in solution])

    def _get_optimal(self, solution1, solution0) -> List[int]:
        if solution1 == []:
            return solution0
        elif solution0 == []:
            return solution1
        else:
            sum1 = self._get_cost(solution1)
            sum0 = self._get_cost(solution0)
            return solution1 if sum1 > sum0 else solution0

    def _choose_orbit(self) -> int:
        max_val = max(self.cover.coverage)
        return self.cover.coverage.index(max_val)
    
    def _reduce(self, pending, solution, coverage) -> None:
        has_essential = self._add_essentials(pending, solution)
        has_covered   = self._remove_covered(pending, solution, coverage)
        if has_essential or has_covered:
            self._reduce(pending,solution,coverage)
    
    def _add_essentials(self, pending, solution) -> bool:
        essentials = set()
        for id in pending:
            orbit = self.orbits[id]
            if(self.cover.is_essential(orbit, pending, solution)):
                essentials.add(id)
        add(solution, essentials)
        minus(pending, essentials)
        return len(essentials) > 0
    
    def _remove_covered(self, pending, solution) -> bool:
        covered = set()
        self.cover.reset_coverage()
        for id in pending:
            orbit = orbits[id]
            coverage = self.cover.get_coverage(orbit, solution)
            if coverage == 0:
                covered.add(id)
        minus(pending, essentials)
        return len(covered) > 0

    def solve(self, pending=range(len(self.orbits)), solution=[]) -> List[int]:
        self._reduce(pending, solution) 
        cost = self._get_cost(solution)
        if len(pending) == 0:
            if cost < self.ubound:
                self.ubound = cost
                return solution
            else:
                return []
        lbound = cost
        if lbound >= ubound:
            return [] 

        id = self._choose_orbit()
        # include id to solution
        solution1 = self.solve(pending.copy().remove(id), solution.copy().append(id))
        if self._get_cost(solution1) == lbound:
            return solution1 
        # exlucde id from solution
        solution0 = self.solve(pending.copy().remove(id), solution.copy().append(id))
        return self._get_optimal(solution1, solution0)

    
        
            

    
    