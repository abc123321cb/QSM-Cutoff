import os
import csv
from typing import Dict, List, Set
from transition_system import TransitionSystem
from prime import *
from cover_constraints import CoverConstraints
from finite_ivy_instantiate import FiniteIvyInstantiator
from util import QrmOptions, ForwardMode
from verbose import *
from ivy import ivy_logic as il

class Rmin():
    # static members
    definitions  = {}
    eq_relations = []
    def_lines = []
    eq_lines  = []
    def_qcost = 0
    eq_qcost  = 0
    
    def __init__(self, solution, orbits):
        self.solution    = solution
        self.invariants  = [orbits[i].quantified_form for i in solution] 
        self.invar_lines = []
        for i in solution:
            line = f'invariant [invar_{i}] {str(orbits[i].quantified_form)} # qcost: {orbits[i].qcost}'
            self.invar_lines.append(line)
        
    @staticmethod
    def set_definitions_and_eq_relations(tran_sys : TransitionSystem):
        Rmin.definitions  = tran_sys.definitions
        Rmin.eq_relations = list(tran_sys.closed_atom_equivalence_constraints)
        for def_symbol, def_ast in tran_sys.definitions.items():
            (num_forall, num_exists, num_lits) = futil.count_quantifiers_and_literals(il.close_formula(def_ast))
            qcost = num_forall + num_exists + num_lits
            line = f'invariant [def_{str(def_symbol)}] {format(il.close_formula(def_ast))} # definition, qcost: {qcost}'
            Rmin.def_lines.append(line)
            Rmin.def_qcost += qcost
        for i, atom_equiv in enumerate(tran_sys.closed_atom_equivalence_constraints):
            (num_forall, num_exists, num_lits) = futil.count_equiv_invar_quantifiers_and_literals(atom_equiv)
            qcost = num_forall + num_exists + num_lits
            line = f'invariant [eq_{i}] {format(atom_equiv)} # equivalence relation, qcost: {qcost}'
            Rmin.eq_lines.append(line)
            Rmin.eq_qcost += qcost

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
        self.decision_targets: List[int] = []
        self.decision_added: List[int] = []

    def _switch_branch(self) -> None:
        self.include_orbit = not self.include_orbit

class Minimizer():
    def __init__(self, options : QrmOptions, tran_sys : TransitionSystem, instantiator : FiniteIvyInstantiator, protocol : Protocol, orbits: List[PrimeOrbit], dnf = False) -> None: 
        self.tran_sys      = tran_sys
        self.orbits        = orbits
        self.orbit_groups : OrbitGroups
        self.cover         = CoverConstraints(options, tran_sys, instantiator, protocol, orbits, options.useMC, dnf)
        self.max_orbit_qcost = 6
        self.max_cost      = 0 
        self.ubound        = 0 
        self.bnb_max_depth = 0
        self.decision_stack : List[StackLevel] = []
        self.pending    : List[int] = list(range(len(orbits)))
        self.pending_orbit_groups : List[OrbitGroup]
        self.orbit_to_group_id: Dict[int, int] = {}
        self.solution   : List[int] = []
        self.solution_orbit_groups : List[OrbitGroup]
        self.optimal_solutions : List[List[int]] = []
        self.rmin          = []
        self.options = options
        self.is_dnf = dnf
        self.first_solution_found = False
        self._last_inference_list : List[int] = []


    def _remove_high_cost_from_pending(self):
        max_pattern = 3
        # self.pending = [i for i, orbit in enumerate(self.orbits) if orbit.qcost <= self.max_orbit_qcost]

        # skipped = len(self.orbits) - len(self.pending)
        # if skipped > 0:
        #     vprint(self.options, f'[MIN NOTE]: skipped {skipped} orbits with qcost > {self.max_orbit_qcost}', 3)

        allowed_groups = sorted([group for group in self.orbit_groups.groups
            if group.pattern <= max_pattern], key=lambda group: group.sig)
        allowed_orbit_ids = {
            orbit.id
            for group in allowed_groups
            for orbit in group.orbits
        }
        self.pending = [orbit_id for orbit_id in self.pending if orbit_id in allowed_orbit_ids]

        sanity_result = True
        protocol = self.orbit_groups.protocol
        if self.options.forward_mode == ForwardMode.Sym_DFS:
            sanity_result = self._compare_symmetry_quotient(0, self.pending, protocol)
        else:
            sanity_result = self._equivalence_checking(0, self.pending, protocol)
        
        if not sanity_result:
            return False
        
        return True

    #------------------------------------------------------------
    # Minimizer: minimization 
    #------------------------------------------------------------
    def _get_cost(self) -> int:
        if self._use_group_bnb():
            selected_group_ids = self._orbit_ids_to_group_ids(self.solution)
            s = sum([self.orbit_groups.groups[group_id].qcost for group_id in selected_group_ids])
        else:
            s = sum([self.orbits[i].qcost for i in self.solution])
        vprint(self.options, f'\nSolution : {self.solution} has cost {s}.', 5)
        return s

    def _get_max_coverage_id(self) -> int:
        max_val = 0
        max_id  = -1
        for i in self.pending:
            coverage = self.cover.coverage[i]
            if coverage > max_val:
                max_val = coverage
                max_id  = i
        assert(max_val > 0 and max_id >=0)
        return max_id

    def _use_group_bnb(self) -> bool:
        return bool(self.options.total_order and getattr(self, 'orbit_groups', None) is not None)

    def _get_pending_group_ids(self) -> List[int]:
        pending_set = set(self.pending)
        return [
            group.id for group in self.orbit_groups.groups
            if any(orbit.id in pending_set for orbit in group.orbits)
        ]

    def _get_pending_orbits_in_group(self, group_id: int) -> List[int]:
        pending_set = set(self.pending)
        group = self.orbit_groups.groups[group_id]
        return [orbit.id for orbit in group.orbits if orbit.id in pending_set]

    def _get_max_coverage_group_id(self) -> int:
        min_val = (float('inf'), float('inf'))
        min_id = -1
        for group_id in self._get_pending_group_ids():
            group = self.orbit_groups.groups[group_id]
            pending_count = len(self._get_pending_orbits_in_group(group_id))
            score = (group.qcost, pending_count)
            if score < min_val:
                min_val = score
                min_id = group_id
        assert(min_val[0] > 0 and min_id >= 0)
        return min_id

    def _orbit_ids_to_group_ids(self, orbit_ids: List[int]) -> List[int]:
        if not self._use_group_bnb():
            return []
        group_ids = {
            self.orbit_to_group_id[orbit_id]
            for orbit_id in orbit_ids
            if orbit_id in self.orbit_to_group_id
        }
        return sorted(group_ids)

    def _format_pending_solution_log(self) -> str:
        if self._use_group_bnb():
            pending_groups = self._orbit_ids_to_group_ids(self.pending)
            solution_groups = self._orbit_ids_to_group_ids(self.solution)
            return (
                f'pending : {self.pending}\n'
                f'pending_groups : {pending_groups}\n'
                f'solution : {self.solution}\n'
                f'solution_groups : {solution_groups}'
            )
        return f'pending : {self.pending}\nsolution : {self.solution}'

    def _get_initial_phase(self) -> bool:
        # hot start
        return True

    def _invert_decision(self) -> None:
        assert(len(self.decision_stack))
        top = self.decision_stack[-1]
        if top.include_orbit:
            assert(len(self.solution) >= len(top.decision_added))
            if len(top.decision_added) > 0:
                assert(self.solution[-len(top.decision_added):] == top.decision_added)
                del self.solution[-len(top.decision_added):]
        top._switch_branch()
        top.decision_added = []
        if top.include_orbit:
            self.solution.extend(top.decision_targets)
            top.decision_added = top.decision_targets.copy()
        vprint(self.options, f'\nInvert decision for {top.orbit_id} at level {top.level}', 5)

    def _new_level(self) -> None:
        level    = len(self.decision_stack)
        start_id = len(self.solution)
        self.bnb_max_depth = max(level, self.bnb_max_depth)
        self.decision_stack.append(StackLevel(level,start_id))
        vprint(self.options, f'\nNew level: {level}\n{self._format_pending_solution_log()}', 5)

    def _decide(self) -> None:
        # decide orbit/group id and initial phase
        assert(len(self.decision_stack))
        top = self.decision_stack[-1]
        if self._use_group_bnb():
            top.orbit_id = self._get_max_coverage_group_id()
            top.decision_targets = self._get_pending_orbits_in_group(top.orbit_id)
            cov_msg = [(group_id, len(self._get_pending_orbits_in_group(group_id))) for group_id in self._get_pending_group_ids()]
        else:
            top.orbit_id = self._get_max_coverage_id()
            top.decision_targets = [top.orbit_id]
            cov_msg = [(i, c) for (i, c) in enumerate(self.cover.coverage)]
        top.include_orbit = self._get_initial_phase() 
        vprint(self.options, f'\nDecide in level {top.level} among pending : {self.pending}', 5)
        vprint(self.options, f'Coverage : {cov_msg}', 5)
        vprint(self.options, f'Decide {top.orbit_id} with phase {top.include_orbit} at level {top.level}', 5)
        # update pending and solution accordingly
        self._unpend(set(top.decision_targets))
        if top.include_orbit:
            self.solution.extend(top.decision_targets)
            top.decision_added = top.decision_targets.copy()
        vprint(self.options, f'After decision at level {top.level}\n{self._format_pending_solution_log()}', 5)

    def _backtrack(self) -> None:
        assert(len(self.decision_stack))
        top = self.decision_stack[-1]
        vprint(self.options,f'\nBefore backtrack at level {top.level}\n{self._format_pending_solution_log()}', 5)
        # restore pending and solution
        self.pending.extend(top.unpended)
        if len(self.solution) > top.solution_start_idx:
            del self.solution[top.solution_start_idx:]
        self.decision_stack.pop()
        vprint(self.options, f'After backtrack at level {top.level}\n{self._format_pending_solution_log()}', 5)
    
    def _collect_essentials(self) -> Set[int]:
        essentials = set()
        for i in self.pending:
            orbit = self.orbits[i]
            if(self.cover.is_essential(orbit, self.pending, self.solution)):
                essentials.add(i)
        if self.options.verbosity >=5:
            assert(len(self.decision_stack))
            top = self.decision_stack[-1]
            vprint(self.options, f'Essensial at level {top.level} : {essentials}', 5)
        return essentials

    def _collect_essential_groups(self) -> Set[int]:
        essentials = set()
        for group_id in self._get_pending_group_ids():
            group = self.orbit_groups.groups[group_id]
            if self.cover.is_essential_group(group, self.pending, self.solution):
                essentials.update(self._get_pending_orbits_in_group(group_id))
        if self.options.verbosity >=5:
            assert(len(self.decision_stack))
            top = self.decision_stack[-1]
            vprint(self.options, f'Essensial at level {top.level} : {essentials}', 5)
        return essentials
    

    def _collect_covered(self) -> Set[int]:
        vprint(self.options, f'Before removed\n coverage : {[(i,c) for (i,c) in enumerate(self.cover.coverage)]}', 5)
        covered = set()
        for i in self.pending:
            orbit = self.orbits[i]
            if not self.cover.has_coverage(orbit, self.solution):
                covered.add(i)
        if self.options.verbosity >=5:
            assert(len(self.decision_stack))
            top = self.decision_stack[-1]
            vprint(self.options, f'After removed\n coverage : {[(i,c) for (i,c) in enumerate(self.cover.coverage)]}', 5)
            vprint(self.options, f'Covered at level {top.level} : {covered}', 5)
        return covered

    def _collect_covered_groups(self) -> Set[int]:
        vprint(self.options, f'Before removed\n coverage : {[(i,c) for (i,c) in enumerate(self.cover.coverage)]}', 5)
        covered = set()
        for group_id in self._get_pending_group_ids():
            group = self.orbit_groups.groups[group_id]
            if not self.cover.has_coverage_group(group, self.solution):
                covered.update(self._get_pending_orbits_in_group(group_id))
        if self.options.verbosity >=5:
            assert(len(self.decision_stack))
            top = self.decision_stack[-1]
            vprint(self.options, f'After removed\n covered_groups : {sorted(self._get_pending_group_ids())}', 5)
            vprint(self.options, f'Covered at level {top.level} : {covered}', 5)
        return covered

    def _unpend(self, to_unpend : Set[int]) -> None:
        removed = remove_target_from_source(source=self.pending, target=to_unpend) 
        assert(len(self.decision_stack))
        top = self.decision_stack[-1]
        top.unpended.extend(removed)
    
    def _add_essentials(self) -> bool:
        essentials = self._collect_essential_groups() if self._use_group_bnb() else self._collect_essentials()
        self.solution += list(essentials)
        self._unpend(essentials)
        return len(essentials) > 0
    
    def _remove_covered(self) -> bool:
        covered = self._collect_covered_groups() if self._use_group_bnb() else self._collect_covered()
        self._unpend(covered)
        return len(covered) > 0

    def _reduce(self) -> None:
        vprint(self.options, f'\nBefore reduction : \n{self._format_pending_solution_log()}', 5)
        has_essential = self._add_essentials()
        has_covered   = self._remove_covered()
        vprint(self.options, f'After reduction : \n{self._format_pending_solution_log()}', 5)
        if has_essential or has_covered:
            self._reduce()

    def _solve_one(self) -> int: 
        # Early return if first solution already found
        # if self.first_solution_found:
        #     self._backtrack()
        #     return self.max_cost
        
        self._new_level()
        self._reduce() 
        cost = self._get_cost()
        if len(self.pending) == 0: 
            if cost < self.ubound:
                self.ubound = cost
                self.optimal_solutions = [self.solution.copy()]
                self.first_solution_found = True
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

    #------------------------------------------------------------
    # Minimizer: reduction 
    #------------------------------------------------------------
    def _remove_definition_prime_orbits_from_pending(self) -> Set[int]:
        def_orbits : Set[int]  = set()
        for orbit_id in self.pending:
            orbit = self.orbits[orbit_id]
            is_definition = self.cover.is_definition_prime(orbit)
            if (is_definition):
                def_orbits.add(orbit_id)
        vprint(self.options, f'definition primes: {def_orbits}', 5)
        remove_target_from_source(source=self.pending, target=def_orbits)

    #------------------------------------------------------------
    # Minimizer: helpers 
    #------------------------------------------------------------
    def _write_orbit_csv(self) -> None:
        if not getattr(self.options, 'write_orbit_csv', False):
            return

        orbit_to_group = {}
        if getattr(self, 'orbit_groups', None) is not None:
            for group in self.orbit_groups.groups:
                for orbit in group.orbits:
                    orbit_to_group[orbit.id] = group

        csv_filename = self.options.instance_name + '.' + self.options.instance_suffix + '.orbits.csv'
        with open(csv_filename, 'w', newline='') as csv_file:
            writer = csv.writer(csv_file, quoting=csv.QUOTE_ALL)
            row_headers = [
                'Orbit',
                'pattern',
                'SQI',
                'qcost',
                'Bit String',
                '# literals',
                'Group',
                'Group Size',
                'Sig',
                'Number sig',
                'Literal sig'
            ]
            row_headers.extend(self.orbit_groups.state_vars)
            for var in self.orbit_groups.state_vars:
                row_headers.extend(["#" + var + "=1", "#" + var + "=0"])
            row_headers.extend(["#forall", "#exists"])

            writer.writerow(row_headers)

            for i in self._last_inference_list:
                orbit = self.orbits[i]
                bit_string = ''.join(orbit.repr_prime.values)
                group = orbit_to_group.get(orbit.id)
                group_id = group.id if group is not None else ''
                pattern = group.pattern if group is not None else ''
                group_size = len(group.orbits) if group is not None else ''
                number_sig = ''.join(str(x) for x in orbit.sig) if orbit is not None else ''
                row = [
                    orbit.id,
                    pattern,
                    str(orbit.quantified_form),
                    orbit.qcost,
                    bit_string,
                    orbit.num_literals,
                    group_id,
                    group_size,
                ]

                
                atom_literals = [lit.rstrip('=') for lit in list(zip(*self.orbit_groups.protocol.atom_sig))[0]]
                var_bit_strings = []


                for var in self.orbit_groups.state_vars:
                    left_atom_num = atom_literals.index(var)
                    right_atom_num = len(atom_literals) - 1 - atom_literals[::-1].index(var)
                    var_bit_string = bit_string[left_atom_num:right_atom_num+1]
                    var_bit_strings.append(var_bit_string)

                lit_sig = ""
                for var, var_bit_string in zip(self.orbit_groups.state_vars, var_bit_strings):
                    if '1' in var_bit_string:
                        lit_sig += var[0] + '1'
                    if '0' in var_bit_string:
                        lit_sig += var[0] + '0'
                
                if orbit.num_exists > 0:
                    row.append(lit_sig)
                else:
                    row.append(number_sig)

                row.append(number_sig)                
                row.append(lit_sig)

                row.extend(var_bit_strings)
                for var_bit_string in var_bit_strings:
                    row.append(var_bit_string.count('1'))
                    row.append(var_bit_string.count('0'))
                
                row.append(orbit.num_forall)
                row.append(orbit.num_exists)

                writer.writerow(row)

    def _print_quantifier_inference(self, inference_list) -> None:
        if self.options.writeQI:
            prime_filename   = self.options.instance_name + '.' + self.options.instance_suffix + '.qpis'
            outF = open(prime_filename, "w")
            for i in inference_list:
                orbit = self.orbits[i]
                outF.write(str(orbit))
            outF.close()
        vprint_step_banner(self.options, f'[QI RESULT]: Quantified Prime Orbits on [{self.options.ivy_filename}: {self.options.size_str}]', 3)
        for i in inference_list:
            orbit = self.orbits[i]
            vprint(self.options, str(orbit), 3)
        vprint(self.options, "\n[QI RESULT]: Quantified Forms Only", 5)
        for i in inference_list:
            orbit = self.orbits[i]
            vprint(self.options, orbit.quantified_form, 5)


    def print_rmin(self) -> None:
        vprint_step_banner(self.options, f'[MIN RESULT]: Minimized Invariants on [{self.options.ivy_filename}: {self.options.size_str}]', 3)
        vprint(self.options, f'[MIN NOTE]: number of minimal solution found: {len(self.optimal_solutions)}', 3)
        vprint(self.options, f'[MIN NOTE]: upper bound: {self.ubound}', 3)
        vprint(self.options, f'[MIN NOTE]: maximum branch and bound depth: {self.bnb_max_depth}', 3)
        vprint(self.options, f'[MIN NOTE]: number of definitions: {len(Rmin.def_lines)}', 3)
        for line in Rmin.def_lines:
            vprint(self.options, line, 3)
        vprint(self.options, f'[MIN NOTE]: number of equality relations: {len(Rmin.eq_lines)}', 3)
        for line in Rmin.eq_lines:
            vprint(self.options, line, 3)
        for (sid, rmin) in enumerate(self.rmin):
            vprint(self.options, f'[MIN NOTE]: Solution {sid} : {rmin.solution}', 3)
            vprint(self.options, f'[MIN NOTE]: solution length: {len(rmin.solution)}', 3)
            for line in rmin.invar_lines:
                vprint(self.options, line, 3)
            vprint(self.options, f'[MIN NOTE]: number of total invariants: {len(rmin.solution) + len(Rmin.def_lines) + len(Rmin.eq_lines)}', 3)
            vprint(self.options, f'[MIN NOTE]: total qCost: {self.ubound + Rmin.def_qcost + Rmin.eq_qcost}', 3)
            vprint(self.options, '\n', 3)

    def set_rmin(self) -> None:
        Rmin.set_definitions_and_eq_relations(self.tran_sys)
        for solution in self.optimal_solutions:
            self.rmin.append(Rmin(solution, self.orbits))

    def write_ivy_files(self) -> None:
        for rmin_id, rmin in enumerate(self.rmin):
            ivy_name = self.options.instance_name + '.' + self.options.instance_suffix + f'.{rmin_id}'+ '.ivy'
            cp_cmd = f'cp {self.options.ivy_filename} {ivy_name}'
            os.system(cp_cmd)
            comment_invar_cmd = f"sed -i '/invariant/s/^/#/' {ivy_name}"
            os.system(comment_invar_cmd) # comment out the existing invariants, including safety property
            ivy_file = open(ivy_name, 'a')
            ivy_file.write('\n')
            invariants = Rmin.def_lines + Rmin.eq_lines + rmin.invar_lines
            for line in invariants:
                ivy_file.write(line+'\n')
            ivy_file.close()

    #------------------------------------------------------------
    # Minimizer: public core methods
    #------------------------------------------------------------
    def reduce_redundant_prime_orbits(self):
        self._remove_definition_prime_orbits_from_pending()
        self._new_level()
        self._reduce()

    def quantifier_inference(self, instantiator: FiniteIvyInstantiator, atoms) -> None:
        from qinference import QInference, QPrime
        
        QInference.setup(atoms, self.tran_sys, instantiator, self.is_dnf)
        vprint_title(self.options, 'quantifier_inference', 5)
        inference_list = self.solution + self.pending
        for orbit_id in inference_list:
            orbit = self.orbits[orbit_id]
            vprint(self.options, str(orbit), 5)
            qinf    = QInference(orbit, self.options, self.is_dnf)
            qclause = qinf.get_qclause()
            orbit.set_quantifier_inference_result(qclause)
            # if self.options.sanity_check:
            #     self.cover.init_quantifier_inference_check_solver_smt(orbit.primes, qclause)
            #     vprint_title(self.options, f'Quantifier Inference: orbit {orbit_id}')
            #     if self.cover.quantifier_inference_check_smt():
            #         vprint(self.options, f'[QI_CHECK RESULT]: PASS')
            #     else:
            #         vprint(self.options, f'[QI_CHECK RESULT]: FAIL')
        # output result
        self._last_inference_list = sorted(inference_list)
        self._print_quantifier_inference(self._last_inference_list)
        self.max_cost = 1 + sum([orbit.qcost for orbit in self.orbits])
        self.ubound   = self.max_cost

    def set_orbit_groups(self, uncurried_protocol : Protocol, state_vars):
        self.orbit_groups = OrbitGroups(self.orbits, uncurried_protocol, state_vars, self.options)
        self.orbit_to_group_id = {}
        for group in self.orbit_groups.groups:
            for orbit in group.orbits:
                self.orbit_to_group_id[orbit.id] = group.id
        if self.options.verbosity >= 5:
            vprint_title(self.options, 'set_orbit_groups', 5)
            vprint(self.options, f'group_count: {len(self.orbit_groups.groups)}', 5)
            for group in self.orbit_groups.groups:
                orbit_ids = sorted([orbit.id for orbit in group.orbits])
                vprint(
                    self.options,
                    f'group {group.id}: size={len(group.orbits)} qcost={group.qcost} sig={group.sig} orbits={orbit_ids}',
                    5,
                )
            mapping = sorted(self.orbit_to_group_id.items())
            vprint(self.options, f'orbit_to_group_id: {mapping}', 5)

    def solve_rmin(self) -> List[str]:
        if self._use_group_bnb():
            self._remove_high_cost_from_pending()
            self.max_cost = 1 + sum([group.qcost for group in self.orbit_groups.groups])
            self.ubound = self.max_cost
        if self.options.all_solutions:
            self._solve_all()
        else:
            self._solve_one()
        self.set_rmin()
        self.print_rmin()
        self.write_ivy_files()
        return True

    def _state_to_readable(self, bit_str, protocol : Protocol):
        """
        Convert a state integer to readable atom assignments.
        
        Args:
            bit_str: Binary string representation of the state
            protocol: Protocol object containing state atoms
        """
        lines = []
        atoms = protocol.state_atoms_fmla 
        
        for i, bit in enumerate(bit_str):
            if i >= len(atoms):
                break
            if bit == '1':  # Only show atoms that are true
                atom_str = str(atoms[i])
                lines.append(f"    {atom_str}")
                
        return '\n'.join(lines) if lines else "    (no atoms set)"

    def _compare_symmetry_quotient(self, sol_id, invariants, protocol : Protocol):
        vprint(self.options, f'Minimization check for Solution {sol_id}')
        self.cover.init_minimization_check_solver(invariants, protocol)
        (result, values)  = self.cover.get_minimization_check_minterm()
        model_repr_states = set()
        model_bit_states = set()
        model_match = True
        while result:
            repr_int = int(''.join(values), 2)
            for nvalues in protocol.all_permutations(values[:protocol.state_atom_num]): # only permute the mutable part
                nvalues += values[protocol.state_atom_num:]
                repr_int = min(int(''.join(nvalues), 2), repr_int)
                self.cover.block_minimization_check_minterm(nvalues)
            bit_str = '{0:0{1}b}'.format(repr_int, protocol.atom_num)[:protocol.state_atom_num]
            if not bit_str in protocol.bit_repr_states and not bit_str in model_bit_states:
                vprint(self.options, f'Found a representative state in Rmin not in reachability: decimal: {repr_int}, binary: {bit_str}', 1)
                vprint(self.options, f'State:\n{self._state_to_readable(bit_str, protocol)}', 2)
                model_match = False
                if self.options.early_terminate_reach:
                    vprint(self.options, f'[MIN_CHECK RESULT]: FAIL')
                    return model_match
            model_repr_states.add(repr_int)
            model_bit_states.add(bit_str)
            (result, values) = self.cover.get_minimization_check_minterm()

        difference = protocol.repr_states - model_repr_states
        if len(difference) > 0:
            vprint(self.options, 'Representatitive states in reachability not in Rmin', 1)
            for d in difference:
                bit_str = '{0:0{1}b}'.format(d, protocol.atom_num)[:protocol.state_atom_num]
                if bit_str not in model_bit_states:
                    vprint(self.options, f'{hex(d)}', 1)
                    vprint(self.options, f'  Binary: {bit_str}', 2)
                    vprint(self.options, f'  State:\n{self._state_to_readable(bit_str, protocol)}', 2)
                    model_match = False
        if model_match:
            vprint(self.options, f'[MIN_CHECK RESULT]: PASS')
        else:
            vprint(self.options, f'[MIN_CHECK RESULT]: FAIL')
        return model_match 

    def _equivalence_checking(self, sol_id, invariants, protocol : Protocol) -> bool:
        vprint(self.options, f'Minimization check for Solution {sol_id}')
        self.cover.init_minimization_check_solver(invariants, protocol)
        (result, _)  = self.cover.get_minimization_check_minterm()
        if result: # Non-equal
            vprint(self.options, f'[MIN_CHECK RESULT]: FAIL')
            return False
        else:
            vprint(self.options, f'[MIN_CHECK RESULT]: PASS')
            return True

    def minimization_check(self, protocol : Protocol):
        self.cover.init_minimization_check_clauses()
        result = True
        for sol_id, solution in enumerate(self.optimal_solutions):
            invariants = [self.orbits[orbit_id].quantified_form for orbit_id in solution]
            if self.options.forward_mode == ForwardMode.Sym_DFS:
                result = result and self._compare_symmetry_quotient(sol_id, invariants, protocol)
            else:
                result = result and self._equivalence_checking(sol_id, invariants, protocol)
        return result