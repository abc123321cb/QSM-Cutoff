import repycudd
from typing import Type, Set, List, Dict
from util import QrmOptions
from transition_system import TransitionSystem
from finite_ivy_instantiate import FiniteIvyInstantiator
from ivy import ivy_logic as il
from ivy import logic as lg
from ivy import ivy_actions as ia
from ivy import ivy_logic_utils as ilu
from itertools import product as product
from verbose import *

class FormulaInitializer():
    def __init__(self, tran_sys : TransitionSystem, instantiator : FiniteIvyInstantiator, options : QrmOptions):
        self.options      : QrmOptions            = options
        self.tran_sys     : TransitionSystem      = tran_sys
        self.instantiator : FiniteIvyInstantiator = instantiator
        self.curr_atoms      = [] 
        self.next_atoms      = []
        self.immutable_atoms = []
        self.curr2next       = {}
        self.curr_axiom_fmla = None
        self.init_action_fmlas     = {}
        self.exported_action_fmlas = {}

        self._init_atoms()
        self._init_axiom_formulas()
        self._init_action_formulas()

    def _get_action_formula_recur(self, action, is_init=True, params=set()):
        if isinstance(action, ia.Sequence):
           action_fmlas = [self._get_action_formula_recur(a, is_init, params) for a in action.args] 
           return il.And(*action_fmlas)
        elif isinstance(action, ia.AssertAction) or isinstance(action, ia.AssumeAction):
            assert(hasattr(action, 'formula'))
            return il.close_formula(action.formula)
        elif isinstance(action, ia.AssignAction):
            lhs = action.args[0]
            rhs = action.args[1]
            lhs_vars = ilu.used_variables_ast(lhs)            
            if is_init:
                assert(len(params) == 0)
                fmla = lhs
                if rhs == il.Or():
                    fmla =  il.Not(lhs)
                elif rhs != il.Or() and rhs != il.And():
                    fmla = il.Equals(lhs,rhs)
                if len(lhs_vars):
                    fmla = il.ForAll(lhs_vars, fmla)
                return fmla
            else:
                consts    = ilu.used_constants_ast(lhs) 
                consts    = consts.intersection(params)
                var2const = {il.Variable(f'{const.sort.name.upper()}{i}', const.sort):const for i,const in enumerate(consts)}
                const2var = {c:v for v,c in var2const.items()}
                lhs       = il.substitute(lhs, const2var)
                if_fmla   = il.And(*[il.Equals(v,c) for v,c in var2const.items()])
                then_fmla = rhs
                else_fmla = lhs 
                next_lhs  = il.substitute(lhs, self.curr2next)
                fmla = il.Equals(next_lhs, il.Ite(if_fmla, then_fmla, else_fmla))
                all_vars = list(lhs_vars) + list(var2const.keys())
                if len(all_vars) > 0:
                    fmla = il.ForAll(all_vars, fmla)
                return fmla 
        elif isinstance(action, ia.HavocAction):
            lhs = action.args[0]
            lhs_vars = ilu.used_variables_ast(lhs)            
            if is_init:
                assert(len(params) == 0)
                return il.And()
            else:
                consts    = ilu.used_constants_ast(lhs) 
                consts    = consts.intersection(params)
                var2const = {il.Variable(f'{const.sort.name.upper()}{i}', const.sort):const for i,const in enumerate(consts)}
                const2var = {c:v for v,c in var2const.items()}
                lhs       = il.substitute(lhs, const2var)
                next_lhs  = il.substitute(lhs, self.curr2next)
                all_vars  = list(lhs_vars) + list(var2const.keys())
                fmlas = []
                for v,c in var2const.items():
                    fmla = il.Implies(next_lhs, il.Or(lhs, il.Equals(v,c)))
                    fmla = il.ForAll(all_vars, fmla) if len(all_vars) > 0 else fmla
                    fmlas.append(fmla)
                    fmla = il.Implies(lhs, il.Or(next_lhs, il.Equals(v,c)))
                    fmla = il.ForAll(all_vars, fmla) if len(all_vars) > 0 else fmla
                    fmlas.append(fmla)
                return il.And(*fmlas)
        else:
            assert(0)

    def _get_action_assign_symbols(self, action):
        if isinstance(action, ia.Sequence):
            lhs = set() 
            for a in action.args:
                lhs.update(self._get_action_assign_symbols(a))
            return lhs
        elif isinstance(action, ia.AssignAction):
            return ilu.used_symbols_ast(action.args[0])
        elif isinstance(action, ia.HavocAction):
            return ilu.used_symbols_ast(action.args[0])
        else:
            return set()

    def _update_action_non_changing_fmlas(self, action, action_fmla):
        assign_symbols = self._get_action_assign_symbols(action)
        fmlas = [action_fmla]
        for state_symbol in self.tran_sys.state_symbols:
            if state_symbol not in assign_symbols and state_symbol not in self.tran_sys.definitions: 
                state_var   = state_symbol
                output_sort = state_symbol.sort
                argvars     = []
                if il.is_function_sort(state_symbol.sort):
                    argvars     = [il.Variable(f'{sort.name.upper()}{i}', sort) for i, sort in enumerate(state_symbol.sort.dom)] 
                    state_var   = il.App(state_symbol, *argvars)
                    output_sort = state_symbol.sort.rng
                if il.is_boolean_sort(output_sort):
                    next_state_var = il.substitute(state_var, self.curr2next)
                    fmla = il.Equals(next_state_var, state_var)
                    if len(argvars) > 0:
                        fmla = il.ForAll(argvars, fmla) 
                    fmlas.append(fmla)
                else:
                    for const in output_sort.constructors:
                        eq_var   = il.Equals(state_var, const)
                        next_eq_var = il.substitute(eq_var, self.curr2next)
                        fmla = il.Equals(next_eq_var, eq_var)
                        if len(argvars) > 0:
                            fmla = il.ForAll(argvars, fmla)
                        fmlas.append(fmla)
        return il.And(*fmlas) 

    def _instantiate_params(self, action_fmla, params):
        action_fmlas = []
        elems = []
        for param in params:
            elems.append(param.sort.constructors)
        inst_params = list(product(*elems))
        for inst_param in inst_params: 
            subst = {p:i for p,i in zip(params,inst_param)}
            fmla  = il.substitute(action_fmla, subst)
            action_fmlas.append(fmla)
        return action_fmlas

    def _init_atoms(self):
        self.curr2next = {symb:il.Symbol('next_'+symb.name, symb.sort) for symb in self.tran_sys.state_symbols} 
        self.curr_atoms      = self.instantiator.protocol_state_atoms_fmlas
        self.immutable_atoms = self.instantiator.protocol_interpreted_atoms_fmlas
        for atom in self.curr_atoms:
            next_atom = il.substitute(atom, self.curr2next)
            self.next_atoms.append(next_atom)

    def _init_axiom_formulas(self):
        def_eqs = []
        for def_lhs, def_rhs in self.instantiator.instantiated_def_map.items():
            def_eqs.append(il.Equals(def_lhs, def_rhs))
        axiom_fmlas = def_eqs + self.instantiator.dep_axioms_fmla
        if self.instantiator.axiom_fmla != None:
            axiom_fmlas.append(self.instantiator.axiom_fmla)
        lhs_set = {} 
        for atom in self.instantiator.protocol_atoms_fmlas:
            if il.is_eq(atom):
                lhs = atom.args[0]
                if str(lhs) not in lhs_set:
                    lhs_set[str(lhs)] = []
                lhs_set[str(lhs)].append(atom)
        for eq_atoms in lhs_set.values():
            at_least_one = il.Or(*eq_atoms) 
            axiom_fmlas.append(at_least_one)
            for id0 in range(len(eq_atoms)-1):
                for id1 in range(id0+1, len(eq_atoms)):
                    atom0 = eq_atoms[id0]
                    atom1 = eq_atoms[id1]
                    at_most_one = il.Or(*[il.Not(atom0), il.Not(atom1)])
                    axiom_fmlas.append(at_most_one)
        self.curr_axiom_fmla = il.And(*axiom_fmlas)

    def _init_action_formulas(self):
        self.init_action_fmlas = {}
        self.exported_action_fmlas = {}
        for action_symbol, action in self.tran_sys.init_actions.items():
            action_fmla = self._get_action_formula_recur(action, is_init=True, params=set(action_symbol.args))
            action_fmla = self.instantiator.instantiate_quantifier(action_fmla)
            self.init_action_fmlas[action_symbol] = action_fmla
        for action_symbol, action in self.tran_sys.exported_actions.items():
            action_fmla   = self._get_action_formula_recur(action, is_init=False, params=set(action_symbol.args))
            action_fmla   = self._update_action_non_changing_fmlas(action, action_fmla)
            action_fmlas  = self._instantiate_params(action_fmla, action_symbol.args)
            action_fmlas  = [self.instantiator.instantiate_quantifier(f) for f in action_fmlas]
            self.exported_action_fmlas[action_symbol] = action_fmlas

class BddNode():
    def __init__(self, name, cudd_node):
        self.name = name 
        self.cudd_node = cudd_node
        self.cudd_id   = cudd_node.NodeReadIndex()

    def __str__(self):
        return self.name

class Bdd():
    def __init__(self, options: QrmOptions, fmla : FormulaInitializer):
        self.options      = options
        self.ddmanager    = repycudd.DdManager()
        self.atom_nodes : Dict[str, BddNode]  = {}
        self.bdd_nodes  : Dict[str, BddNode]  = {}
        self.cudd_id2state_atom_id : Dict[int, int] = {}
        self.cudd_id2immut_atom_id : Dict[int, int] = {}
        self.init_action            = None
        self.curr_axiom             = None
        self.next_axiom             = None
        self.exported_actions       = {}
        self.curr_atom_cube         = None
        self.next_atom_cube         = None
        self.all_but_curr_atom_cube = None
        self.curr_DdArray           = None
        self.next_DdArray           = None
        self.state_atom_num         = 0

        self._initialize(fmla)

    def canonicalize_formula(self, fmla):
        args = [self.canonicalize_formula(a) for a in fmla.args]
        if isinstance(fmla, il.Or): 
            args = sorted(args, key=lambda x: str(x))
            fmla = il.Or(*args)
        elif isinstance(fmla, il.And):
            args = sorted(args, key=lambda x: str(x))
            fmla = il.And(*args)
        elif isinstance(fmla, il.Implies):
            assert(len(args) == 2)
            fmla = il.Implies(args[0],args[1]) 
        elif isinstance(fmla, il.Ite):
            assert(len(args) == 3)
            fmla = il.Ite(args[0], args[1], args[2]) 
        elif isinstance(fmla, lg.Eq):
            assert(len(args) == 2)
            args = sorted(args, key=lambda x: str(x))
            fmla = il.Equals(args[0], args[1]) 
        return fmla

    def _get_bdd_node(self, fmla):
        if str(fmla) in self.atom_nodes:
            return self.atom_nodes[str(fmla)].cudd_node
        else:
            if isinstance(fmla, il.Not):
                node = self._get_bdd_node(fmla.args[0])
                return self.ddmanager.Not(node)
            if len(fmla.args) == 0:
                assert( isinstance(fmla, il.And) or isinstance(fmla, il.Or) )
                return self.ddmanager.One() if isinstance(fmla, il.And) else self.ddmanager.Zero()
            elif len(fmla.args) == 1:
                assert( isinstance(fmla, il.And) or isinstance(fmla, il.Or) )
                return self._get_bdd_node(fmla.args[0])
            assert(len(fmla.args) > 1) 
            fmla = self.canonicalize_formula(fmla)
            if str(fmla) in self.bdd_nodes:
                return self.bdd_nodes[str(fmla)].cudd_node
            args = [self._get_bdd_node(arg) for arg in fmla.args]
            if isinstance(fmla, il.And):
                res = args[0]
                for a in args[1:]:
                    res = self.ddmanager.And(a, res)
            elif isinstance(fmla, il.Or):
                res = args[0]
                for a in args[1:]:
                    res = self.ddmanager.Or(res,a)
            elif isinstance(fmla, il.Implies):
                assert(len(args) == 2)
                res = self.ddmanager.Or(self.ddmanager.Not(args[0]), args[1])
            elif isinstance(fmla, lg.Eq):
                assert(len(args) == 2)
                res = self.ddmanager.Xnor(args[0], args[1])
            elif isinstance(fmla, il.Ite):
                assert(len(args) == 3)
                res = self.ddmanager.Ite(fmla.cond, fmla.t_then, fmla.t_else)
            else:
                assert(0)
            bdd_node  = BddNode(str(fmla), res)
            self.bdd_nodes[str(fmla)] = bdd_node
            return res

    def _get_atoms_bdd_cube(self, atoms):
        indices = repycudd.IntArray(len(atoms))
        for i, atom in enumerate(atoms):
            indices[i] = self.atom_nodes[str(atom)].cudd_id
        cube = self.ddmanager.IndicesToCube(indices, len(atoms))
        return cube

    def _init_atoms(self, curr_atoms, next_atoms, immutable_atoms):
        vprint(self.options, 'building bdd for atoms', 5)
        assert(len(curr_atoms) == len(next_atoms))
        # declare curr and next atom consecutively in order is critical! 
        for catom, natom in zip(curr_atoms, next_atoms):
            cudd_node = self.ddmanager.NewVarAtLevel(0)
            bdd_node  = BddNode(str(catom), cudd_node)
            self.atom_nodes[str(catom)] = bdd_node
            cudd_node = self.ddmanager.NewVarAtLevel(0)
            bdd_node  = BddNode(str(natom), cudd_node)
            self.atom_nodes[str(natom)] = bdd_node
        for atom in immutable_atoms:
            cudd_node = self.ddmanager.NewVarAtLevel(0)
            bdd_node  = BddNode(str(atom), cudd_node)
            self.atom_nodes[str(atom)] = bdd_node
        for atom_id, atom in enumerate(curr_atoms):
            cudd_id = self.atom_nodes[str(atom)].cudd_id
            self.cudd_id2state_atom_id[cudd_id] = atom_id
        for atom_id, atom in enumerate(immutable_atoms):
            cudd_id = self.atom_nodes[str(atom)].cudd_id
            self.cudd_id2immut_atom_id[cudd_id] = atom_id

    def _init_initial_action(self, init_action_fmlas, curr_axiom_fmla):
        vprint(self.options, 'building bdd for initial action', 5)
        assert(len(init_action_fmlas) == 1) 
        init_fmla = list(init_action_fmlas.values())[0]
        init_fmla = il.And(*[init_fmla, curr_axiom_fmla])
        self.init_action = self._get_bdd_node(init_fmla) 

    def _init_axioms(self, curr_axiom_fmla):
        vprint(self.options, 'building bdd for axioms', 5)
        self.curr_axiom = self._get_bdd_node(curr_axiom_fmla)

    def _init_actions(self, exported_action_fmlas):
        vprint(self.options, 'building bdd for actions', 5)
        for action_symbol, action_fmlas in exported_action_fmlas.items():
            vprint(self.options, f'building bdd for action: {str(action_symbol)}', 5)
            action_bdds = [self._get_bdd_node(f) for f in action_fmlas]
            self.exported_actions[str(action_symbol)] = action_bdds

    def _init_abstraction(self, curr_atoms, next_atoms, immutable_atoms):
        vprint(self.options, 'building bdd for abstractions', 5)
        self.curr_atom_cube = self._get_atoms_bdd_cube(curr_atoms)
        self.next_atom_cube = self._get_atoms_bdd_cube(next_atoms)
        self.all_but_curr_atom_cube = self._get_atoms_bdd_cube(next_atoms + immutable_atoms)
        assert(len(curr_atoms) == len(next_atoms))
        self.state_atom_num = len(curr_atoms)
        self.curr_DdArray   = repycudd.DdArray(self.ddmanager, self.state_atom_num)
        self.next_DdArray   = repycudd.DdArray(self.ddmanager, self.state_atom_num)
        for atom in curr_atoms:
            node = self.atom_nodes[str(atom)].cudd_node
            self.curr_DdArray.Push(node)
        for atom in next_atoms:
            node = self.atom_nodes[str(atom)].cudd_node
            self.next_DdArray.Push(node)

    def _initialize(self, fmla : FormulaInitializer):
        self._init_atoms(fmla.curr_atoms, fmla.next_atoms, fmla.immutable_atoms)
        self._init_initial_action(fmla.init_action_fmlas, fmla.curr_axiom_fmla)
        self._init_axioms(fmla.curr_axiom_fmla)
        self._init_actions(fmla.exported_action_fmlas)
        self._init_abstraction(fmla.curr_atoms, fmla.next_atoms, fmla.immutable_atoms)

    def clean(self):
        del self.curr_DdArray
        del self.next_DdArray
        self.curr_DdArray = None
        self.next_DdArray = None

