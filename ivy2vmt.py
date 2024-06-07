import sys

from ivy import ivy_logic
from ivy import ivy_utils as iu
from ivy import ivy_actions as ia
from ivy import logic as lg
from ivy import ivy_printer as ip

from ivy.ivy_logic import UninterpretedSort, UnionSort
from ivy import ivy_logic_utils as lut
from ivy import ivy_art
from ivy import ivy_interp as itp
from ivy import logic as lg
from ivy import logic_util as lgu
from ivy import ivy_init
from ivy import ivy_module as im
from ivy import ivy_utils as utl
from ivy import ivy_compiler
from ivy import ivy_isolate
from ivy import ivy_ast

from verbose import *

for cls in [lg.Eq, lg.Not, lg.And, lg.Or, lg.Implies, lg.Iff, lg.Ite, lg.ForAll, lg.Exists,
            lg.Apply, lg.Var, lg.Const, lg.Lambda, lg.NamedBinder]:
    if hasattr(cls,'__vmt__'):
        cls.__str__ = cls.__vmt__

prefix = '__'

class VmtWriter():
    def __init__(self, mod):
        self.mod = mod

        # data
        self.definitions  = [] 
        self.sort2size    = {}
        self.all_symbols  = set()
        self.new_symbols  = set()

        # transistions
        self.prev_symbols = set()
        self.next_symbols = set()
        self.next2prev    = {}
        self.prev2next    = {}
        self.updated_symbols = set()
        self.global_symbols  = set()
        self.actions         = set()

        # print
        self.symbol_line    = {}
        self.vmt_signature  = {}
        self.defn_labels    = []
        self.vmt_file       = None

        self._initialize()

    def _init_definitions(self):
        for update in self.mod.updates:
            if type(update) == ia.DerivedUpdate:
                defn = update.defn
                self.definitions.append(defn)
            self.mod.definitions = []

    def _init_sorts(self):
        for name,sort in ivy_logic.sig.sorts.items():
            if name == 'bool':
                continue
            if not isinstance(sort,UninterpretedSort):
                raise iu.IvyError(None,f'Cannot handle uninterprested sort {sort}')
            self.sort2size[sort] = 0
            self.symbol_line[str(sort)]   = f'(declare-sort {name} 0)\n'

    def _set_symbol_line(self, sym, addPre):   
        sort = sym.sort
        name = str(sym)
        prefix = '(declare-fun '
        suffix = ' ('
        if sort.dom:
            suffix += ' '.join(f'{sort}' for sort in sort.dom)
        suffix += ')'
        if not sort.is_relational():
            suffix += f' {sort.rng}'
        else:
            suffix += ' Bool'
        suffix += ')'
        self.symbol_line[name] = prefix + name + suffix + '\n'
        
        if addPre:
            prev_sym   = self.next2prev[sym]
            prev_name  = str(prev_sym)
            prev2next  = '(define-fun ' + '.' + name + ' ('
            if sort.dom:
                prev2next += ' '.join(f'(V{id} {sort})' for id,sort in enumerate(sort.dom))
            prev2next += ')'
            if not sort.is_relational():
                prev2next += f' {sort.rng}'
            else:
                prev2next += ' Bool'
            prev2next += ' (! '
            if sort.dom:
                prev2next += '(' + prev_name + ' '
                prev2next += ' '.join(f'V{id}' for id,_ in enumerate(sort.dom)) + ')'
            else:
                prev2next += prev_name
            prev2next += ' :next ' + name + '))'
            self.symbol_line[prev_name] = prefix + prev_name + suffix + '\n'
            self.symbol_line[prev_name+name] = prev2next + '\n'

    def _init_symbols(self):
        symbol_list  = list(ivy_logic.sig.symbols.values())
        symbol_list += [defn.defines() for defn in self.definitions]
        for sym in symbol_list:
            if sym in self.all_symbols:
                continue
            if isinstance(sym.sort,UnionSort):
                raise iu.IvyError(None,f'Cannot handle unionsort symbol {sym}')
            
            prev_sym = sym.prefix(prefix)
            next_sym = sym
            self.prev_symbols.add(prev_sym)
            self.next_symbols.add(next_sym)
            self.prev2next[prev_sym] = next_sym
            self.next2prev[next_sym] = prev_sym
            self.all_symbols.add(prev_sym)
            self.all_symbols.add(next_sym)
            self._set_symbol_line(sym, True)
    
    def _set_new_symbols_line(self, formula):
        cons = lgu.used_constants(formula)
        for c in cons:
            if c not in self.all_symbols:
                self._set_symbol_line(c, False)
                self.new_symbols.add(c)
                self.all_symbols.add(c)

    def _init_definition_labels(self):
        for defn in self.definitions:
            sym   = defn.defines()
            label = 'def_' + str(sym)
            lhs   = defn.lhs()
            rhs   = defn.rhs()
            self._set_new_symbols_line(rhs)

            arg2vargs = {}
            vargs     = []
            if isinstance(lhs, lg.Apply):
                for arg in lhs.terms:
                    name = 'V' + str(len(vargs))
                    varg = lg.Var(name, arg.sort)
                    arg2vargs[arg] = varg
                    vargs.append(varg)
                lhs = lgu.substitute(lhs, arg2vargs)
                rhs = lgu.substitute(rhs, arg2vargs)
            fmla = lg.Eq(lhs, rhs)
            if len(vargs) != 0:
                fmla = lg.ForAll(vargs, fmla)
            res = (fmla, label, 'definition', str(sym))
            self.vmt_signature[label] = res
            self.defn_labels.append(label)
        
            sym   = lgu.substitute(sym, self.next2prev)
            label = 'def_' + str(sym)
            self.defn_labels.append(label)
            prev_fmla = lgu.substitute(fmla, self.next2prev)
            self.vmt_signature[label] = (prev_fmla, label, 'definition', str(sym))

    def _get_formula(self, clauses):
        cl = lut.and_clauses(clauses)
        return cl.to_formula()

    def _init_conjectures(self):
        fmlas = []
        for conj in self.mod.labeled_conjs:
            fmlas.append(conj.formula)
        clauses = lut.Clauses(fmlas)
        fmla    = self._get_formula(clauses)
        prev_fmla = lgu.substitute(fmla, self.next2prev)
        self._set_new_symbols_line(prev_fmla)
        self.vmt_signature['$prop'] = (prev_fmla, 'prop', 'invar-property', '0')

    def _init_axioms(self):
        fmlas = [lf.formula for lf in self.mod.labeled_axioms]
        clauses = lut.Clauses(fmlas)
        fmla = self._get_formula(clauses)
        self._set_new_symbols_line(fmla)
        self.vmt_signature['$axiom'] = (fmla, 'axiom', 'axiom', 'true')

    def _init_initial_state(self):
        init_clauses = []
        for name,action in self.mod.initializers:
            ag = ivy_art.AnalysisGraph(initializer=lambda x:None)
            history = ag.get_history(ag.states[0])
            post = lut.and_clauses(history.post)
            init_clauses.append(post)
        clauses = lut.and_clauses(*init_clauses)
        fmla      = self._get_formula(clauses)
        prev_fmla = lgu.substitute(fmla, self.next2prev)
        self._set_new_symbols_line(prev_fmla)
        self.vmt_signature['$init'] = (prev_fmla, 'init', 'init', 'true')

    def _get_action_transition_formula(self, formula, update_vars):
        self.updated_symbols.update(update_vars)
        symbols = lgu.used_constants(formula)
        subs    = dict()
        evars   = []
        for sym in symbols:
            if sym in self.next_symbols:
                if sym not in update_vars:
                    subs[sym] = self.next2prev[sym] # does not update
            elif sym not in self.prev_symbols: # not in next_symbols or prev_symbols
                if (not sym.sort.dom) and (sym.sort != lg.Boolean):
                    vname = 'V'+ sym.name
                    qv = lg.Var(vname, sym.sort)
                    subs[sym] = qv
                    evars.append(qv)
        action = formula
        if len(subs) != 0:
            action = lgu.substitute(formula, subs)
        if len(evars) != 0:
            action = lg.Exists(evars, action)
        return action

    def _init_actions(self):
        for name, action in self.mod.actions.items():
            ag = ivy_art.AnalysisGraph()
            pre = itp.State()
            pre.clauses = lut.true_clauses()
            post = ag.execute(action, pre)
            history = ag.get_history(post)
            clauses = lut.and_clauses(history.post)
            fmla = self._get_formula(clauses)
            
            update      = action.update(pre.domain,pre.in_scope)
            update_vars = set(update[0])
            trans_fmla = self._get_action_transition_formula(fmla, update_vars)
            self._set_new_symbols_line(trans_fmla)
            
            actname = 'action_' + name
            self.actions.add(actname)
            self.vmt_signature[actname] = (trans_fmla, actname, 'action', name)

    def _set_global_line(self, sym, key):
        sort = sym.sort
        name = str(sym)
        
        prev2next =  '(define-fun ' +  '.' + name + ' ('
        if sort.dom:
            prev2next += ' '.join(f'(V{id} {sort})' for id,sort in enumerate(sort.dom))
        prev2next += ')'
        if not sort.is_relational():
            prev2next += f' {sort.rng}'
        else:
            prev2next += ' Bool'
        prev2next += ' (! '
        if sort.dom:
            prev2next += '(' + name + ' '
            prev2next += ' '.join(f'V{id}' for id,_ in enumerate(sort.dom)) + ')'
        else:
            prev2next += name
        prev2next += ' :global true))'
        self.symbol_line[key] = prev2next + '\n'

    def _init_global_symbols(self):
        for next_sym in self.next_symbols:
            if next_sym not in self.updated_symbols:
                self.global_symbols.add(next_sym)
        subs = {}
        for next_sym in self.global_symbols:
            prev_sym = self.next2prev[next_sym]
            subs[prev_sym] = next_sym
            def_label = 'def_' + str(prev_sym)
            if def_label in self.defn_labels:
                self.defn_labels.remove(def_label)
            self.prev_symbols.remove(prev_sym)
            self.symbol_line.pop(str(prev_sym))
            self._set_global_line(next_sym, str(prev_sym)+str(next_sym))
        if len(subs) != 0:
            for k, v in self.vmt_signature.items():
                fmla, name, suffix, value = v
                fmla = lgu.substitute(fmla, subs)
                self.vmt_signature[k] = (fmla, name, suffix, value)

    def _initialize(self):
        with self.mod.theory_context():
            self._init_definitions()
            self._init_sorts()
            self._init_symbols()
            self._init_definition_labels()
            self._init_conjectures()
            self._init_axioms()
            self._init_initial_state()
            self._init_actions()
            self._init_global_symbols()

    def _get_vmt_line(self, label):
        fmla, name, annot, value = self.vmt_signature[label]
        if annot != '': # has annotation
            line = '(define-fun .' + name + ' () Bool (! \n'
            line += ' (let (($v ' + str(fmla)
            line += '\n ))\n (and $v))'
            line += '\n :' + annot + ' ' + value + '))\n'
        else: # no annotation, value is the prefix
            line = '(define-fun ' + value + ' \n '
            line += str(fmla) + '\n)\n'
        return line 

    def _write_sorts(self):
        for sort in sorted(self.sort2size.keys(), key=lambda v: str(v)):
            line = self.symbol_line[str(sort)]
            self.vmt_file.write(line)
        self.vmt_file.write('\n')

    def _write_sort_size(self):
        for sort, size in sorted(self.sort2size.items(), key=lambda v: str(v)):
            name = str(sort)
            line = f'(define-fun .{name} ((S {name})) {name} (! S :sort {size}))\n'
            self.vmt_file.write(line)
        self.vmt_file.write('\n')

    def _write_prev_symbols(self):
        for prev_sym in sorted(self.prev_symbols, key=lambda v: str(v)):
            line = self.symbol_line[str(prev_sym)]
            self.vmt_file.write(line)
        self.vmt_file.write('\n')

    def _write_next_symbols(self):
        for prev_sym in sorted(self.prev_symbols, key=lambda v: str(v)):
            next_sym = self.prev2next[prev_sym]
            line = self.symbol_line[str(next_sym)]
            self.vmt_file.write(line)
        self.vmt_file.write('\n')

    def _write_prev2next(self):
        for prev_sym in sorted(self.prev_symbols, key=lambda v: str(v)):
            next_sym = self.prev2next[prev_sym]
            line = self.symbol_line[str(prev_sym)+str(next_sym)]
            self.vmt_file.write(line)
        self.vmt_file.write('\n')

    def _write_global_symbols(self):
        for sym in sorted(self.global_symbols, key=lambda v: str(v)):
            line = self.symbol_line[str(sym)]
            self.vmt_file.write(line)
        self.vmt_file.write('\n')

        for next_sym in sorted(self.global_symbols, key=lambda v: str(v)):
            prev_sym = self.next2prev[next_sym]
            line = self.symbol_line[str(prev_sym)+str(next_sym)]
            self.vmt_file.write(line)
        self.vmt_file.write('\n')

    def _write_new_symbols(self):
        for sym in sorted(self.new_symbols, key=lambda v: str(v)):
            line = self.symbol_line[str(sym)]
            self.vmt_file.write(line)
        self.vmt_file.write('\n')

    def _write_definitions(self):
        for label in sorted(self.defn_labels, key=lambda v: str(v)):
            line = self._get_vmt_line(label)
            self.vmt_file.write(line)
            self.vmt_file.write('\n')

    def _write_properties(self):
        line = self._get_vmt_line('$prop')
        self.vmt_file.write(line)
        self.vmt_file.write('\n')

    def _write_axioms(self):
        line = self._get_vmt_line('$axiom')
        self.vmt_file.write(line)
        self.vmt_file.write('\n')

    def _write_init(self):
        line = self._get_vmt_line('$init')
        self.vmt_file.write(line)
        self.vmt_file.write('\n')

    def _write_actions(self):
        for action in sorted(self.actions, key=lambda v: str(v)):
            line = self._get_vmt_line(action)
            self.vmt_file.write(line)
            self.vmt_file.write('\n')

    def write(self, vmt_filename):
        self.vmt_file = open(vmt_filename, 'w')
        self._write_sorts()
        self._write_sort_size()
        self._write_prev_symbols()
        self._write_next_symbols()
        self._write_prev2next()
        if len(self.global_symbols) != 0:
            self._write_global_symbols()
        if len(self.new_symbols) != 0:
            self._write_new_symbols()
        self._write_definitions()
        self._write_properties()
        if len(self.mod.labeled_axioms) != 0:
            self._write_axioms()
        self._write_init()
        self._write_actions()
        self.vmt_file.close()

def print_isolate(vmt_filename):
    temporals = [p for p in im.module.labeled_props if p.temporal]
    mod = im.module
    if temporals:
        if len(temporals) > 1:
            raise iu.IvyError(None,'multiple temporal properties in an isolate not supported yet')
        from ivy.ivy_l2s import l2s
        l2s(mod, temporals[0])
        mod.concept_spaces = []
        mod.update_conjs()
    vmt_writer = VmtWriter(mod)
    vmt_writer.write(vmt_filename)
    with im.module.theory_context():
        pass
        return

def print_module(options, vmt_filename):
    isolates = sorted(list(im.module.isolates))
    done_isolates = 0
    for isolate in isolates:
        if isolate != None and isolate in im.module.isolates:
            idef = im.module.isolates[isolate]
            if len(idef.verified()) == 0 or isinstance(idef,ivy_ast.TrustedIsolateDef):
                continue # skip if nothing to verify
        if isolate:
            vprint(options, f'\nPrinting isolate {isolate}:', 5)
        if done_isolates >= 1:
            raise iu.IvyError(None,"Expected exactly one isolate, got %s" % len(isolates))
        with im.module.copy():
            ivy_isolate.create_isolate(isolate) # ,ext='ext'
            print_isolate(vmt_filename)
            done_isolates += 1

def compile_ivy2vmt(options, ivy_filename, vmt_filename):
    import signal
    signal.signal(signal.SIGINT,signal.SIG_DFL)
    from ivy import ivy_alpha
    ivy_alpha.test_bottom = False # this prevents a useless SAT check
    ivy_init.read_params()
    with im.Module():
        with utl.ErrorPrinter():
            ivy_init.source_file(ivy_filename,ivy_init.open_read(ivy_filename),create_isolate=False)
            print_module(options, vmt_filename)
    vprint (options, 'OK', 5)
    import sys
    sys.stdout.flush()