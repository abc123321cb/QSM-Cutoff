import datetime
import tracemalloc
from verbose import *
from enum import Enum
UseMC = Enum('UseMC', ['sat', 'mc'])
PrimeGen = Enum('PrimeGen', ['ilp', 'binary', 'enumerate'])

class QrmFail(Exception):
    pass

class QrmOptions():
    def __init__(self) -> None:
        self.verbosity  = 0
        self.instance_name = ''
        self.ivy_filename  = ''
        self.size_str      = ''
        self.sizes         = {} # sort name to size
        self.instance_suffix = ''
        self.flow_mode     = 1
        self.useMC = UseMC.sat
        self.prime_gen = PrimeGen.ilp
        self.readReach         = False
        self.early_terminate_reach = False
        self.sanity_check      = False
        self.writeReach        = False
        self.writePrime        = False
        self.writeQI           = False
        self.writeLog          = False
        self.log_name          = ''
        self.log_fout          = None
        self.all_solutions     = True 
        self.merge_suborbits   = True 
        self.convergence_check = False 
        self.ivy_to            = 120 
        self.qrm_to            = 36000 
        self.time_start        = None
        self.time_stamp        = None
        self.python_include_path = '/usr/include/python3.12'

    def get_new_size_copy(self, new_size_str):
        options = QrmOptions()
        options.verbosity = self.verbosity
        options.instance_name =  self.instance_name
        options.ivy_filename  =  self.ivy_filename 
        options.set_sizes(new_size_str)
        options.writeReach   = True 
        options.writeLog     = self.writeLog 
        options.log_name     = self.log_name
        options.log_fout     = self.log_fout
        options.time_start     = self.time_start 
        options.time_stamp     = self.time_stamp 
        return options

    def set_files_name(self, ivy_name):
        self.ivy_filename  = ivy_name
        self.instance_name = ivy_name.split('.')[0]

    def open_log(self) -> None:
        assert(self.writeLog)
        self.log_fout = open(self.log_name, 'w')

    def append_log(self) -> None:
        assert(self.writeLog)
        self.log_fout = open(self.log_name, 'a')

    def write_log(self, lines) -> None:
        self.log_fout.write(lines)
        self.log_fout.flush()

    def close_log_if_exists(self) -> None:
        if self.writeLog and self.log_fout != None:
            self.log_fout.close()

    def append_log_if_exists(self) -> None:
        if self.writeLog:
            self.log_fout = open(self.log_name, 'a')

    def set_sizes(self, size_str):
        self.size_str        = size_str
        self.instance_suffix = size_str.replace('=', '_').replace(',', '_')
        import re
        tokens = re.split('=|,', self.size_str)
        i = 0
        while i < len(tokens)-1:
            sort = tokens[i]
            size = tokens[i+1]
            i += 2
            if len(sort) == 0 or len(size) == 0:
                break
            if not size.isdigit():
                break
            if sort in self.sizes:
                break
            self.sizes[sort] = int(size)

    def print_time(self):
        new_time_stamp  = datetime.datetime.now()
        if self.time_start != None and self.time_stamp != None:
            delta   = new_time_stamp - self.time_start 
            seconds = delta.seconds + 1e-6 * delta.microseconds
            vprint(self, "[QRM NOTE]: Time elapsed since start: %.3f seconds" % (seconds), 1)
            delta   = new_time_stamp - self.time_stamp 
            seconds = delta.seconds + 1e-6 * delta.microseconds
            vprint(self, "[QRM NOTE]: Time elapsed since last: %.3f seconds" % (seconds), 1)
            self.time_stamp = new_time_stamp
        else:
            self.time_start = new_time_stamp
            self.time_stamp = new_time_stamp

    def print_peak_memory_and_reset(self):
        (_, peak) = tracemalloc.get_traced_memory()
        vprint(self, f'[QRM NOTE]: Peak memory: {peak} bytes', 1)
        tracemalloc.reset_peak()    

    def step_start(self, verbose_string):
        vprint_step_banner(self, verbose_string)
        tracemalloc.start()

    def step_end(self):
        self.print_time()
        self.print_peak_memory_and_reset()

SET_DELIM      = '__'
SET_ELEM_DELIM = '_'
from ivy import ivy_logic as il
from ivy import ivy_logic_utils as ilu
class FormulaUtility():
    @staticmethod
    def flatten_or(formula):
        flat = set()
        if isinstance(formula, il.Or):
            for arg in formula.args:
                for flat_arg in FormulaUtility.flatten_or(arg):
                    flat.add(flat_arg)
        else:
            flat.add(formula)
        return list(flat)

    def flatten_and(formula):
        flat = set()
        if isinstance(formula, il.And):
            for arg in formula.args:
                for flat_arg in FormulaUtility.flatten_and(arg):
                    flat.add(flat_arg)
        elif (formula.is_not()):
            formulaNeg = formula.arg[0]
            if isinstance(formulaNeg, il.Or):
                for arg in formulaNeg.args:
                    for flat_arg in FormulaUtility.flatten_or(arg):
                        flat.add(il.Not(flat_arg))
            else:
                flat.add(formula)
        else:
            flat.add(formula)
        return list(flat)

    def flatten_cube(cube):
        flat = set()
        if isinstance(cube, il.Exists):
            cube = cube.args[0]

        if isinstance(cube, il.And):
            for arg in cube.args:
                for flat_arg in FormulaUtility.flatten_cube(arg):
                    flat.add(flat_arg)
        else:
            flat.add(cube)
        return list(flat)

    def count_quantifiers_and_literals(formula, pol=True, inF=0, inE=0, inL=0):
        outF = inF
        outE = inE
        outL = inL
        if isinstance(formula, il.Not):
            outF, outE, outL = FormulaUtility.count_quantifiers_and_literals(formula.args[0], not pol, outF, outE, outL)
            return (outF, outE, outL)
        if isinstance(formula, il.Implies):
            outF, outE, outL = FormulaUtility.count_quantifiers_and_literals(formula.args[0], not pol, outF, outE, outL)
            outF, outE, outL = FormulaUtility.count_quantifiers_and_literals(formula.args[1], pol, outF, outE, outL)
            return (outF, outE, outL)
        is_e = isinstance(formula, il.Exists)
        is_a = isinstance(formula, il.ForAll)
        if (is_e and pol) or (is_a and not pol):
            qvars = il.quantifier_vars(formula)
            outE += len(qvars)
            outF, outE, outL = FormulaUtility.count_quantifiers_and_literals(formula.args[0], pol, outF, outE, outL)
            return (outF, outE, outL)
        if (is_e and not pol) or (is_a and pol):
            qvars = il.quantifier_vars(formula)
            outF += len(qvars)
            outF, outE, outL = FormulaUtility.count_quantifiers_and_literals(formula.args[0], pol, outF, outE, outL)
            return (outF, outE, outL)
        if isinstance(formula, il.And) or isinstance(formula, il.Or):
            for arg in formula.args:
                outF, outE, outL = FormulaUtility.count_quantifiers_and_literals(arg, pol, outF, outE, outL)
        elif ilu.is_true(formula) or ilu.is_false(formula):
            pass
        else:
            outL += 1
        return (outF, outE, outL) 

    def de_morgan(f):
        """ remove negations from formula by applying de Morgans' laws """
        f = ilu.expand_abbrevs(f)
        if not isinstance(f,il.Not):
            return f
        g = FormulaUtility.de_morgan(f.args[0])
        if isinstance(g,il.And):
            if len(g.args) == 1: return FormulaUtility.de_morgan(ilu.negate(g.args[0]))
            return il.Or(*[FormulaUtility.de_morgan(ilu.negate(x)) for x in g.args])
        if isinstance(g,il.Or):
            if len(g.args) == 1: return FormulaUtility.de_morgan(ilu.negate(g.args[0]))
            return il.And(*[FormulaUtility.de_morgan(ilu.negate(x)) for x in g.args])
        if il.is_quantifier(g):
            prefix = il.quantifier_vars(g)
            matrix = il.quantifier_body(g)
            negate_matrix = FormulaUtility.de_morgan(ilu.negate(matrix))
            if isinstance(g, il.ForAll):
                return il.Exists(prefix, negate_matrix)
            if isinstance(g, il.Exists):
                return il.ForAll(prefix, negate_matrix)
        return il.Not(g)