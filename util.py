from enum import Enum
Mode  = Enum('Mode', ['ivy', 'yaml'])
UseMC = Enum('UseMC', ['sat', 'mc'])

class QrmOptions():
    def __init__(self) -> None:
        self.verbosity  = 0
        self.yaml_filename = ''
        self.instance_name = ''
        self.ivy_filename  = ''
        self.vmt_filename  = ''
        self.size_str      = ''
        self.sizes         = {} # sort name to size
        self.instance_suffix = ''
        self.mode  = Mode.ivy
        self.useMC = UseMC.sat
        self.check_qi        = False
        self.writeReach      = False
        self.writePrime      = False
        self.writeQI         = False
        self.writeLog        = False
        self.log_name        = ''
        self.log_fout        = None
        self.all_solutions   = True 
        self.merge_suborbits = True 
        self.ivy_to          = 120 
        self.qrm_to          = 3600 
        self.python_include_path = '/usr/include/python3.12'
        self.disable_print   = False # FIXME

    def set_files_name(self, ivy_name):
        self.ivy_filename  = ivy_name
        self.instance_name = ivy_name.split('.')[0]
        self.vmt_filename  = self.instance_name + '.vmt'

    def open_log(self) -> None:
        assert(self.writeLog)
        self.log_fout = open(self.log_name, 'a')

    def write_log(self, lines) -> None:
        self.log_fout.write(lines)
        self.log_fout.flush()

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
        return flat

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
        return flat 

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
        return flat

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

def get_instances_from_yaml(yaml_name):
    import yaml
    import itertools
    from math import comb
    instances  = {}
    yaml_file  = open(yaml_name, 'r')
    yaml_input = yaml.safe_load(yaml_file)
    for data in yaml_input.values():
        sizes = []
        sorts = []
        dep2quorum_size = {}
        is_quorum_list = []
        for sort, interval in data['size'].items(): #stable
            is_quorum = False
            size_tuple = tuple([0])
            size_tuple = tuple(range(interval['from'],interval['to']+1))
            is_quorum_list.append(is_quorum)
            sizes.append(size_tuple)
            sorts.append(sort)

        ivy_name = data['path']
        instances[ivy_name] = []
        for size in itertools.product(*sizes):
            size_list = list(size)
            for idx, is_quorum in enumerate(is_quorum_list):
                if is_quorum:
                    dep_idx = list(data['size'].keys()).index(dep_type)
                    dep_size = size_list[dep_idx]
                    size_list[idx] = dep2quorum_size[dep_size]
            size_str = ','.join([f'{k}={v}' for (k,v) in zip(sorts,size_list)])
            instances[ivy_name].append(size_str)
    return instances
