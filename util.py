from enum import Enum
Mode  = Enum('Mode', ['ivy', 'yaml'])
UseMC = Enum('UseMC', ['sat', 'appMC'])

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
        self.writeReach      = False
        self.writePrime      = False
        self.writeQI         = False
        self.writeLog        = False
        self.log_name        = ''
        self.log_fout        = None
        self.all_solutions   = False
        self.merge_suborbits = False
        self.ivy_to          = 120 
        self.qrm_to          = 3600 

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

from pysmt.pretty_printer import pretty_serialize
SORT_SUFFIX = ':e'
class FormulaPrinter():

    name_set   = set()
    sort_count = {}
    qvar_count = 0

    @staticmethod
    def reset():
        FormulaPrinter.name_set   = set()
        FormulaPrinter.sort_count = {}
        FormulaPrinter.qvar_count = 0

    def pretty_print_enum_constant(enum):
        assert(enum.is_enum_constant())
        name = enum.constant_value()
        prefix = name.rstrip('1234567890')
        suffix = name[len(prefix):]
        prefix = prefix.rstrip(':1234567890')
        assert(prefix.endswith(SORT_SUFFIX))
        prefix = prefix[:-2]
        return prefix+suffix

    def pretty_print_quantified_var(qvar):
        name   = str(qvar)
        suffix = name.rstrip('1234567890')
        name   = name[len(suffix):]
        assert(len(name) != 0)
        var_type = qvar.symbol_type()
        sort_name = str(var_type)[0].upper()
        if sort_name not in FormulaPrinter.sort_count:
            FormulaPrinter.sort_count[sort_name] = 0
        name = sort_name + str(FormulaPrinter.sort_count[sort_name])
        FormulaPrinter.sort_count[sort_name] += 1
        if name in FormulaPrinter.name_set:
            name = name + '_' + str(FormulaPrinter.qvar_count)
            FormulaPrinter.qvar_count += 1
        FormulaPrinter.name_set.add(name)
        return name
    
    def pretty_print_free_var(fvar):
        name = str(fvar)
        name = name.lstrip('_')
        suffix = name.rstrip('1234567890')
        if len(suffix) != 0:
            tmp_name = name[:len(suffix)]
            if tmp_name.endswith(SORT_SUFFIX):
                name = tmp_name[:-2]
        return name

    def pretty_print_str(fmla, mode=0, reset=True):
        FormulaPrinter.reset()
        subs = {}
        qvars   = fmla.get_quantifier_variables()
        for qvar in qvars:
            name = FormulaPrinter.pretty_print_quantified_var(qvar)
            subs[qvar] = name
        fvars = fmla.get_free_variables()
        for fvar in fvars:
            name = FormulaPrinter.pretty_print_free_var(fvar)
            subs[fvar] = name
        enums = fmla.get_enum_constants()
        for enum in enums:
            name = FormulaPrinter.pretty_print_enum_constant(enum)
            subs[enum] = name
        if reset:
            mode = 0
        return pretty_serialize(fmla, mode=mode, subs=subs)

    def pretty_print_set(set_to_print, mode=1):
        list_to_print = [pretty_serialize(elem) for elem in set_to_print]
        res = '[ ' + ', '.join(list_to_print) + ' ]'
        return res

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
            if 'superset' in interval.keys():
                dep_type = interval['superset']
                dep_from = data['size'][dep_type]['from']
                dep_to   = data["size"][dep_type]['to'] +2
                for dep_size in range(dep_from, dep_to):
                    quorum_size = comb(dep_size, int(dep_size/2)+1)
                    dep2quorum_size[dep_size] = quorum_size
                is_quorum  = True
            else:
                size_tuple = tuple(range(interval['from'],interval['to']+2))
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
