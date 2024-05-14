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
        self.ivy_to          = 60

    def open_log(self) -> None:
        assert(self.writeLog)
        self.log_fout = open(self.log_name, 'a')

    def write_log(self, lines) -> None:
        self.log_fout.write(lines)
        self.log_fout.flush()

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