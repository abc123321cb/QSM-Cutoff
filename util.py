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
        self.writeR          = False
        self.all_solutions   = False
        self.merge_suborbits = False

def get_instances_from_yaml(yaml_name):
    import yaml
    import itertools
    instances  = {}
    yaml_file  = open(yaml_name, 'r')
    yaml_input = yaml.safe_load(yaml_file)
    for data in yaml_input.values():
        sizes = []
        sorts = []
        for sort, interval in data['size'].items(): #stable
            sizes.append(tuple(range(interval['from'],interval['to']+2)))
            sorts.append(sort)
        ivy_name = data['path']
        instances[ivy_name] = []
        for size in itertools.product(*sizes):
            size_list = list(size)
            size_str = ','.join([f'{k}={v}' for (k,v) in zip(sorts,size_list)])
            instances[ivy_name].append(size_str)
    return instances