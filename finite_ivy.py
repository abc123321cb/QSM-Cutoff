import os
import subprocess
from util import QrmOptions
from vmt_parser import TransitionSystem
from verbose import *

class IvyAccessAction():
    def __init__(self, symbol, param_types, return_type):
        self.symbol      = symbol
        self.param_types = param_types 
        self.return_type = return_type

        self._symbol_name     = str(symbol)
        self._action_name     = f'get_{str(symbol)}'
        self._param_types_str = [f'{str(ptype)}_{pid}: {str(ptype)}' for pid, ptype in enumerate(param_types)]
        self._params_list     = [f'{str(ptype)}_{pid}' for pid, ptype in enumerate(param_types)]
        self._return_type_str = 'bool' if return_type.is_bool_type() else str(return_type)

    def _get_action_header(self):
        line  = f'action {self._action_name}'
        if len(self.param_types):
            line += f'({', '.join(self._param_types_str)})'
        line += f' returns(x: {self._return_type_str}) = ' 
        line += '{\n'
        return line

    def _get_action_body(self):
        line = '    x := '
        line += f'{self._symbol_name}'
        if len(self.param_types):
            line += f'({', '.join(self._params_list)})'
        line += '\n'
        return line

    def _get_action_end(self):
        return '}\n'

    def _get_export_action(self):
        line  = f'export {self._action_name}'
        line += '\n'
        return line

    def get_action_lines(self):
        lines = []
        lines.append(self._get_action_header())
        lines.append(self._get_action_body())
        lines.append(self._get_action_end())
        lines.append(self._get_export_action())
        return lines

class FiniteIvy():
    # static datas
    tran_sys : TransitionSystem
    options  : QrmOptions
    lines               = []
    var2access_action = {}
    path_name       = ''
    file_prefix     = ''
    finite_ivy_name = ''
    executable_name = ''

    @staticmethod
    def _reset():
        FiniteIvy.lines = []

    def _get_finite_sort_line(line, sort_name):
        sort_elems = FiniteIvy.tran_sys.get_pretty_elements_of_sort(sort_name)
        line = line + ' = {' + ', '.join(sort_elems) + '}\n'
        return line

    def _set_lines_from_source_ivy():
        source_ivy = open(FiniteIvy.options.ivy_filename, 'r')
        for line in source_ivy.readlines():
            if line.startswith('type'): # type sort
                line = line.strip('\n')
                sort = line.split(' ')[1]
                line = FiniteIvy._get_finite_sort_line(line, sort)
            FiniteIvy.lines.append(line)
        source_ivy.close()

    def _add_comment_lines():
        FiniteIvy.lines.append('\n')
        FiniteIvy.lines.append('### For DFS reachability ###\n')

    def _add_dependent_sort_axiom_lines():
        FiniteIvy.lines.append('\n')
        FiniteIvy.lines.append('## Dependent relation axioms ##\n')
        axioms = FiniteIvy.tran_sys.get_dependent_axioms()
        for axiom in axioms:
            FiniteIvy.lines.append('axiom ' +axiom+'\n')

    def _add_access_action_lines():
        FiniteIvy.lines.append('\n')
        FiniteIvy.lines.append('## Access actions ##\n')
        for access_action in FiniteIvy.var2access_action.values():
            for line in access_action.get_action_lines():
                FiniteIvy.lines.append(line)
            FiniteIvy.lines.append('\n')

    def _write_lines_to_finite_ivy():
        finite_ivy = open(FiniteIvy.finite_ivy_name, 'w')
        for line in FiniteIvy.lines:
            finite_ivy.write(line)
        finite_ivy.close()

    def set_path_and_file_names():
        name = FiniteIvy.options.instance_name + '.' + FiniteIvy.options.instance_suffix + '.finite'
        segments  = name.split('/')
        FiniteIvy.path_name       = '/'.join(segments[:-1])
        FiniteIvy.file_prefix     = segments[-1]
        FiniteIvy.finite_ivy_name = segments[-1]  + '.ivy'
        FiniteIvy.executable_name = name

    def set_transition_system(tran_sys : TransitionSystem):
        FiniteIvy.tran_sys = tran_sys

    def set_options(options : QrmOptions):
        FiniteIvy.options  = options

    def set_state_var_to_access_action(var2access_action):
        FiniteIvy.var2access_action = var2access_action

    def write_ivy():
        FiniteIvy._reset()
        FiniteIvy._set_lines_from_source_ivy()
        FiniteIvy._add_comment_lines()
        FiniteIvy._add_dependent_sort_axiom_lines()
        FiniteIvy._add_access_action_lines()
        FiniteIvy._write_lines_to_finite_ivy()

    def compile_finite_ivy_to_cpp():
        ivy_args = ['ivy_to_cpp', 'target=repl', 'build=true', FiniteIvy.finite_ivy_name]
        ivy_cmd  = ' '.join(ivy_args)
        vprint(FiniteIvy.options, ivy_cmd)
        try:
            if FiniteIvy.options.write_log:
                subprocess.run(ivy_args, text=True, check=True, stdout=FiniteIvy.options.log_fout) 
            else:
                subprocess.run(ivy_args, capture_output=True, text=True, check=True) 
            sys.stdout.flush()
        except subprocess.CalledProcessError as error:
            if error.returncode == 1:
                vprint(FiniteIvy.options, f'[IVY_TO_CPP RESULT]: FAIL ... exit with return code {error.returncode}')
            else:
                vprint(FiniteIvy.options, f'[IVY_TO_CPP RESULT]: ABORT ... exit with return code {error.returncode}')
            return False
        return True

    def relocate_compilation_results():
        mv_cmd = f'mv {FiniteIvy.file_prefix}* {FiniteIvy.path_name}'
        os.system(mv_cmd)
        if not os.path.isfile(FiniteIvy.executable_name):
            vprint(FiniteIvy.options, f'[IVY_TO_CPP RESULT]: FAIL ... cannot fined {FiniteIvy.executable_name}')
            return False
        vprint(FiniteIvy.options, f'[IVY_TO_CPP RESULT]: OK')