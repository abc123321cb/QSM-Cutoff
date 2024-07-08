import os
import subprocess
from typing import List
from util import QrmOptions
from util import FormulaPrinter as printer
from transition import TransitionSystem
from verbose import *
import re

class FiniteIvyAccessAction():
    def __init__(self, symbol, param_types, return_type):
        self.symbol      = symbol
        self.param_types = param_types 
        self.return_type = return_type

        self._symbol_name      = str(symbol)
        self._action_name      = f'get_{str(symbol)}'
        self._bool_action_name = f'get_bool_{str(symbol)}'
        self._params_signature = [f'{str(ptype)[0]}{pid}: {str(ptype)}' for pid, ptype in enumerate(param_types)]
        self._params_list      = [f'{str(ptype)[0]}{pid}' for pid, ptype in enumerate(param_types)]
        self._return_type_str  = 'bool' if return_type.is_bool_type() else str(return_type)
        self._return_signature = 'result: bool' if return_type.is_bool_type() else f'result: {str(return_type)}'

    def _get_action_header(self):
        line  = f'action {self._action_name}'
        if len(self.param_types):
            line += f'({', '.join(self._params_signature)})'
        line += f' returns(x: {self._return_type_str}) = ' 
        line += '{\n'
        return line

    def _get_bool_action_header(self):
        line  = f'action {self._bool_action_name}'
        bool_params_signature = self._params_signature + [self._return_signature]
        line += f'({', '.join(bool_params_signature)})'
        line += f' returns(x: bool) = ' 
        line += '{\n'
        return line

    def _get_action_body(self):
        line = '    x := '
        line += f'{self._symbol_name}'
        if len(self.param_types):
            line += f'({', '.join(self._params_list)})'
        line += '\n'
        return line

    def _get_bool_action_body(self):
        line = '    x := ('
        line += f'{self._symbol_name}'
        if len(self.param_types):
            line += f'({', '.join(self._params_list)})'
        line += ' = result)\n'
        return line

    def _get_action_end(self):
        return '}\n'

    def _get_export_action(self):
        line  = f'export {self._action_name}'
        line += '\n'
        return line

    def _get_bool_export_action(self):
        line  = f'export {self._bool_action_name}'
        line += '\n'
        return line

    def get_action_lines(self):
        lines = []
        lines.append(self._get_action_header())
        lines.append(self._get_action_body())
        lines.append(self._get_action_end())
        lines.append(self._get_export_action())
        return lines

    def get_bool_action_lines(self):
        lines = []
        lines.append(self._get_bool_action_header())
        lines.append(self._get_bool_action_body())
        lines.append(self._get_action_end())
        lines.append(self._get_bool_export_action())
        return lines

class FiniteIvyGenerator():
    # static datas
    tran_sys : TransitionSystem
    options  : QrmOptions
    lines               = []
    var2access_action   = {}
    ivy_state_vars = []
    cpp_state_vars = []

    path_name           = '' #path_name
    file_name_prefix    = '' #instance_name.size.finite
    finite_ivy_name     = '' #instance_name.size.finite.ivy
    cpp_name            = '' #instance_name.size.finite.cpp
    wrapper_name        = '' #instance_name.size.finite_wrap.cpp
    object_name         = '' #instance_name.size.finite.o
    wrapper_object_name = '' #instance_name.size.finite_wrap.o

    swig_interface_name = 'ivy_exec.i'
    library_name        = '_ivy_exec.so'

    @staticmethod
    def _reset_lines():
        FiniteIvyGenerator.lines = []

    def _get_finite_sort_line(line, sort_name):
        sort_elems = FiniteIvyGenerator.tran_sys.get_pretty_constants_of_sort(sort_name)
        line = line + ' = {' + ', '.join(sort_elems) + '}\n'
        return line

    def _set_lines_from_source_ivy():
        source_ivy = open(FiniteIvyGenerator.options.ivy_filename, 'r')
        for line in source_ivy.readlines():
            if line.startswith('type'): # type sort
                line = line.strip('\n')
                sort = line.split(' ')[1]
                line = FiniteIvyGenerator._get_finite_sort_line(line, sort)
            FiniteIvyGenerator.lines.append(line)
        source_ivy.close()

    def _add_comment_lines():
        FiniteIvyGenerator.lines.append('\n')
        FiniteIvyGenerator.lines.append('### For QRM DFS reachability ###\n')

    def _add_dependent_sort_axiom_lines():
        FiniteIvyGenerator.lines.append('\n')
        FiniteIvyGenerator.lines.append('## Dependent relation axioms ##\n')
        axioms = FiniteIvyGenerator.tran_sys.get_dependent_axioms()
        for axiom in axioms:
            FiniteIvyGenerator.lines.append('axiom ' +axiom+'\n')

    def _add_access_action_lines():
        FiniteIvyGenerator.lines.append('\n')
        FiniteIvyGenerator.lines.append('## Access actions ##\n')
        for access_action in FiniteIvyGenerator.var2access_action.values():
            for line in access_action.get_action_lines():
                FiniteIvyGenerator.lines.append(line)
            FiniteIvyGenerator.lines.append('\n')
            for line in access_action.get_bool_action_lines():
                FiniteIvyGenerator.lines.append(line)
            FiniteIvyGenerator.lines.append('\n')

    def _write_lines_to_finite_ivy():
        finite_ivy = open(FiniteIvyGenerator.finite_ivy_name, 'w')
        for line in FiniteIvyGenerator.lines:
            finite_ivy.write(line)
        finite_ivy.close()

    def set_path_and_file_names():
        name = FiniteIvyGenerator.options.instance_name + '.' + FiniteIvyGenerator.options.instance_suffix + '.finite'
        segments  = name.split('/')
        FiniteIvyGenerator.path_name            = '/'.join(segments[:-1])
        FiniteIvyGenerator.file_name_prefix     = segments[-1]
        FiniteIvyGenerator.finite_ivy_name      = segments[-1]  + '.ivy'
        FiniteIvyGenerator.cpp_name             = segments[-1]  + '.cpp'
        FiniteIvyGenerator.wrapper_name         = segments[-1]  + '_wrap.cpp'
        FiniteIvyGenerator.object_name          = segments[-1]  + '.o'
        FiniteIvyGenerator.wrapper_object_name  = segments[-1]  + '_wrap.o'

    def set_transition_system(tran_sys : TransitionSystem):
        FiniteIvyGenerator.tran_sys = tran_sys

    def set_options(options : QrmOptions):
        FiniteIvyGenerator.options  = options

    def set_state_var_to_access_action():
        FiniteIvyGenerator.var2access_action = {}
        state_vars = FiniteIvyGenerator.tran_sys.get_state_variables()
        for var in state_vars:
            param_types = []
            return_type = None
            var_type = var.symbol_type()
            if not var_type.is_function_type():
                # case1: (start_node = n0)
                # case2: bool type, no parameters
                return_type = var_type 
            else: 
                # case3: predicate
                # case 4: function (predicate is a function with return type bool)
                param_types = list(var_type._param_types)
                return_type = var_type._return_type
            access_action = FiniteIvyAccessAction(var, param_types, return_type)
            FiniteIvyGenerator.var2access_action[var] = access_action

    def set_state_variables(element_Name2Id, ivy_state_vars):
        FiniteIvyGenerator.ivy_state_vars = ivy_state_vars
        FiniteIvyGenerator.cpp_state_vars = []
        for atom in FiniteIvyGenerator.ivy_state_vars:
            var_name = ''
            args     = []
            match  = re.search(r'(\w+)\(([^)]+)\)',  atom)
            if match: # case 3: predicate 
                var_name = match.group(1)
                args     = match.group(2).split(',')
            else:
                var_name = atom.strip('( )')
            args = [str(element_Name2Id[arg]) for arg in args]
            ivy_var = ''
            if len(args) > 0:
                ivy_var = var_name + '[' + ']['.join(args) + ']'
            else:
                ivy_var = var_name
            FiniteIvyGenerator.cpp_state_vars.append(ivy_var)

    def write_ivy():
        FiniteIvyGenerator._reset_lines()
        FiniteIvyGenerator._set_lines_from_source_ivy()
        FiniteIvyGenerator._add_comment_lines()
        FiniteIvyGenerator._add_dependent_sort_axiom_lines()
        FiniteIvyGenerator._add_access_action_lines()
        FiniteIvyGenerator._write_lines_to_finite_ivy()

    def _append_cpp():
        cpp_file = open(FiniteIvyGenerator.cpp_name, 'a')
        lines = []
        protocol_class_name = FiniteIvyGenerator.file_name_prefix.replace('-', '_').replace('.', '__') + '_repl'

        lines.append('\n')
        lines.append('/***********************************************************/\n')
        lines.append('/**                For QRM DFS reachability               **/\n')
        lines.append('/***********************************************************/\n')

        lines.append('\n')
        lines.append('#include <vector>\n')
        lines.append(protocol_class_name + ' * ivy_exec;\n') 
        lines.append('cmd_reader* ivy_exec_cr;\n') 
        lines.append('std::ostringstream ivy_exec_stream;\n')

        lines.append('\n')
        lines.append('void ivy_exec_init(){\n') 
        lines.append('\t__ivy_out.basic_ios<char>::rdbuf(ivy_exec_stream.rdbuf());\n') 
        lines.append('\tivy_exec = new ' + protocol_class_name + ';\n') 
        lines.append('\tivy_exec -> __unlock();\n') 
        lines.append('\tivy_exec_cr = new cmd_reader(*ivy_exec);\n') 
        lines.append('}\n') 

        lines.append('\n')
        lines.append('void ivy_exec_set_buffer(std::string buffer_str){\n') 
        lines.append('\tivy_exec_stream.str(buffer_str);\n') 
        lines.append('}\n') 

        lines.append('\n')
        lines.append('void ivy_exec_reset_buffer(){\n') 
        lines.append('\tivy_exec_stream.str("");\n') 
        lines.append('}\n') 

        lines.append('\n')
        lines.append('std::string ivy_exec_get_buffer(){\n') 
        lines.append('\treturn ivy_exec_stream.str();\n') 
        lines.append('}\n') 

        lines.append('\n')
        lines.append('void ivy_exec_set_state(std::vector<std::string> state_values){\n')
        for i, state_var in enumerate(FiniteIvyGenerator.cpp_state_vars):
            lines.append('\t std::stringstream(state_values[' + str(i) + ']) >> ivy_exec -> ' + state_var + ';\n')
        lines.append('}\n')  

        lines.append('\n')
        lines.append('bool ivy_exec_run_actions(std::vector<std::string> inputs){\n')  
        lines.append('\tfor (int i=0; i<inputs.size(); ++i){\n')
        lines.append('\t\tstd::string input = inputs[i];\n')
        lines.append('\t\tif (input == "STOP_PROTOCOL"){\n')
        lines.append('\t\t\tdelete ivy_exec_cr;\n')
        lines.append('\t\t\tdelete ivy_exec;\n')
        lines.append('\t\t\treturn false;\n') 
        lines.append('\t\t}\n') 
        lines.append('\t\ttry {\n')
        lines.append('\t\t\tivy_exec_cr->process(input);\n') 
        lines.append('\t\t}\n')
        lines.append('\t\tcatch (ivy_assume_err & err) {\n')
        lines.append('\t\t\tivy_exec -> __unlock();\n')
        lines.append('\t\t\treturn false;\n')
        lines.append('\t\t}\n')
        lines.append('\t}\n') 
        lines.append('\treturn true;\n')
        lines.append('}\n')                                                                    

        lines.append('\n')
        lines.append('const int QRM_IVY_ACTION_COMPLETE   = 0;\n')
        lines.append('const int QRM_IVY_ACTION_INCOMPLETE = 1;\n')
        lines.append('const int QRM_IVY_ACTION_FAIL       = 2;\n')

        lines.append('\n')
        lines.append('int ivy_exec_run_action(std::string input){\n')  
        lines.append('\tif (input == "QRM_STOP_PROTOCOL"){\n')
        lines.append('\t\tdelete ivy_exec_cr;\n')
        lines.append('\t\tdelete ivy_exec;\n')
        lines.append('\t\treturn QRM_IVY_ACTION_COMPLETE;\n') 
        lines.append('\t}\n') 
        lines.append('\ttry {\n')
        lines.append('\t\tif (input == "QRM_INIT_PROTOCOL"){\n')
        lines.append('\t\t\tivy_exec -> __init();\n') 
        lines.append('\t\t\tivy_exec -> __unlock();\n') 
        lines.append('\t\t}\n')
        lines.append('\t\telse ivy_exec_cr->process(input);\n') 
        lines.append('\t}\n')
        lines.append('\tcatch (ivy_assume_err & err) {\n')
        lines.append('\t\tivy_exec -> __unlock();\n')
        lines.append('\t\treturn QRM_IVY_ACTION_FAIL;\n')
        lines.append('\t}\n')
        lines.append('\tcatch (ivy_nondet_except & except) {\n')
        lines.append('\t\tivy_exec -> __unlock();\n')
        lines.append('\t\treturn QRM_IVY_ACTION_INCOMPLETE;\n')
        lines.append('\t}\n')
        lines.append('\treturn QRM_IVY_ACTION_COMPLETE;\n')
        lines.append('}\n')          
        
        for line in lines:
            cpp_file.write(line)
        cpp_file.close()

    def compile_finite_ivy_to_cpp():
        ivy_args = ['ivy_to_cpp', 'target=qrm', FiniteIvyGenerator.finite_ivy_name]
        ivy_cmd  = ' '.join(ivy_args)
        vprint(FiniteIvyGenerator.options, ivy_cmd)
        try:
            if FiniteIvyGenerator.options.write_log:
                subprocess.run(ivy_args, text=True, check=True, stdout=FiniteIvyGenerator.options.log_fout) 
            else:
                subprocess.run(ivy_args, capture_output=True, text=True, check=True) 
            sys.stdout.flush()
        except subprocess.CalledProcessError as error:
            if error.returncode == 1:
                vprint(FiniteIvyGenerator.options, f'[IVY_TO_CPP RESULT]: FAIL ... exit with return code {error.returncode}')
            else:
                vprint(FiniteIvyGenerator.options, f'[IVY_TO_CPP RESULT]: ABORT ... exit with return code {error.returncode}')
            return False
        if not os.path.isfile(FiniteIvyGenerator.cpp_name):
            vprint(FiniteIvyGenerator.options, f'[IVY_TO_CPP RESULT]: FAIL ... cannot fined {FiniteIvyGenerator.cpp_name}')
            return False
        FiniteIvyGenerator._append_cpp()
        vprint(FiniteIvyGenerator.options, f'[IVY_TO_CPP RESULT]: OK')
        return True

    def _generate_cpp_wrapper():
        swig      = ['swig']
        flags     = ['-c++', '-python', '-o']
        wrapper   = [FiniteIvyGenerator.wrapper_name]
        interface = [FiniteIvyGenerator.swig_interface_name]
        swig_args = swig + flags + wrapper + interface
        swig_cmd  = ' '.join(swig_args)
        vprint(FiniteIvyGenerator.options, swig_cmd)
        try:
            if FiniteIvyGenerator.options.write_log:
                subprocess.run(swig_args, text=True, check=True, stdout=FiniteIvyGenerator.options.log_fout) 
            else:
                subprocess.run(swig_args, capture_output=True, text=True, check=True) 
            sys.stdout.flush()
        except subprocess.CalledProcessError as error:
            if error.returncode == 1:
                vprint(FiniteIvyGenerator.options, f'[SWIG RESULT]: FAIL ... exit with return code {error.returncode}')
            else:
                vprint(FiniteIvyGenerator.options, f'[SWIG RESULT]: ABORT ... exit with return code {error.returncode}')
            return False
        if not os.path.isfile(FiniteIvyGenerator.wrapper_name):
            vprint(FiniteIvyGenerator.options, f'[SWIG RESULT]: FAIL ... cannot fined {FiniteIvyGenerator.wrapper_name}')
            return False
        vprint(FiniteIvyGenerator.options, f'[SWIG RESULT]: OK')
        return True

    def _compile_cpp():
        gpp       = ['g++']
        flags     = ['-std=c++11', '-fpic', '-pthread', '-O3']
        source    = [FiniteIvyGenerator.cpp_name, FiniteIvyGenerator.wrapper_name]
        include   = ['-I'+FiniteIvyGenerator.options.python_include_path]
        flag      = ['-c']
        gpp_args  = gpp + flags + source + include + flag
        gpp_cmd   = ' '.join(gpp_args)
        vprint(FiniteIvyGenerator.options, gpp_cmd)
        try:
            if FiniteIvyGenerator.options.write_log:
                subprocess.run(gpp_args, text=True, check=True, stdout=FiniteIvyGenerator.options.log_fout) 
            else:
                subprocess.run(gpp_args, capture_output=True, text=True, check=True) 
            sys.stdout.flush()
        except subprocess.CalledProcessError as error:
            if error.returncode == 1:
                vprint(FiniteIvyGenerator.options, f'[G++ RESULT]: FAIL ... exit with return code {error.returncode}')
            else:
                vprint(FiniteIvyGenerator.options, f'[G++ RESULT]: ABORT ... exit with return code {error.returncode}')
            return False
        if not os.path.isfile(FiniteIvyGenerator.object_name):
            vprint(FiniteIvyGenerator.options, f'[G++ RESULT]: FAIL ... cannot fined {FiniteIvyGenerator.object_name}')
            return False
        if not os.path.isfile(FiniteIvyGenerator.wrapper_object_name):
            vprint(FiniteIvyGenerator.options, f'[G++ RESULT]: FAIL ... cannot fined {FiniteIvyGenerator.wrapper_object_name}')
            return False
        vprint(FiniteIvyGenerator.options, f'[G++ RESULT]: OK')
        return True      

    def _link_library():
        gpp       = ['g++']
        flag1     = ['-shared']
        objects   = [FiniteIvyGenerator.object_name, FiniteIvyGenerator.wrapper_object_name]
        flag2     = ['-o']
        library   = [FiniteIvyGenerator.library_name]
        flags     = ['-lm', '-lstdc++']
        link_args = gpp + flag1 + objects + flag2 + library + flags
        link_cmd  = ' '.join(link_args)
        vprint(FiniteIvyGenerator.options, link_cmd)
        try:
            if FiniteIvyGenerator.options.write_log:
                subprocess.run(link_args, text=True, check=True, stdout=FiniteIvyGenerator.options.log_fout) 
            else:
                subprocess.run(link_args, capture_output=True, text=True, check=True) 
            sys.stdout.flush()
        except subprocess.CalledProcessError as error:
            if error.returncode == 1:
                vprint(FiniteIvyGenerator.options, f'[LINK RESULT]: FAIL ... exit with return code {error.returncode}')
            else:
                vprint(FiniteIvyGenerator.options, f'[LINK RESULT]: ABORT ... exit with return code {error.returncode}')
            return False
        if not os.path.isfile(FiniteIvyGenerator.library_name):
            vprint(FiniteIvyGenerator.options, f'[LINK RESULT]: FAIL ... cannot fined {FiniteIvyGenerator.library_name}')
            return False
        vprint(FiniteIvyGenerator.options, f'[LINK RESULT]: OK')
        return True      

    def build_ivy_exec_python_module():
        FiniteIvyGenerator._generate_cpp_wrapper()
        FiniteIvyGenerator._compile_cpp()
        FiniteIvyGenerator._link_library()

    def clean():
        mv_cmd = f'mv {FiniteIvyGenerator.file_name_prefix}* {FiniteIvyGenerator.path_name}'
        os.system(mv_cmd)
        os.system('rm -f *.o *_wrap* *.pyc *.pyo _ivy_exec.so ivy_exec.py')