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

    path_name           = '' #path_name
    file_name_prefix    = '' #instance_name.size.finite
    finite_ivy_name     = '' #instance_name.size.finite.ivy
    cpp_name            = '' #instance_name.size.finite.cpp
    wrapper_name        = '' #instance_name.size.finite_wrap.cpp
    object_name         = '' #instance_name.size.finite.o
    wrapper_object_name =  '' #instance_name.size.finite_wrap.o

    swig_interface_name = 'ivy2cpp.i'
    library_name        = '_ivy2cpp.so'

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
        FiniteIvy.path_name            = '/'.join(segments[:-1])
        FiniteIvy.file_name_prefix     = segments[-1]
        FiniteIvy.finite_ivy_name      = segments[-1]  + '.ivy'
        FiniteIvy.cpp_name             = segments[-1]  + '.cpp'
        FiniteIvy.wrapper_name         = segments[-1]  + '_wrap.cpp'
        FiniteIvy.object_name          = segments[-1]  + '.o'
        FiniteIvy.wrapper_object_name  = segments[-1]  + '_wrap.o'

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

    def _append_cpp():
        cpp_file = open(FiniteIvy.cpp_name, 'a')
        lines = []
        lines.append('int run_protocol(){\n')
        lines.append('\tif (!__ivy_out.is_open())\n')
        lines.append('\t\t__ivy_out.basic_ios<char>::rdbuf(std::cout.rdbuf());\n')
        lines.append('\t' + FiniteIvy.file_name_prefix.replace('.', '__') + '_repl ivy;\n')
        lines.append('\tivy.__init();\n')
        lines.append('\tivy.__unlock();\n')
        lines.append('\tcmd_reader *cr = new cmd_reader(ivy);\n')
        lines.append('\tbool stop_protocol;\n')
        lines.append('\twhile (std::cin >> stop_protocol){\n')
        lines.append('\t\tif (stop_protocol)\n')
        lines.append('\t\t\tbreak;\n')
        lines.append('\t\tcr->read();\n')
        lines.append('\t}\n')
        lines.append('\treturn 0;\n')
        lines.append('}')

        # int run_protocol(){
        #     if (!__ivy_out.is_open())
        #         __ivy_out.basic_ios<char>::rdbuf(std::cout.rdbuf());
        #     toy_consensus__node_3_value_3__finite_repl ivy;
        #     ivy.__init();
        # 
        #     ivy.__unlock();
        # 
        #     cmd_reader *cr = new cmd_reader(ivy);
        # 
        #     bool stop_protocol;
        #     while (std::cin >> stop_protocol){
        #         if (stop_protocol)
        #             break;
        #         cr->read();
        #     }
        #         
        #     return 0;
        # }

        for line in lines:
            cpp_file.write(line)
        cpp_file.close()

    def compile_finite_ivy_to_cpp():
        ivy_args = ['ivy_to_cpp', 'target=repl', FiniteIvy.finite_ivy_name]
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
        if not os.path.isfile(FiniteIvy.cpp_name):
            vprint(FiniteIvy.options, f'[IVY_TO_CPP RESULT]: FAIL ... cannot fined {FiniteIvy.cpp_name}')
            return False
        FiniteIvy._append_cpp()
        vprint(FiniteIvy.options, f'[IVY_TO_CPP RESULT]: OK')
        return True

    def _generate_cpp_wrapper():
        swig      = ['swig']
        flags     = ['-c++', '-python', '-o']
        wrapper   = [FiniteIvy.wrapper_name]
        interface = [FiniteIvy.swig_interface_name]
        swig_args = swig + flags + wrapper + interface
        swig_cmd  = ' '.join(swig_args)
        vprint(FiniteIvy.options, swig_cmd)
        try:
            if FiniteIvy.options.write_log:
                subprocess.run(swig_args, text=True, check=True, stdout=FiniteIvy.options.log_fout) 
            else:
                subprocess.run(swig_args, capture_output=True, text=True, check=True) 
            sys.stdout.flush()
        except subprocess.CalledProcessError as error:
            if error.returncode == 1:
                vprint(FiniteIvy.options, f'[SWIG RESULT]: FAIL ... exit with return code {error.returncode}')
            else:
                vprint(FiniteIvy.options, f'[SWIG RESULT]: ABORT ... exit with return code {error.returncode}')
            return False
        if not os.path.isfile(FiniteIvy.wrapper_name):
            vprint(FiniteIvy.options, f'[SWIG RESULT]: FAIL ... cannot fined {FiniteIvy.wrapper_name}')
            return False
        vprint(FiniteIvy.options, f'[SWIG RESULT]: OK')
        return True

    def _compile_cpp():
        gpp       = ['g++']
        flags     = ['-std=c++11', '-fpic', '-pthread', '-O3']
        source    = [FiniteIvy.cpp_name, FiniteIvy.wrapper_name]
        include   = ['-I'+FiniteIvy.options.python_include_path]
        flag      = ['-c']
        gpp_args  = gpp + flags + source + include + flag
        gpp_cmd   = ' '.join(gpp_args)
        vprint(FiniteIvy.options, gpp_cmd)
        try:
            if FiniteIvy.options.write_log:
                subprocess.run(gpp_args, text=True, check=True, stdout=FiniteIvy.options.log_fout) 
            else:
                subprocess.run(gpp_args, capture_output=True, text=True, check=True) 
            sys.stdout.flush()
        except subprocess.CalledProcessError as error:
            if error.returncode == 1:
                vprint(FiniteIvy.options, f'[G++ RESULT]: FAIL ... exit with return code {error.returncode}')
            else:
                vprint(FiniteIvy.options, f'[G++ RESULT]: ABORT ... exit with return code {error.returncode}')
            return False
        if not os.path.isfile(FiniteIvy.object_name):
            vprint(FiniteIvy.options, f'[G++ RESULT]: FAIL ... cannot fined {FiniteIvy.object_name}')
            return False
        if not os.path.isfile(FiniteIvy.wrapper_object_name):
            vprint(FiniteIvy.options, f'[G++ RESULT]: FAIL ... cannot fined {FiniteIvy.wrapper_object_name}')
            return False
        vprint(FiniteIvy.options, f'[G++ RESULT]: OK')
        return True      

    def _link_library():
        gpp       = ['g++']
        flag1     = ['-shared']
        objects   = [FiniteIvy.object_name, FiniteIvy.wrapper_object_name]
        flag2     = ['-o']
        library   = [FiniteIvy.library_name]
        flags     = ['-lm', '-lstdc++']
        link_args = gpp + flag1 + objects + flag2 + library + flags
        link_cmd  = ' '.join(link_args)
        vprint(FiniteIvy.options, link_cmd)
        try:
            if FiniteIvy.options.write_log:
                subprocess.run(link_args, text=True, check=True, stdout=FiniteIvy.options.log_fout) 
            else:
                subprocess.run(link_args, capture_output=True, text=True, check=True) 
            sys.stdout.flush()
        except subprocess.CalledProcessError as error:
            if error.returncode == 1:
                vprint(FiniteIvy.options, f'[LINK RESULT]: FAIL ... exit with return code {error.returncode}')
            else:
                vprint(FiniteIvy.options, f'[LINK RESULT]: ABORT ... exit with return code {error.returncode}')
            return False
        if not os.path.isfile(FiniteIvy.library_name):
            vprint(FiniteIvy.options, f'[LINK RESULT]: FAIL ... cannot fined {FiniteIvy.library_name}')
            return False
        vprint(FiniteIvy.options, f'[LINK RESULT]: OK')
        return True      

    def build_ivy2cpp_python_module():
        FiniteIvy._generate_cpp_wrapper()
        FiniteIvy._compile_cpp()
        FiniteIvy._link_library()

    def clean():
        mv_cmd = f'mv {FiniteIvy.file_name_prefix}* {FiniteIvy.path_name}'
        os.system(mv_cmd)
        os.system('rm -f *.o *_wrap* *.pyc *.pyo _ivy2cpp.so ivy2cpp.py')
