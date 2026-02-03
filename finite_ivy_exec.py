from importlib import reload
from finite_ivy_instantiate import FiniteIvyInstantiator
from verbose import *
from util import QrmOptions

IVY_ACTION_COMPLETE   = 0
IVY_ACTION_INCOMPLETE = 1   # nondeterministic behavior not yet exhausted
IVY_ACTION_FAIL       = 2   # assumption failed

class FiniteIvyExecutor():
    def __init__(self, options : QrmOptions, instantiator : FiniteIvyInstantiator):
        import ivy_exec
        self.options = options
        self.ivy_exec = reload(ivy_exec)
        self.ivy_exec.ivy_exec_init()

        dfs_state_vars       = instantiator.dfs_state_vars
        dfs_interpreted_vars = instantiator.dfs_interpreted_vars
        ivy_state_vars       = instantiator.ivy_state_vars

        self.get_dfs_state_vars  = self.ivy_exec.StrVector(len(dfs_state_vars)) 
        for i, state_var in enumerate(dfs_state_vars):
            self.get_dfs_state_vars[i] = 'get_bool_' + state_var 

        self.get_dfs_interpreted_vars  = self.ivy_exec.StrVector(len(dfs_interpreted_vars)) 
        for i, state_var in enumerate(dfs_interpreted_vars):
            self.get_dfs_interpreted_vars[i] = 'get_bool_' + state_var 
        
        self.get_ivy_state_vars = self.ivy_exec.StrVector(len(ivy_state_vars)) 
        for i, state_var in enumerate(ivy_state_vars):
            self.get_ivy_state_vars[i] = 'get_' + state_var

    def _decode_ivy_state(self, result : str) -> str:
        return ','.join(result.strip('\n> = ').split('\n> = '))

    def _decode_dfs_state(self, result : str) -> str:
        return ''.join(c for c in result if c in '01')

    def get_dfs_state(self) -> str:
        self.ivy_exec.ivy_exec_reset_buffer()
        self.ivy_exec.ivy_exec_run_actions(self.get_dfs_state_vars)
        result = self.ivy_exec.ivy_exec_get_buffer()
        result = self._decode_dfs_state(result)
        return result

    def get_dfs_immutable_state(self) -> str:
        self.ivy_exec.ivy_exec_reset_buffer()
        self.ivy_exec.ivy_exec_run_actions(self.get_dfs_interpreted_vars)
        result = self.ivy_exec.ivy_exec_get_buffer()
        result = self._decode_dfs_state(result)
        return result

    def backup_ivy_state(self) -> str:
        self.ivy_exec.ivy_exec_reset_buffer()
        self.ivy_exec.ivy_exec_run_actions(self.get_ivy_state_vars)
        result = self.ivy_exec.ivy_exec_get_buffer()
        vprint(self.options, f"[DEBUG] Raw buffer from backup_ivy_state: '{result[:200]}'", 5)
        result = self._decode_ivy_state(result)
        vprint(self.options, f"[DEBUG] Decoded ivy_state: '{result[:200]}'", 5)
        vprint(self.options, f"[DEBUG] Number of values after decode: {len(result.split(','))}", 5)
        return result

    def restore_ivy_state(self, ivy_state : str):
        # Debug: log the state being restored
        vprint(self.options, f"[DEBUG] restore_ivy_state called with state length: {len(ivy_state)}", 5)
        vprint(self.options, f"[DEBUG] Ivy state is {ivy_state}", 5)
        
        ivy_state_list = ivy_state.split(',')
        vprint(self.options, f"[DEBUG] Split into {len(ivy_state_list)} values", 5)
        
        # Check for problematic values
        for i, value in enumerate(ivy_state_list):
            if value is None:
                vprint(self.options, f"[ERROR] Found None at index {i}", 1)
            elif value == '':
                vprint(self.options, f"[ERROR] Found empty string at index {i}", 1)
            elif not isinstance(value, str):
                vprint(self.options, f"[ERROR] Non-string value at index {i}: {type(value)}", 1)
        
        try:
            ivy_state_values = self.ivy_exec.StrVector(len(ivy_state_list))
            vprint(self.options, f"[DEBUG] Created StrVector of size {len(ivy_state_list)}", 5)
            
            for i, value in enumerate(ivy_state_list):
                ivy_state_values[i] = value
            
            vprint(self.options, f"[DEBUG] About to call ivy_exec_set_state", 5)
            self.ivy_exec.ivy_exec_set_state(ivy_state_values)
            vprint(self.options, f"[DEBUG] ivy_exec_set_state completed successfully", 5)
        except Exception as e:
            vprint(self.options, f"[ERROR] Exception in restore_ivy_state: {type(e).__name__}: {e}", 1)
            vprint(self.options, f"[ERROR] State was: {ivy_state[:200]}...", 1)
            raise

    def execute_ivy_action(self, ivy_action : str) -> int:
        prev_result   = self.ivy_exec.ivy_exec_get_buffer()
        self.ivy_exec.ivy_exec_reset_buffer()
        ivy_result    = self.ivy_exec.ivy_exec_run_action(ivy_action)
        if ivy_result == IVY_ACTION_FAIL:
            self.ivy_exec.ivy_exec_set_buffer(prev_result)
        return ivy_result 