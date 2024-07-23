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

        dfs_state_vars  = instantiator.dfs_state_vars
        dfs_axiom_vars  = instantiator.dfs_axiom_vars
        ivy_state_vars  = instantiator.ivy_state_vars

        self.get_dfs_state_vars  = self.ivy_exec.StrVector(len(dfs_state_vars)) 
        for i, state_var in enumerate(dfs_state_vars):
            self.get_dfs_state_vars[i] = 'get_bool_' + state_var 
        
        self.get_dfs_axiom_vars = self.ivy_exec.StrVector(len(dfs_axiom_vars)) 
        for i, axiom_var in enumerate(dfs_axiom_vars):
            self.get_dfs_axiom_vars[i] = 'get_bool_' + axiom_var 

        self.get_ivy_state_vars = self.ivy_exec.StrVector(len(ivy_state_vars)) 
        for i, state_var in enumerate(ivy_state_vars):
            self.get_ivy_state_vars[i] = 'get_' + state_var

    def _decode_ivy_state(self, result : str) -> str:
        return ','.join(result.strip('\n> = ').split('\n> = '))

    def get_dfs_state(self) -> str:
        self.ivy_exec.ivy_exec_reset_buffer()
        self.ivy_exec.ivy_exec_run_actions(self.get_dfs_state_vars)
        result = self.ivy_exec.ivy_exec_get_buffer()
        result = self._decode_ivy_state(result)
        return result

    def get_dfs_axiom_state(self)  -> str:
        self.ivy_exec.ivy_exec_reset_buffer()
        self.ivy_exec.ivy_exec_run_actions(self.get_dfs_axiom_vars)
        result = self.ivy_exec.ivy_exec_get_buffer()
        result = self._decode_ivy_state(result)
        return result

    def backup_ivy_state(self) -> str:
        self.ivy_exec.ivy_exec_reset_buffer()
        self.ivy_exec.ivy_exec_run_actions(self.get_ivy_state_vars)
        result = self.ivy_exec.ivy_exec_get_buffer()
        result = self._decode_ivy_state(result)
        return result

    def restore_ivy_state(self, ivy_state : str):
        ivy_state = ivy_state.split(',')
        ivy_state_values = self.ivy_exec.StrVector(len(ivy_state)) 
        for i, value in enumerate(ivy_state):
            ivy_state_values[i] = value
        self.ivy_exec.ivy_exec_set_state(ivy_state_values)

    def execute_ivy_action(self, ivy_action : str) -> int:
        prev_result   = self.ivy_exec.ivy_exec_get_buffer()
        self.ivy_exec.ivy_exec_reset_buffer()
        ivy_result    = self.ivy_exec.ivy_exec_run_action(ivy_action)
        if ivy_result == IVY_ACTION_FAIL:
            self.ivy_exec.ivy_exec_set_buffer(prev_result)
        return ivy_result 