from importlib import reload
from finite_ivy_instantiate import FiniteIvyInstantiator

class FiniteIvyExecutor():
    def __init__(self, instantiator : FiniteIvyInstantiator):
        import ivy_exec
        self.ivy_exec = reload(ivy_exec)
        self.ivy_exec.ivy_exec_init()

        dfs_state_vars  = instantiator.dfs_state_vars
        dfs_global_vars = instantiator.dfs_global_vars
        ivy_state_vars  = instantiator.ivy_state_vars

        self.get_dfs_state_vars  = self.ivy_exec.StrVector(len(dfs_state_vars)) 
        for i, state_var in enumerate(dfs_state_vars):
            self.get_dfs_state_vars[i] = 'get_bool_' + state_var 
        
        self.get_dfs_global_vars = self.ivy_exec.StrVector(len(dfs_global_vars)) 
        for i, global_var in enumerate(dfs_global_vars):
            self.get_dfs_global_vars[i] = 'get_bool_' + global_var 

        self.get_ivy_state_vars = self.ivy_exec.StrVector(len(ivy_state_vars)) 
        for i, state_var in enumerate(ivy_state_vars):
            self.get_ivy_state_vars[i] = 'get_' + state_var

    def _decode_ivy_state(self, result : str) -> str:
        return ','.join(result.strip('\n> = ').split('\n> = '))

    def get_dfs_state(self) -> str:
        self.ivy_exec.ivy_exec_reset_buffer()
        self.ivy_exec.ivy_exec_run_protocol(self.get_dfs_state_vars)
        result = self.ivy_exec.ivy_exec_get_buffer()
        result = self._decode_ivy_state(result)
        return result

    def get_dfs_global_state(self)  -> str:
        self.ivy_exec.ivy_exec_reset_buffer()
        self.ivy_exec.ivy_exec_run_protocol(self.get_dfs_global_vars)
        result = self.ivy_exec.ivy_exec_get_buffer()
        result = self._decode_ivy_state(result)
        return result

    def backup_ivy_state(self) -> str:
        self.ivy_exec.ivy_exec_reset_buffer()
        self.ivy_exec.ivy_exec_run_protocol(self.get_ivy_state_vars)
        result = self.ivy_exec.ivy_exec_get_buffer()
        result = self._decode_ivy_state(result)
        return result

    def restore_ivy_state(self, ivy_state : str):
        ivy_state = ivy_state.split(',')
        ivy_state_values = self.ivy_exec.StrVector(len(ivy_state)) 
        for i, value in enumerate(ivy_state):
            ivy_state_values[i] = value
        self.ivy_exec.ivy_exec_set_state(ivy_state_values)

    def execute_ivy_action(self, action : str) -> bool:
        prev_result   = self.ivy_exec.ivy_exec_get_buffer()
        ivy_action    = self.ivy_exec.StrVector(1) 
        ivy_action[0] = action
        self.ivy_exec.ivy_exec_reset_buffer()
        can_execute_action = self.ivy_exec.ivy_exec_run_protocol(ivy_action)
        if not can_execute_action:
            self.ivy_exec.ivy_exec_set_buffer(prev_result)
        result = self.ivy_exec.ivy_exec_get_buffer() 
        has_change_state = (result != prev_result)
        return has_change_state