import sys
import subprocess
from util import *
from verbose import *


def run_reach():
    yaml_name = 'yamls/all.yaml'
    instances = get_instances_from_yaml(yaml_name)
    options   = QrmOptions()
    timeout   = 5 
    memout    = 15000 #15GB
    for ivy_name, sizes in instances.items():
        instance_name = ivy_name.split('.')[0]
        options.writeLog   = True
        options.log_name   = instance_name + '.log'
        options.open_log()
        for size_str in sizes:
            vprint(options, f'[QRM]: [{instance_name}: {size_str}]')
            #qrm_args     = ['./runlim' f'--time-limit={timeout}', f'--real-time-limit={timeout}', f'--space-limit={memout}']
            qrm_args      = ['python3', 'qrm.py', ivy_name, '-s', size_str, '-f', '2', '-w', '-r', '-v', '5', '-l', f'{instance_name}.{size_str}.reach.log']
            if instance_name == 'consensus_epr':
                qrm_args.append('-b')
            try:
                subprocess.run(qrm_args, stderr=subprocess.PIPE, text=True, check=True, timeout=timeout) 
                sys.stdout.flush()
                vprint(options, '[QRM RESULT]: PASS')
            except subprocess.CalledProcessError as error:
                vprint(options, error.stderr)
                vprint(options, f'[QRM NOTE]: Exit with return code {error.returncode}')
                vprint(options, '[QRM RESULT]: FAIL')
            except subprocess.TimeoutExpired as error:
                vprint(options, f'[QRM NOTE]: Timeout after {timeout}')
                vprint(options, '[QRM RESULT]: FAIL')

if __name__ == '__main__':
    run_reach()