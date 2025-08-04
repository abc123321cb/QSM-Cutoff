import sys
import inspect

def vprint_instance_banner(options, line : str, level=0, disable=False) -> None:
    if options.verbosity >= level and not disable:
        banner = '*'*(len(line)+20)
        lines =  '\n'
        lines += f'{banner}\n'
        lines += f'\n\t{line}\n\n'
        lines += f'{banner}\n'
        lines += '\n'
        sys.stdout.write(lines)
        sys.stdout.flush()
        if options.writeLog:
            options.write_log(lines)

def vprint_step_banner(options, line : str, level=0, disable=False) -> None:
    if options.verbosity >= level and not disable:
        banner = '='*(len(line)+15)
        lines =  '\n'
        lines += f'{banner}\n'
        lines += f'\n\t{line}\n\n'
        lines += f'{banner}\n'
        lines += '\n'
        sys.stdout.write(lines)
        sys.stdout.flush()
        if options.writeLog:
            options.write_log(lines)

def vprint_title(options, line : str, level=0, disable=False) -> None:
    if options.verbosity >= level and not disable:
        bullet = '-'*10
        line = f'\n{bullet} {line} {bullet}\n\n'
        sys.stdout.write(line)
        sys.stdout.flush()
        if options.writeLog:
            options.write_log(line)

def vprint(options, line : str, level=0, disable=False) -> None:
    if options.verbosity >= level and not disable:
        
        frame = inspect.currentframe()
        caller_frame = frame.f_back
        filename = caller_frame.f_code.co_filename
        lineno = caller_frame.f_lineno
        
        # Add caller info to the output
        #location = f'[Called from {filename}, line {lineno}]'
        #full_line = f'{location}\n{line}\n\n'
        full_line = f'{line}\n\n'

        # Output to stdout
        sys.stdout.write(full_line)
        sys.stdout.flush()

        if options.writeLog:
            options.write_log(line)