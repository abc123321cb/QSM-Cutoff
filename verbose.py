import sys
def vprint_instance_banner(options, line : str, level=0, disable=False) -> None:
    if options.verbosity >= level and not disable:
        banner = '*'*(len(line)+20)
        print()
        print(banner)
        print(f'\n\t{line}\n')
        print(banner)
        print()
        sys.stdout.flush()

def vprint_step_banner(options, line : str, level=0, disable=False) -> None:
    if options.verbosity >= level and not disable:
        banner = '='*(len(line)+15)
        print()
        print(banner)
        print(f'\n\t{line}\n')
        print(banner)
        print()
        sys.stdout.flush()

def vprint_title(options, line : str, level=0, disable=False) -> None:
    if options.verbosity >= level and not disable:
        bullet = '-'*10
        print(f'\n{bullet} {line} {bullet}\n')

def vprint(options, line : str, level=0, disable=False) -> None:
    if options.verbosity >= level and not disable:
        print(line)