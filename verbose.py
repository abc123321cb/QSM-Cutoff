def vprint_banner(options, line : str, level=0) -> None:
    if options.verbosity >= level:
        banner ='**' + '='*(len(line)+20) + '**'
        print()
        print(banner)
        print(f'\n\t{line}\n')
        print(banner)
        print()

def vprint_title(options, line : str, level=0) -> None:
    if options.verbosity >= level:
        bullet = '-'*10
        print(f'\n{bullet} {line} {bullet}\n')

def vprint(options, line : str, level=0) -> None:
    if options.verbosity >= level:
        print(line)