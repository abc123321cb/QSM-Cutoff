def print_banner(line : str) -> None:
    banner ='*'*100
    print()
    print(banner)
    print(f'\t\t{line}')
    print(banner)
    print()

def vprint(self, line : str, level:int) -> None:
    if (self.options.verbosity >= level):
        print(line)