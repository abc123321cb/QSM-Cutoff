def vprint_banner(self, line : str, level=0) -> None:
    if self.options.verbosity >= level:
        banner ='='*(len(line)+20)
        print()
        print(banner)
        print(f'\n\t{line}\n')
        print(banner)
        print()

def vprint(self, line : str, level=0) -> None:
    if self.options.verbosity >= level:
        print(line)