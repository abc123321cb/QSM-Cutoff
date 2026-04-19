from pathlib import Path
import sys


atoms = [
    'ep_epoch0_n0', 'ep_epoch1_n0', 'ep_epoch2_n0', 'ep_epoch3_n0', 
    'ep_epoch0_n1', 'ep_epoch1_n1', 'ep_epoch2_n1', 'ep_epoch3_n1', 
    'held_n0', 'held_n1', 
    'locked_epoch0_n0', 'locked_epoch0_n1', 'locked_epoch1_n0', 'locked_epoch1_n1', 
    'locked_epoch2_n0', 'locked_epoch2_n1', 'locked_epoch3_n0', 'locked_epoch3_n1',
    'transfer_epoch0_n0', 'transfer_epoch0_n1', 'transfer_epoch1_n0', 'transfer_epoch1_n1', 
    'transfer_epoch2_n0', 'transfer_epoch2_n1', 'transfer_epoch3_n0', 'transfer_epoch3_n1'
]


def load_reachable_bitstrings(file_path, expected_len):
    bitstrings = []
    with open(file_path, 'r', encoding='utf-8') as f:
        for line_num, raw_line in enumerate(f, 1):
            line = raw_line.strip()
            if not line or line.startswith('#'):
                continue
            if set(line) - {'0', '1'}:
                raise ValueError(
                    f"Invalid line {line_num} in {file_path}: expected only 0/1 characters"
                )
            if len(line) != expected_len:
                raise ValueError(
                    f"Invalid line {line_num} in {file_path}: expected length {expected_len}, got {len(line)}"
                )
            bitstrings.append(line)

    if not bitstrings:
        raise ValueError(f"No bitstrings found in {file_path}")

    return bitstrings

def bitstring_to_smt(bit_str, atoms_list, state_num):
    constraints = []
    for i, bit in enumerate(bit_str):
        atom = atoms_list[i]
        # Split 'locked_epoch0_n0' into ('locked_epoch0', 'n0')
        parts = atom.rsplit('_', 1)
        func_name = parts[0]
        node_name = parts[1]
        
        if bit == '1':
            constraints.append(f"({func_name} {node_name})")
        else:
            constraints.append(f"(not ({func_name} {node_name}))")
            
    # Formats as S1 = (and ...), S2 = (and ...), etc.
    return f"(assert (= S{state_num} (and\n    " + "\n    ".join(constraints) + "\n)))"


default_states_path = Path(__file__).with_name('simplified_states.txt')
states_path = Path(sys.argv[1]) if len(sys.argv) > 1 else default_states_path
reachable_bitstrings = load_reachable_bitstrings(states_path, len(atoms))

# Generate assertions for all states
for i, bitstring in enumerate(reachable_bitstrings, 1):
    print(bitstring_to_smt(bitstring, atoms, i))