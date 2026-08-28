from pathlib import Path
import sys


atoms = ['(ep(node0)=epoch0)', '(ep(node0)=epoch1)', '(ep(node0)=epoch2)', '(ep(node0)=epoch3)', '(ep(node1)=epoch0)', '(ep(node1)=epoch1)', '(ep(node1)=epoch2)', '(ep(node1)=epoch3)', 'held(node0)', 'held(node1)', 'locked(epoch0,node0)', 'locked(epoch0,node1)', 'locked(epoch1,node0)', 'locked(epoch1,node1)', 'locked(epoch2,node0)', 'locked(epoch2,node1)', 'locked(epoch3,node0)', 'locked(epoch3,node1)', 'transfer(epoch0,node0)', 'transfer(epoch0,node1)', 'transfer(epoch1,node0)', 'transfer(epoch1,node1)', 'transfer(epoch2,node0)', 'transfer(epoch2,node1)', 'transfer(epoch3,node0)', 'transfer(epoch3,node1)']



def normalize_atom(atom):
    atom = atom.strip()

    # Legacy format: (ep(node0)=epoch2)
    if atom.startswith('(ep(') and atom.endswith(')') and ')=' in atom:
        inner = atom[1:-1]  # ep(node0)=epoch2
        left, epoch = inner.split(')=', 1)
        node = left[left.find('(') + 1 :].replace('node', 'n')
        return f"ep_{epoch}", node

    # Legacy format: held(node0)
    if atom.startswith('held(') and atom.endswith(')'):
        node = atom[atom.find('(') + 1 : -1].replace('node', 'n')
        return 'held', node

    # Legacy format: locked(epoch2,node1) / transfer(epoch1,node0)
    if (atom.startswith('locked(') or atom.startswith('transfer(')) and atom.endswith(')'):
        pred = atom[:atom.find('(')]
        inside = atom[atom.find('(') + 1 : -1]
        epoch, node = [x.strip() for x in inside.split(',', 1)]
        return f"{pred}_{epoch}", node.replace('node', 'n')

    # Current format fallback: func_node
    parts = atom.rsplit('_', 1)
    if len(parts) == 2:
        return parts[0], parts[1]

    raise ValueError(f"Unsupported atom format: {atom}")


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
        func_name, node_name = normalize_atom(atoms_list[i])
        
        if bit == '1':
            constraints.append(f"({func_name} {node_name})")
        else:
            constraints.append(f"(not ({func_name} {node_name}))")
            
    # Formats as define-fun S1/S2/... returning Bool.
    return f"(define-fun S{state_num} () Bool\n  (and\n    " + "\n    ".join(constraints) + "\n  ))"


default_states_path = Path(__file__).with_name('simplified_states.txt')
states_path = Path(sys.argv[1]) if len(sys.argv) > 1 else default_states_path
reachable_bitstrings = load_reachable_bitstrings(states_path, len(atoms))

# Generate assertions for all states
for i, bitstring in enumerate(reachable_bitstrings, 1):
    print(bitstring_to_smt(bitstring, atoms, i))