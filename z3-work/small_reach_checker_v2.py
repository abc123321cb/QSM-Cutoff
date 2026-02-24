import z3
import re

atoms = [
    'ep_n0_e0', 'ep_n0_e1', 'ep_n0_e2', 'ep_n0_e3', 
    'ep_n1_e0', 'ep_n1_e1', 'ep_n1_e2', 'ep_n1_e3', 
    'held_n0', 'held_n1', 
    'l_e0_n0', 'l_e0_n1', 'l_e1_n0', 'l_e1_n1', 'l_e2_n0', 'l_e2_n1', 'l_e3_n0', 'l_e3_n1',
    't_e0_n0', 't_e0_n1', 't_e1_n0', 't_e1_n1', 't_e2_n0', 't_e2_n1', 't_e3_n0', 't_e3_n1'
]

reachable_bitstrings = [
    '01001000100010000000000000',
    '10000100010001000000000000',
    '01001000000010000000001000',
    '10000100000001000000000100',
    '00101000100010100000000000',
    '10000010010001010000000000',
    '00101000000010100000000010',
    '10000010000001010000000001',
    '00011000100010101000000000',
    '10000001010001010100000000',
    '00101000000010100000000001',
    '10000010000001010000000010',
    '00100001010010100100000000',
    '00010010100001011000000000',
    '01001000000010000000000010',
    '10000100000001000000000001',
    '00011000100010001000000000',
    '10000001010001000100000000',
    '01001000000010000000000100',
    '10000100000001000000001000',
    '01000010010010010000000000',
    '00100100100001100000000000',
    '01000010000010010000000010',
    '00100100000001100000000001',
    '00010010100010011000000000',
    '00100001010001100100000000',
    '01000010000010010000000001',
    '00100100000001100000000010',
    '01000001010010010100000000',
    '00010100100001101000000000',
    '01001000000010000000000001',
    '10000100000001000000000010',
    '01000001010010000100000000',
    '00010100100001001000000000'
]

def format_state_readable(bit_str, atoms_list):
    readable_lines = []
    for i, bit in enumerate(bit_str):
        if bit == '1':
            label = atoms_list[i]
            pretty = label.replace('ep_n', 'ep(node').replace('l_e', 'locked(epoch').replace('t_e', 'transfer(epoch').replace('held_n', 'held(node').replace('_e', ') = epoch').replace('_n', ', node')
            if '(' in pretty and ')' not in pretty: pretty += ')'
            readable_lines.append(pretty)
    return "\n    " + "\n    ".join(readable_lines)

def check_reach():
    # 1. Map atoms to named Boolean variables for SMT-LIB readability
    atom_vars = {name: z3.Bool(name) for name in atoms}

    def get_b(name):
        return atom_vars[name]

    # 2. Define Invariants using Boolean logic
    invars = []
    
    # --- Basic Negations ---
    for n in ['n0', 'n1']:
        invars.append(z3.Not(get_b(f'l_e0_{n}')))
        invars.append(z3.Not(get_b(f't_e1_{n}')))
        invars.append(z3.Or(z3.Not(get_b(f'ep_{n}_e0')), z3.Not(get_b(f'held_{n}'))))

    # --- Identity Logic ---
    pairs = [('n0', 'n1'), ('n1', 'n0')]
    for n0, n1 in pairs:
        invars.append(z3.Or(get_b(f'l_e1_{n1}'), z3.Not(get_b(f'ep_{n0}_e0'))))
        invars.append(z3.Or(z3.Not(get_b(f'ep_{n0}_e3')), z3.Not(get_b(f'held_{n1}'))))
        invars.append(z3.Or(z3.Not(get_b(f'held_{n0}')), z3.Not(get_b(f'l_e3_{n1}'))))
        for e in ['1', '2', '3']:
            invars.append(z3.Or(z3.Not(get_b(f'l_e{e}_{n1}')), z3.Not(get_b(f'ep_{n0}_e{e}'))))

    # --- Consistency Rules ---
    for n in ['n0', 'n1']:
        invars.append(z3.Or(get_b(f'held_{n}'), z3.Not(get_b(f'ep_{n}_e3'))))
        invars.append(z3.Or(get_b(f'ep_{n}_e3'), z3.Not(get_b(f'l_e3_{n}'))))
        invars.append(z3.Or(get_b(f'held_{n}'), z3.Not(get_b(f'l_e3_{n}'))))
        invars.append(z3.Or(get_b(f'l_e1_{n}'), z3.Not(get_b(f'ep_{n}_e1'))))
        invars.append(z3.Or(z3.Not(get_b(f'ep_{n}_e2')), get_b(f'l_e2_{n}')))
        invars.append(z3.Or(z3.Not(get_b(f'ep_{n}_e3')), get_b(f'l_e3_{n}')))

    # --- Existentials & Mutual Exclusions ---
    h_any = z3.Or(get_b('held_n0'), get_b('held_n1'))
    t2_any = z3.Or(get_b('t_e2_n0'), get_b('t_e2_n1'))
    t3_any = z3.Or(get_b('t_e3_n0'), get_b('t_e3_n1'))
    l2_any = z3.Or(get_b('l_e2_n0'), get_b('l_e2_n1'))
    l3_any = z3.Or(get_b('l_e3_n0'), get_b('l_e3_n1'))

    invars.append(z3.Or(z3.Not(get_b('held_n0')), z3.Not(get_b('held_n1')))) # Exists ~held
    invars.append(z3.Not(z3.And(t2_any, t3_any)))
    invars.append(z3.Not(z3.And(h_any, t2_any)))
    invars.append(z3.Not(z3.And(l2_any, t2_any)))

    all_invariants = z3.And(*invars)

    # 3. Solver Setup for REVERSE CHECK (Finding missing states)
    solver = z3.Solver()
    solver.add(all_invariants)

    # Exclude known reachable states
    for bit_str in reachable_bitstrings:
        state_match = []
        for i, bit in enumerate(bit_str):
            var = get_b(atoms[i])
            state_match.append(var if bit == '1' else z3.Not(var))
        solver.add(z3.Not(z3.And(*state_match)))

    # Discovery Loop
    missing_states = []
    print("--- DISCOVERING MISSING STATES ---")
    while solver.check() == z3.sat:
        model = solver.model()
        # Reconstruct bitstring from Boolean model
        res = ["1" if z3.is_true(model[atom_vars[a]]) else "0" for a in atoms]
        found_str = "".join(res)
        
        missing_states.append(found_str)
        print(f"Missing: {found_str}{format_state_readable(found_str, atoms)}")
        
        # Block this state
        block = []
        for a in atoms:
            val = model[atom_vars[a]]
            block.append(atom_vars[a] == val)
        solver.add(z3.Not(z3.And(*block)))
        
        if len(missing_states) >= 10: break

    # 4. EXPORT TO READABLE SMT-LIB
    with open("readable_reach.smt2", "w") as f:
        f.write("; Benchmark generated with named Boolean variables for readability\n")
        f.write(solver.to_smt2())
        f.write("\n(check-sat)\n(get-model)\n")

    print(f"\n========SUMMARY========\n")
    print(f"Missing states found: {len(missing_states)}")
    print("SMT-LIB code exported to: readable_reach.smt2")

if __name__ == "__main__":
    check_reach()