import z3

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
            
            # Clean up the shorthand for the professor
            pretty_label = label.replace('ep_n', 'ep(node') \
                                .replace('l_e', 'locked(epoch') \
                                .replace('t_e', 'transfer(epoch') \
                                .replace('held_n', 'held(node') \
                                .replace('_e', ') = epoch') \
                                .replace('_n', ', node')           
            # Close the parenthesis for locked/transfer/held if they were opened
            if '(' in pretty_label and ')' not in pretty_label:
                pretty_label += ')'
                
            readable_lines.append(pretty_label)
            
    return "\n    ".join(readable_lines)

def export_to_smtlib(solver, filename="small_reach_checker.smt2"):
    """
    Exports the current solver state to a standalone SMT-LIB v2 file.
    """
    # Get the SMT-LIB string from the solver
    smt_string = solver.to_smt2()
    
    with open(filename, "w") as f:
        f.write(smt_string)
        
        f.write("\n(check-sat)\n")
        f.write("(get-model)\n")
        
    print(f"\nSMT-LIB code exported to: {filename}")

def check_reach():
    solver = z3.Solver()
    num_atoms = len(atoms)

    # Create state variables for each reachable state
    states = []
    for i, bit_str in enumerate(reachable_bitstrings, 1):
        state_var = z3.BitVec(f'S{i}', num_atoms)
        states.append(state_var)
        # Assert that this state equals the bitstring value
        solver.add(state_var == int(bit_str, 2))

    # Helper to get bit value by atom name for a given state
    def get_bit(state, name):
        idx = atoms.index(name)
        return z3.Extract(num_atoms - 1 - idx, num_atoms - 1 - idx, state) == 1

    # 2. Define your invariants in Z3 logic for a given state
    
    def form_invariants(state):
        invars = []
        def get_b(name): return get_bit(state, name)

        # --- Basic Negations ---
        for n in ['n0', 'n1']:
            invars.append(z3.Not(get_b(f'l_e0_{n}'))) # ~locked_epoch0
            invars.append(z3.Not(get_b(f't_e1_{n}'))) # ~transfer_epoch1
            # ~ep_epoch0(NODE0) | ~held(NODE0)
            invars.append(z3.Or(z3.Not(get_b(f'ep_{n}_e0')), z3.Not(get_b(f'held_{n}'))))

        # --- Identity Logic (NODE0 != NODE1 cases) ---
        # forall NODE0,NODE1. NODE0 != NODE1 => ...
        pairs = [('n0', 'n1'), ('n1', 'n0')]
        for n0, n1 in pairs:
            # locked_epoch1(N1) | ~ep_epoch0(N0)
            invars.append(z3.Or(get_b(f'l_e1_{n1}'), z3.Not(get_b(f'ep_{n0}_e0'))))
            # ~ep_epoch3(N0) | ~held(N1)
            invars.append(z3.Or(z3.Not(get_b(f'ep_{n0}_e3')), z3.Not(get_b(f'held_{n1}'))))
            # ~held(N0) | ~locked_epoch3(N1)
            invars.append(z3.Or(z3.Not(get_b(f'held_{n0}')), z3.Not(get_b(f'l_e3_{n1}'))))
            # ~locked_epochX(N1) | ~ep_epochX(N0)
            for e in ['1', '2', '3']:
                invars.append(z3.Or(z3.Not(get_b(f'l_e{e}_{n1}')), z3.Not(get_b(f'ep_{n0}_e{e}'))))

        # --- Simple Epoch/Locked/Held Consistency ---
        for n in ['n0', 'n1']:
            invars.append(z3.Or(get_b(f'held_{n}'), z3.Not(get_b(f'ep_{n}_e3'))))
            invars.append(z3.Or(get_b(f'ep_{n}_e3'), z3.Not(get_b(f'l_e3_{n}'))))
            invars.append(z3.Or(get_b(f'held_{n}'), z3.Not(get_b(f'l_e3_{n}'))))
            # locked_epoch1 | ~ep_epoch1
            invars.append(z3.Or(get_b(f'l_e1_{n}'), z3.Not(get_b(f'ep_{n}_e1'))))
            # ~ep_epoch2 | locked_epoch2
            invars.append(z3.Or(z3.Not(get_b(f'ep_{n}_e2')), get_b(f'l_e2_{n}')))
            # ~ep_epoch3 | locked_epoch3
            invars.append(z3.Or(z3.Not(get_b(f'ep_{n}_e3')), get_b(f'l_e3_{n}')))
            # ep_epoch0 exclusions
            invars.append(z3.Or(z3.Not(get_b(f'ep_{n}_e0')), z3.Not(get_b(f'l_e1_{n}'))))
            invars.append(z3.Or(z3.Not(get_b(f'l_e2_{n}')), z3.Not(get_b(f'ep_{n}_e0'))))
            invars.append(z3.Or(z3.Not(get_b(f'ep_{n}_e0')), z3.Not(get_b(f'l_e3_{n}'))))
            # ep_epoch1 exclusions
            invars.append(z3.Or(z3.Not(get_b(f'l_e2_{n}')), z3.Not(get_b(f'ep_{n}_e1'))))
            invars.append(z3.Or(z3.Not(get_b(f'l_e3_{n}')), z3.Not(get_b(f'ep_{n}_e1'))))
            # ep_epoch2 exclusions
            invars.append(z3.Or(z3.Not(get_b(f'ep_{n}_e2')), z3.Not(get_b(f'l_e3_{n}'))))

        # --- Existentials (Exists NODE0) ---
        invars.append(z3.Or(z3.Not(get_b('held_n0')), z3.Not(get_b('held_n1'))))
        invars.append(z3.Or(get_b('l_e1_n0'), get_b('l_e1_n1')))
        invars.append(z3.Or(z3.Not(get_b('t_e2_n0')), z3.Not(get_b('t_e2_n1'))))
        invars.append(z3.Or(z3.Not(get_b('t_e3_n0')), z3.Not(get_b('t_e3_n1'))))
        invars.append(z3.Or(z3.Not(get_b('l_e1_n0')), z3.Not(get_b('l_e1_n1'))))
        invars.append(z3.Or(z3.Not(get_b('l_e2_n0')), z3.Not(get_b('l_e2_n1'))))
        invars.append(z3.Or(z3.Not(get_b('l_e3_n0')), z3.Not(get_b('l_e3_n1'))))

        # --- Global Mutual Exclusions (Cross-Node/Cross-Epoch) ---
        # ~transfer_e3 | ~transfer_e2 (any combination)
        invars.append(z3.Not(z3.And(z3.Or(get_b('t_e3_n0'), get_b('t_e3_n1')), 
                                    z3.Or(get_b('t_e2_n0'), get_b('t_e2_n1')))))
        
        # ~locked_e2 | ~transfer_e2
        invars.append(z3.Not(z3.And(z3.Or(get_b('l_e2_n0'), get_b('l_e2_n1')), 
                                    z3.Or(get_b('t_e2_n0'), get_b('t_e2_n1')))))
        
        # ~transfer_e2 | ~locked_e3
        invars.append(z3.Not(z3.And(z3.Or(get_b('t_e2_n0'), get_b('t_e2_n1')), 
                                    z3.Or(get_b('l_e3_n0'), get_b('l_e3_n1')))))

        # ~locked_e3 | ~transfer_e3
        invars.append(z3.Not(z3.And(z3.Or(get_b('l_e3_n0'), get_b('l_e3_n1')), 
                                    z3.Or(get_b('t_e3_n0'), get_b('t_e3_n1')))))

        # --- Held vs Transfers ---
        # ~held | ~transfer_e2
        invars.append(z3.Not(z3.And(z3.Or(get_b('held_n0'), get_b('held_n1')), 
                                    z3.Or(get_b('t_e2_n0'), get_b('t_e2_n1')))))
        # ~held | ~transfer_e3
        invars.append(z3.Not(z3.And(z3.Or(get_b('held_n0'), get_b('held_n1')), 
                                    z3.Or(get_b('t_e3_n0'), get_b('t_e3_n1')))))

        # --- Epoch vs Transfers ---
        # ~ep_e2 | ~transfer_e2
        invars.append(z3.Not(z3.And(z3.Or(get_b('ep_n0_e2'), get_b('ep_n1_e2')), 
                                    z3.Or(get_b('t_e2_n0'), get_b('t_e2_n1')))))
        # ~ep_e3 | ~transfer_e2
        invars.append(z3.Not(z3.And(z3.Or(get_b('ep_n0_e3'), get_b('ep_n1_e3')), 
                                    z3.Or(get_b('t_e2_n0'), get_b('t_e2_n1')))))
        # ~ep_e3 | ~transfer_e3
        invars.append(z3.Not(z3.And(z3.Or(get_b('ep_n0_e3'), get_b('ep_n1_e3')), 
                                    z3.Or(get_b('t_e3_n0'), get_b('t_e3_n1')))))

        # --- Mutual Exclusive Epochs ---
        for n in ['n0', 'n1']:
            e_pairs = [('e0','e1'), ('e0','e2'), ('e0','e3'), ('e1','e2'), ('e1','e3'), ('e2','e3')]
            for e1, e2 in e_pairs:
                invars.append(z3.Or(z3.Not(get_b(f'ep_{n}_{e1}')), z3.Not(get_b(f'ep_{n}_{e2}'))))

        # --- Existence of ~ep_epochX ---
        for e in ['e0', 'e1', 'e2', 'e3']:
            invars.append(z3.Or(z3.Not(get_b(f'ep_n0_{e}')), z3.Not(get_b(f'ep_n1_{e}'))))

        return invars

    # 1. FORWARD CHECK: Any reachable states excluded by invariants?
    violations = []
    for i, (state_var, bit_str) in enumerate(zip(states, reachable_bitstrings), 1):
        all_invariants = z3.And(*form_invariants(state_var))
        solver.push()
        solver.add(z3.Not(all_invariants))
        if solver.check() == z3.sat:
            violations.append((i, bit_str))
        solver.pop()

    if violations:
        print(f"--- VIOLATIONS OF INVARIANTS FOUND ({len(violations)}) ---")
        for v in violations:
            print(f"Bitstring: {v}")
            print(f"    {format_state_readable(v, atoms)}")
    else:
        print("--- NO VIOLATIONS: All provided states satisfy invariants. ---")

    # 2. REVERSE CHECK: Any unreachable states not excluded by invariants
    print("\n--- DISCOVERING ALL UNREACHABLE STATES NOT EXCLUDED BY INVARIANTS ---")
    solver.reset()
    solver.add(all_invariants)
    
    # Exclude the known reachable states
    for bit_str in reachable_bitstrings:
        solver.add(state != int(bit_str, 2))
    
    missing_states = []
    # Exhaustive loop
    while solver.check() == z3.sat:
        model = solver.model()
        found_val = model[state].as_long()
        found_str = f"{found_val:0{num_atoms}b}"
        
        missing_states.append(found_str)
        # Block this specific state from appearing again
        solver.add(state != found_val)

    if missing_states:
        print(f"Found {len(missing_states)} additional states that satisfy the invariants but weren't in reachability:")
        for m in missing_states:
            print(f"Bitstring: {m}")
            print(f"    {format_state_readable(m, atoms)}")
    else:
        print("No missing states found. Reachability list is exhaustive for these invariants.")
    
    print("\n========SUMMARY========\n")
    if violations:
        print(f"--- VIOLATIONS OF INVARIANTS FOUND ({len(violations)}) ---")
    else:
        print("--- NO VIOLATIONS: All provided states satisfy invariants. ---")
    if missing_states:
        print(f"Found {len(missing_states)} additional states that satisfy the invariants but weren't in reachability:")
    else:
        print("No missing states found. Reachability list is exhaustive for these invariants.")
    
    export_to_smtlib(solver)



if __name__ == "__main__":
    check_reach()