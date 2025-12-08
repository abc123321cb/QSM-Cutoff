import itertools

MY_INVARIANT = ("forall NODE0, NODE1. (NODE0 = NODE1) | ~p(NODE0) | ~p(NODE1) | "
"(exists NODE2, NODE3. (NODE2 ~= NODE3 & q(NODE2) & q(NODE3))")

NEGATION = ("exists NODE0, NODE1. NODE0 ~= NODE1 & p(NODE0) & p(NODE1) & "
"forall NODE2, NODE3. ((NODE2 ~= NODE3) -> ~q(NODE2) | ~q(NODE3))")

NEGATION_2 = ()

MY_INV_CLAUSE = ("exists NODE0, NODE1. NODE0 ~= NODE1 & p(NODE0) & p(NODE1) & "
"~exists NODE2, NODE3. (NODE2 ~= NODE3 & q(NODE2) & q(NODE3))")


def main():
    INV_CLAUSE = "p(NODE0) & p(NODE1) & ~q(NODE0) & ~q(NODE2)"


    CLAUSES  = {
    ('p(node0)', 'p(node1)', '~q(node0)', '~q(node1)'),
    ('p(node0)', 'p(node2)', '~q(node0)', '~q(node2)'),
    ('p(node1)', 'p(node2)', '~q(node1)', '~q(node2)'),
    ('p(node0)', 'p(node2)', '~q(node0)', '~q(node1)'),
    ('p(node0)', 'p(node1)', '~q(node0)', '~q(node2)'),
    ('p(node1)', 'p(node2)', '~q(node0)', '~q(node1)'),
    ('p(node0)', 'p(node1)', '~q(node1)', '~q(node2)'),
    ('p(node1)', 'p(node2)', '~q(node0)', '~q(node2)'),
    ('p(node0)', 'p(node2)', '~q(node1)', '~q(node2)'),
    }
    
    #joined_clauses = [" & ".join(inner) for inner in CLAUSE_LIST]



    CONSTRAINT = "(NODE0 ~= NODE1 | NODE0 = NODE2) & (NODE0 ~= NODE1 | NODE0 ~= NODE2)"

    # normalize it to Python syntax
    expr = CONSTRAINT.replace("~=", "!=").replace(" = ", " == ").replace("&", "and").replace("|", "or")

    values = [0,1,2]

    seen_clauses = set()

    print(f"Invariant: {INV_CLAUSE}")
    print(f"Constraint: {CONSTRAINT}")

    c = 1

    for NODE0, NODE1, NODE2 in itertools.product(values, repeat=3):
        #if NODE1 < NODE0 or NODE2 < NODE0: continue
        NODES = [NODE0, NODE1, NODE2]
        inv = INV_CLAUSE
        for i in values:
            inv = inv.replace(
                f"NODE{i}", f"node{NODES[i]}")
        inv = inv.split(" & ")

        sorted_inv = tuple(sorted(inv))
        if sorted_inv in seen_clauses:
            #print(f"Ignoring {inv}, same as {sorted_inv}")
            continue
        else: seen_clauses.add(sorted_inv)

        if eval(expr):  # evaluates using current NODE0, NODE1, NODE2

            if sorted_inv in CLAUSES:
                print(f"{c}: {sorted_inv}: CORRECT ✅")
            else:
                print(f"{c}: {sorted_inv}: INCORRECT ❌")
        else:
            print(f"{c}: {sorted_inv}: DON'T CARE🤷")
        c += 1
    
    print("Unseen clauses:")
    for clause in CLAUSES - seen_clauses:
        print(f"{clause}")




if __name__ == "__main__":
    main()