import itertools

def main():
    INVARIANT = "p(NODE1) & ~q(NODE0) & p(NODE0) & ~q(NODE2)"

    expr = "(NODE0 ~= NODE1 | NODE0 = NODE2) & (NODE0 ~= NODE1 | NODE0 ~= NODE2)"

    # normalize it to Python syntax
    expr = expr.replace("~=", "!=").replace(" = ", " == ").replace("&", "and").replace("|", "or")

    values = ["n0", "n1", "n2"]

    for NODE0, NODE1, NODE2 in itertools.product(values, repeat=3):
        i = INVARIANT.replace("NODE0", NODE0).replace("NODE1", NODE1).replace("NODE2", NODE2)

        if eval(expr):  # evaluates using current NODE0, NODE1, NODE2
            print(f"{i}: VALID ✅")
        else:
            print(f"{i}: INVALID ❌")


if __name__ == "__main__":
    main()