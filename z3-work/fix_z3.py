import re
import sys

def fix_smt_file(input_filename, output_filename):
    with open(input_filename, 'r') as f:
        content = f.read()

    # Step 1: Remove all declare-const for Bool 
    content = re.sub(r'\(declare-const\s+[a-zA-Z0-9_]+\s+Bool\)', '', content)

    # Step 2: Swap the restrictive tactic for the default solver
    content = content.replace('(check-sat-using (then simplify bit-blast smt))', '(check-sat)')

    definitions = {}
    out_chars = []
    
    # Use re.compile to avoid creating massive string copies in the loop
    assert_pattern = re.compile(r'\(assert\s+\(\=\s+([a-zA-Z0-9_]+)\s+')
    
    i = 0
    while i < len(content):
        match = assert_pattern.match(content, i)
        if match:
            var_name = match.group(1)
            i = match.end()
            
            paren_count = 0
            expr_chars = []
            
            # Extract the expression by counting matching parentheses
            while i < len(content):
                char = content[i]
                expr_chars.append(char)
                if char == '(': 
                    paren_count += 1
                elif char == ')':
                    paren_count -= 1
                    if paren_count < 0:
                        expr_chars.pop()  # Remove the trailing ')' of the '='
                        i += 1
                        break
                i += 1
            
            definitions[var_name] = "".join(expr_chars).strip()
            
            # Consume trailing whitespace and the closing assert parenthesis
            while i < len(content) and content[i] in ' \n\r\t':
                i += 1
            if i < len(content) and content[i] == ')':
                i += 1
        else:
            out_chars.append(content[i])
            i += 1

    cleaned_text = "".join(out_chars)
    
    # Step 3: Topologically sort the definitions so dependencies are defined first
    defns_to_write = list(definitions.keys())
    written = set()
    sorted_defns = []
    
    while defns_to_write:
        progress = False
        for var in defns_to_write[:]:
            expr = definitions[var]
            # Find all words/identifiers in the expression
            words = set(re.findall(r'[a-zA-Z0-9_]+', expr))
            
            # Check if any dependencies have not been written yet
            if all(w not in defns_to_write for w in words):
                sorted_defns.append(var)
                written.add(var)
                defns_to_write.remove(var)
                progress = True
                
        if not progress:
            print(f"Warning: Cyclic dependency detected among variables: {defns_to_write}")
            sorted_defns.extend(defns_to_write)
            break

    # Step 4: Generate the new define-fun blocks
    define_blocks = []
    for var in sorted_defns:
        define_blocks.append(f"(define-fun {var} () Bool\n  {definitions[var]}\n)")
    
    defs_str = "\n".join(define_blocks) + "\n\n"
    
    # Insert the sorted definitions right before the final property check
    final_assert_idx = cleaned_text.rfind("(assert")
    if final_assert_idx != -1:
        final_output = cleaned_text[:final_assert_idx] + defs_str + cleaned_text[final_assert_idx:]
    else:
        final_output = cleaned_text + defs_str
        
    # Clean up excess whitespace
    final_output = re.sub(r'\n\s*\n\s*\n', '\n\n', final_output)

    with open(output_filename, 'w') as f:
        f.write(final_output)

    print(f"Success! Safely ordered file saved as: {output_filename}")

if __name__ == "__main__":
    if len(sys.argv) != 3:
        print("Usage: python fix_z3.py <input.smt2> <output.smt2>")
    else:
        fix_smt_file(sys.argv[1], sys.argv[2])