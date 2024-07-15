### Configure python3 include path in util.py

python_include_path=$1

echo "1. Checking if Python.h exists ...."
if ! ls "${python_include_path}/Python.h" > /dev/null 2>&1; then
  echo "File not found: ${python_include_path}/Python.h"
  exit 1
fi
echo ""

echo "2. Configuring python3 include path in util.py ...."
pattern="self.python_include_path"
new_pattern="self.python_include_path = '${python_include_path}'"

# Escape special characters in the replacement text
escaped_new_pattern=$(printf '%s\n' "$new_pattern" | sed 's/[\/&]/\\&/g')

# Use sed to replace lines containing the pattern, preserving the indentation
sed -i "/${pattern}/ {s/^\(\s*\).*/\1${escaped_new_pattern}/}" util.py 
echo ""

echo "3. Checking configuration ...."
grep "${new_pattern}" util.py
echo ""

