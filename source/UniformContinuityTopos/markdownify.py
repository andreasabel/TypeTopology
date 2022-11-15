import fileinput
import re

for line in fileinput.input():
    if line.startswith("\\begin{code}"):
        print("```agda")
    elif line.startswith("\\end{code}"):
        print("```")
    elif line.startswith("\\section{"):
        m = re.match(r"\\section{([^A-Za-z0-9 ]+)}", line)
        print("## {}".format(m.groups()[0]))
    else:
        print(line, end="")
