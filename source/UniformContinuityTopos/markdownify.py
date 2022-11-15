import fileinput

for line in fileinput.input():
    if line.startswith("\\begin{code}"):
        print("```agda")
    elif line.startswith("\\end{code}"):
        print("```")
    else:
        print(line, end="")
