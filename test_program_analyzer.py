from program_analyzer import ProgramVerifierAndEquivalenceChecker

code_lines = [
    "x := 3;",
    "if (x < 5) {",
    "y := x + 1;",
    "} else {",
    "y := x - 1;",
    "}",
    "assert(y > 0);"
]

analyzer = ProgramVerifierAndEquivalenceChecker()
analyzer.convert_into_ssa(code_lines)
for line in analyzer.ssa_lines:
    print(line) 

# text = "x := 5"
# result = text.split(":=", 1)
# print(result)