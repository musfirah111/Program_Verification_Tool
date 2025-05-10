from program_analyzer import ProgramEquivalenceChecker

def test_equivalence_checker():
    checker = ProgramEquivalenceChecker()

    print("===== Test Case 1: Equivalent Programs =====")
    program1 = [
        "x := 0",
        "x := x + 1",
        "x := x + 2"
    ]

    program2 = [
        "x := 0",
        "x := x + 3"
    ]

    result, _ = checker.check_program_equivalence(program1, program2)
    print("Are Programs Equivalent?", result)
    print("\n")

    print("===== Test Case 2: Non-Equivalent Programs =====")
    program3 = [
        "x := 0",
        "x := x + 1",
        "x := x + 2"
    ]

    program4 = [
        "x := 0",
        "x := x + 4"
    ]

    result, _ = checker.check_program_equivalence(program3, program4)
    print("Are Programs Equivalent?", result)

if __name__ == "__main__":
    test_equivalence_checker()
