
class ProgramVerifierAndEquivalenceChecker:
    def __init__(self):
        # To keep track of latest versions for each variable.
        self.variable_versions = {}

        # List to store ssa output.
        self.ssa_lines = []

        # List to store unrolled code lines.
        self.unrolled_code_lines = []

    # Function updates the variable to add the counter.
    def new_variable_with_count(self, lefthandsideVar):
        ssa_var = f"{lefthandsideVar}{self.variable_versions[lefthandsideVar]}"
        return ssa_var


    def convert_into_ssa(self, code_lines):
        for line in code_lines:
            # Assignments e.g x := 5
            if ":=" in line:
                # Split the line at the first encounter of := to otain the LHS - the variable and the RHS.
                lefthandsideVar, righthandsideEq = line.split(":=", 1)
                # Using strip to remove any leading or trailing whitespaces.
                lefthandsideVar = lefthandsideVar.strip()
                righthandsideEq = righthandsideEq.strip()
                # if the variable already exists in the dict then increment it's count,
                # Otherwise at it in the dict with count starting from 0.
                if lefthandsideVar in self.variable_versions:
                    self.variable_versions[lefthandsideVar] += 1 
                else:
                    self.variable_versions[lefthandsideVar] = 0
                
                ssa_var = self.new_variable_with_count(lefthandsideVar)
                # Add the line in the Single Static Assignment Lines after combing both the LHS and the RHS.
                ssa_line = f"{ssa_var} := {righthandsideEq}"
                self.ssa_lines.append(ssa_line)
                 

