class ProgramVerifierAndEquivalenceChecker:
    def __init__(self):
        # To keep track of latest versions for each variable.
        self.variable_versions = {}
        # {'x': 2 } means there is x0, x1, x2

        # List to store ssa output.
        self.ssa_lines = []

        # List to store unrolled code lines.
        self.unrolled_code_lines = []

        # Counter for condition numbers.
        self.condition_counter = 0

    # Function updates the variable to add the counter.
    def new_variable_with_count(self, left_hand_side_var):
        ssa_var = f"{left_hand_side_var}{self.variable_versions[left_hand_side_var]}"
        return ssa_var
    
    # Helper function to get current version number of a variable.
    def get_current_variable_version(self, variable):
        return self.variable_versions.get(variable, 0)

    # Function to get unroll depth from loop condition.
    def extract_unroll_depth(self, condition_line):
        if '<' in condition_line:
            # SPlit the condition into two parts arounf the less than (<) sign.
            parts = condition_line.split('<')

            # Check if the condition had exactly two parts.
            if len(parts) == 2:
                right_side = parts[1]
                if right_side.isdigit():
                    return int(right_side)
                
        if '>' in condition_line:
            parts = condition_line.split('>')
            if len(parts) == 2:
                left_side = parts[0]
                if left_side.isdigit():
                    return int(left_side)
                
        return 4
    
    # Function to unroll while loop.
    def unroll_while_loop_and_ssa(self, condition, loop_body, unroll_depth):
        # Store curret versions of variables before loop starts.
        saved_variable_versions = {}
        for variable in self.variable_versions:
            saved_variable_versions[variable] = self.get_current_variable_version(variable)

        # List for new versions.
        loop_variable_versions = []

        # Unroll loop.
        for i in range(unroll_depth):
            self.condition_counter += 1
            condition_number = self.condition_counter

            # Replace the variable names in condition with versions.
            cond_parts = condition.split()
            updated_condition = []

            for part in cond_parts:
                if part in self.variable_versions:
                    version = self.get_current_variable_version(part)
                    updated_condition.append(f"{part}{version}")
                else:
                    updated_condition.append(part)

            # Merge the updated words into a single string.
            condition_new = "".join(updated_condition)

            # Format the condition and add it to SSA output list.
            condition_line = "φ" + str(condition_number) + " = (" + condition_new + ")"
            self.ssa_lines.append(condition_line)

            # Store versions before loop body execuion.
            previous_versions = self.variable_versions.copy()

            # Loop body execution.
            for line in loop_body:
                if ":=" in line:
                    left_hand_side_var, right_hand_side_var = line.split(":=", 1)

                    # Remove whitespaces.
                    left_hand_side_var = left_hand_side_var.strip()
                    right_hand_side_var = right_hand_side_var.strip() 

                    if left_hand_side_var in self.variable_versions:
                        self.variable_versions[left_hand_side_var] += 1
                    else:
                        self.variable_versions[left_hand_side_var] = 0

                    ssa_var = self.new_variable_with_count(left_hand_side_var)
                    ssa_line = f"{ssa_var} := {right_hand_side_var}"
                    self.ssa_lines.append(ssa_line)

                    # Changes for backtracking.
                    loop_variable_versions.append({
                        "condition": condition_number,
                        "variable": left_hand_side_var,
                        "true_version": self.variable_versions[left_hand_side_var],
                        "false_version": previous_versions.get(left_hand_side_var, 0)
                    })

        # Reverse the list so we process changes in the right order.
        loop_variable_versions.reverse()

        # For coniditons already handled.
        done_conditions = set()

        # Iterate through every saved var change.
        for change in loop_variable_versions:
            if change["condition"] not in done_conditions:

                # Get the variable name that changed.
                variable = change["variable"]

                # Increase the version of that var.
                self.variable_versions[variable] += 1

                new_versioned_name = self.new_variable_with_count(variable)

                # new_variable := φcondition_number ? true_version : false_version
                cond_backtrack_line = (
                    f"{new_versioned_name} := φ{change['condition']} ? "
                    f"{variable}{change['true_version']} : {variable}{change['false_version']}"
                )


                self.ssa_lines.append(cond_backtrack_line)
                done_conditions.add(change["condition"])

    def convert_into_ssa(self, code_lines):
        for i, line in enumerate(code_lines):
            # Assignments e.g x := 5
            if ":=" in line:
                # Split the line at the first encounter of := to otain the LHS - the variable and the RHS.
                left_hand_side_var, righthandsideEq = line.split(":=", 1)
                # Using strip to remove any leading or trailing whitespaces.
                left_hand_side_var = left_hand_side_var.strip()
                righthandsideEq = righthandsideEq.strip()
                # if the variable already exists in the dict then increment it's count,
                # Otherwise at it in the dict with count starting from 0.
                if left_hand_side_var in self.variable_versions:
                    self.variable_versions[left_hand_side_var] += 1 
                else:
                    self.variable_versions[left_hand_side_var] = 0
                
                ssa_var = self.new_variable_with_count(left_hand_side_var)
                # Add the line in the Single Static Assignment Lines after combing both the LHS and the RHS.
                ssa_line = f"{ssa_var} := {righthandsideEq}"
                self.ssa_lines.append(ssa_line)

            # while loop.
            if line.startswith("while"):
                # Extract the condition which is between ( and ).
                start = line.find("(")
                end = line.find(")")
                condition = line[start + 1:end]

                unroll_depth = self.extract_unroll_depth(condition)

                # Unroll while loop.
                loop_body = []
                bracket_count = 1
                j = i + 1

                # Keep adding loop lines to body until the matching closing bracket is found.
                while j < len(code_lines) and bracket_count > 0:
                    loop_line = code_lines[j]
                    if "{" in loop_line:
                        bracket_count += 1
                    if "}" in loop_line:
                        bracket_count -= 1
                    if bracket_count > 0 and ":=" in loop_line:
                        loop_body.append(loop_line)
                    j += 1

                # Unroll while loop.
                self.unroll_while_loop_and_ssa(condition, loop_body, unroll_depth)

if __name__ == "__main__":
    code_lines = [
        "x := 0;",
        "while (x < 4) {",
        "    x := x + 1;",
        "}",
        "assert(x == 4);"
    ]

    verifier = ProgramVerifierAndEquivalenceChecker()
    verifier.convert_into_ssa(code_lines)
    for line in verifier.ssa_lines:
        print(line)

                 

