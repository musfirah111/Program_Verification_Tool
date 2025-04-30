
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
    def new_variable_with_count(self, lefthandsideVar):
        ssa_var = f"{lefthandsideVar}{self.variable_versions[lefthandsideVar]}"
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
    def unroll_while_loop(self, condition, loop_body, unroll_depth):
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

                    

    def convert_into_ssa(self, code_lines):
        for i, line in enumerate(code_lines):
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

            # while loop.
            if line.startWith("while"):
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
                self.unroll_while_loop(condition, loop_body, unroll_depth)

                 

