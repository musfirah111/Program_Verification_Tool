from z3 import Solver, Int, If, sat

############################################################# Class for program verification.
from z3 import Solver, Int, If, sat

class ProgramVerifier:
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

        # Dictionary to track array index values and their updates
        # Format: {outer_iter: {inner_iter: {index: {prev_value: val, new_value: val}}}}
        self.array_index_tracker = {}

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
                right_side = parts[1]
                if right_side.isdigit():
                    return int(right_side)
                
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
            print(f"Line 78: Added to ssa_lines:", condition_line)

            # Store versions before loop body execuion.
            previous_versions = self.variable_versions.copy()

            # Loop body execution.
            for line in loop_body:
                if ":=" in line:
                    # left_hand_side_var, right_hand_side_var = line.split(":=", 1)

                    # # Remove whitespaces.
                    # left_hand_side_var = left_hand_side_var.strip()
                    # right_hand_side_var = right_hand_side_var.strip() 

                    # if left_hand_side_var in self.variable_versions:
                    #     self.variable_versions[left_hand_side_var] += 1
                    # else:
                    #     self.variable_versions[left_hand_side_var] = 0

                    # ssa_var = self.new_variable_with_count(left_hand_side_var)
                    # ssa_line = f"{ssa_var} := {right_hand_side_var}"
                    # self.ssa_lines.append(ssa_line)

                    ssa_line, var = self.ssa_assignment(line)
                    self.ssa_lines.append(ssa_line)
                    print(f"Line 102: Added to ssa_lines:", ssa_line)

                    # Changes for backtracking.
                    loop_variable_versions.append({
                        "condition": condition_number,
                        "variable": var,
                        "true_version": self.variable_versions[var],
                        "false_version": previous_versions.get(var, 0)
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
                print(f"Line 137: Added to ssa_lines:", cond_backtrack_line)
                done_conditions.add(change["condition"])


    # Function to handle increment statements
    def handle_increment_statement(self, increment_statement):
        if ":=" in increment_statement:
            increment_variable, increment_expression = increment_statement.split(":=", 1)
            increment_variable = increment_variable.strip()
            increment_expression = increment_expression.strip()

            increment_version = self.get_current_variable_version(increment_variable)

            increment_value = 1  # Default increment value

            if increment_variable == 'i':
                if increment_variable in self.variable_versions:
                    self.variable_versions[increment_variable] += 1
                else:
                    self.variable_versions[increment_variable] += 0

            # Check for post-increment (e.g., j++)
            if increment_expression == f"{increment_variable}++":
                incremented_value = f"{increment_variable}{increment_version}"
            else:
                # Check for other forms like j + constant
                parts = increment_expression.split("+")
                if len(parts) == 2:
                    incremented_variable = parts[0].strip()
                    constant_part = parts[1].strip()

                    if constant_part.isdigit():
                        increment_value = int(constant_part)

                    incremented_value = f"{incremented_variable}{increment_version} + {increment_value}"

            # Create SSA assignment for the increment
            incremented_ssa_line = f"{increment_variable}{increment_version + 1} := {incremented_value}"
            self.ssa_lines.append(incremented_ssa_line)
            # print("########### variable", increment_variable)
            # print("########### expression", increment_expression)
            # print("########### version", increment_version)
            print("PRINTING INSIDE FUNCTION ", incremented_ssa_line)

    # Function to handle initialization statements
    def handle_init_statement(self, init_statement):
        if ":=" in init_statement:
            variable_name, constant_value = init_statement.split(":=", 1)
            variable_name = variable_name.strip()
            constant_value = constant_value.strip()

            # Increment the version for the variable
            if variable_name in self.variable_versions:
                self.variable_versions[variable_name] += 1
            else:
                self.variable_versions[variable_name] = 0

            # Create SSA variable
            ssa_var = self.new_variable_with_count(variable_name)
            ssa_line = f"{ssa_var} := {constant_value}" 
            #self.ssa_lines.append(ssa_line)
            print("INSIDE FUNCTION -> HANDLING INTIALIZATION", ssa_line)
     
    # Function to create phi assignment for loop conditions
    def create_phi_assignment(self, loop_condition, condition_counter):
        condition_number = condition_counter + 1  
        self.condition_counter = condition_number 

        phi_var = f"φ{condition_number}"
        
        # Parse the loop condition to separate variables and constants
        condition_parts = loop_condition.split("<")
        left_side = condition_parts[0].strip()  # e.g., j
        right_side = condition_parts[1].strip()  # e.g., n - i - 1

        # Process the left side to get the current version
        left_version = self.get_current_variable_version(left_side)
        left_side = f"{left_side}{left_version}"  # Update left side to include version

        # Process the right side 
        right_side_parts = right_side.split()
        updated_right_side = []

        for part in right_side_parts:
            if part.isidentifier():  # Check if it's a variable
                if part == 'n':
                    updated_right_side.append(f"{part}0")  # Always use n0
                else:
                    version = self.get_current_variable_version(part)
                    updated_right_side.append(f"{part}{version}")  
            elif part.isdigit():  
                updated_right_side.append(part) 
            else:
                updated_right_side.append(part)  # Keep operators and other parts

        # Join the updated right side
        updated_right_side_str = " ".join(updated_right_side)
        updated_condition = f"{left_side} < {updated_right_side_str}"

        # Create phi assignment
        phi_assignment = f"{phi_var} = ({updated_condition})" 
        self.ssa_lines.append(phi_assignment) 
        print("INSIDE FUNCTION -> CREATING PHI ASSIGNMENT", phi_assignment)
        return phi_assignment
        
    def UpdatingVariablesVersions(self, variable_name):
         # Increment the version for the variable
            if variable_name in self.variable_versions:
                self.variable_versions[variable_name] += 1
            else:
                self.variable_versions[variable_name] = 0

    def AddingToVariableVersions(self, variable_name):
        if variable_name not in self.variable_versions:
            self.variable_versions[variable_name] = 0

    # function to unrol nested for loop 
    def unroll_for_loop_and_ssa(self, condition, loop_body, unroll_depth):
        # Parse the outer for loop condition
        parts = condition.split(";")
        init_statement = parts[0].strip()  # e.g., i := 0
        loop_condition = parts[1].strip()  # e.g., i < n
        incr_statement = parts[2].strip()   # e.g., i := i + 1

        # Handle initialization and phi assignment
        self.handle_init_statement(init_statement)

        # Dictionary to store previous iteration values
        prev_iteration_values = set()
        
        # Unroll the outer loop
        for i in range(unroll_depth - 1):
            print("@@@@@@@@@@@OUTER LOOP ITERATION,@@@@@@@@@", i)
            self.array_index_tracker[i] = {}  # Initialize tracker for this outer iteration

           
            phi_assignment = self.create_phi_assignment(loop_condition, self.condition_counter)
            prev_iteration_values.add(phi_assignment)
            print(prev_iteration_values)

            # Handle the inner loop
            inner_condition = ""
            inner_loop_body = []

            for line in loop_body:
                line = line.strip()
                if line.startswith("for"):
                    # Extract inner loop condition and body
                    start = line.find('(') + 1
                    end = line.find(')', start)
                    inner_condition = line[start:end].strip()
                    parts = [part.strip() for part in inner_condition.split(';')] 

                    self.extract_unroll_depth(inner_condition)

                    inner_init_statement = parts[0]  # j := 0
                    inner_loop_condition = parts[1]  # j < n - i - 1
                    inner_incr_statement = parts[2]  # j := j + 1

                    # Get inner loop body
                    inner_bracket_count = 1
                    k = -1
                    for idx, l in enumerate(loop_body):
                        if l.strip() == line.strip(): 
                            k = idx + 1
                            break

                    while k < len(loop_body) and inner_bracket_count > 0:
                        inner_line = loop_body[k]
                        if "{" in inner_line:
                            inner_bracket_count += 1
                        if "}" in inner_line:
                            inner_bracket_count -= 1
                        if inner_bracket_count > 0:
                            inner_loop_body.append(inner_line)
                        k += 1

            # Process inner loop unrolling
            for j in range(unroll_depth - i - 1):
                print("@@@@@@@@@@@INNER LOOP ITERATION,@@@@@@@@@", j)
                print(self.variable_versions)
                self.array_index_tracker[i][j] = {}  # Initialize tracker for this inner iteration
                
                # Handle inner loop initialization and phi assignment
                self.handle_init_statement(inner_init_statement)               
                self.create_phi_assignment(inner_loop_condition, self.condition_counter)

                # Handle other lines in the inner loop body
                for inner_line in inner_loop_body:
                    if "if" in inner_line:
                        start = inner_line.find("(")
                        end = inner_line.find(")")
                        if_condition = inner_line[start + 1:end].strip()

                        if "[" in inner_line and "]" in inner_line:
                            for cond in ['<', '>', '<=', '>=', '==', '!=']:
                                if cond in if_condition:
                                    parts = if_condition.split(cond)
                                    left_array = parts[0].strip()
                                    right_array = parts[1].strip()

                                    if "[" in left_array:
                                        # Parse array accesses
                                        left_array_parts = left_array.split("[")
                                        left_array_name = left_array_parts[0].strip()
                                        left_index = left_array_parts[1].split("]")[0].strip()
                                        
                                        right_array_parts = right_array.split("[")
                                        right_array_name = right_array_parts[0].strip()
                                        right_index = right_array_parts[1].split("]")[0].strip()

                                        print("LEFT INDEX", left_index)
                                        print("RIGHT INDEX", right_index)

                                        print("left array name", left_array_name)
                                        print("right array name",right_array_name)

                                        # Evaluate indices
                                        left_index = left_index.replace('j', str(j))
                                        right_index = right_index.replace('j', str(j))
                                        right_index = right_index.replace('+1', '')
                                        right_index = str(int(right_index) + 1)

                                        print("LEFT INDEX: -------------", left_index)
                                        print("RIGHT INDEX: -------------", right_index)

                                        # Get current versions for previous values
                                        left_prev_version = self.get_current_variable_version(f"{left_array_name}{left_index}")
                                        right_prev_version = self.get_current_variable_version(f"{right_array_name}{right_index}")

                                        # Track array indices and their values
                                        if left_index not in self.array_index_tracker:
                                            self.array_index_tracker[i][j][left_index] = {
                                                'prev_value': f"{left_array_name}{left_index}_{left_prev_version}",
                                                'new_value': None  # Will be updated after swap
                                            }

                                        if right_index not in self.array_index_tracker[i][j]:
                                            self.array_index_tracker[i][j][right_index] = {
                                                'prev_value': f"{right_array_name}{right_index}_{right_prev_version}",
                                                'new_value': None  # Will be updated after swap
                                            }

                                        #CONSIDERING EACH ARRAY INDEX AS A VARIBALE AND ADDING IT TI VARIABLE VERIONS DICT.
                                        left_array_name = f"{left_array_name}{left_index}"
                                        right_array_name = f"{right_array_name}{right_index}"
                                        
                                        self.AddingToVariableVersions(left_array_name)
                                        self.AddingToVariableVersions(right_array_name)

                                        # Get current versions
                                        left_version = self.get_current_variable_version(left_array_name)
                                        right_version = self.get_current_variable_version(right_array_name)
                                        print("LEFT", left_version)
                                        print("RIGHT", right_version)
                                        
                                        # Create array accesses
                                        left_array_access = f"{left_array_name}_{left_version}"
                                        right_array_access = f"{right_array_name}_{right_version}"

                                        # Create condition line
                                        self.condition_counter += 1
                                        condition_number = self.condition_counter
                                        condition_line = f"φ{condition_number} = ({left_array_access} > {right_array_access})"
                                        print("condition_line", condition_line)
                                        self.ssa_lines.append(condition_line)

                                        # Handle temp variable and swaps
                                        if 'temp' in self.variable_versions:
                                            self.variable_versions['temp'] += 1
                                        else:
                                            self.variable_versions['temp'] = 0

                                        temp_version = self.get_current_variable_version('temp')
                                        temp_var = f"temp{temp_version}"
                                        print(f"{temp_var} := {left_array_access}")
                                        self.ssa_lines.append(f"{temp_var} := {left_array_access}")

                                        self.UpdatingVariablesVersions(left_array_name)
                                        self.UpdatingVariablesVersions(right_array_name)

                                        left_version = self.get_current_variable_version(left_array_name)
                                        right_version = self.get_current_variable_version(right_array_name)

                                        new_left_access = f"{left_array_name}_{left_version}"
                                        new_right_access = f"{right_array_name}_{right_version}"
                                        
                                       
                                        self.ssa_lines.append(f"{new_left_access} := {right_array_access}")
                                        print(f"#########################{new_left_access} := {right_array_access}")
                                        self.ssa_lines.append(f"{new_right_access} := {temp_var}")
                                        print(f"#########################{new_right_access} := {temp_var}")

                                        self.UpdatingVariablesVersions(left_array_name)
                                        self.UpdatingVariablesVersions(right_array_name)

                                        left_version = self.get_current_variable_version(left_array_name)
                                        right_version = self.get_current_variable_version(right_array_name)

                                        
                                        new_cond_left_access = f"{left_array_name}_{left_version}"
                                        new_cond_right_access = f"{right_array_name}_{right_version}"

                                        # Update the new values in the tracker
                                        self.array_index_tracker[i][j][left_index]['new_value'] = new_cond_left_access
                                        self.array_index_tracker[i][j][right_index]['new_value'] = new_cond_right_access
                                        
                                        self.ssa_lines.append(f"{new_cond_left_access} := φ{condition_number} ? {new_left_access} : {left_array_access}")
                                        self.ssa_lines.append(f"{new_cond_right_access} := φ{condition_number} ? {new_right_access} : {right_array_access}")
                                        print(f"{new_cond_left_access} := φ{condition_number} ? {new_left_access} : {left_array_access}")
                                        print(f"{new_cond_right_access} := φ{condition_number} ? {new_right_access} : {right_array_access}")

                self.handle_increment_statement(inner_incr_statement)
    
            self.handle_increment_statement(incr_statement)

        self.backtracking(prev_iteration_values)
        
            
    def backtracking(self, prev_iteration_values):
        print("\n@@@@@@@@@@@FINAL ARRAY INDEX TRACKER STATE@@@@@@@@@@@")
        print("Array Index Tracker:")
        
        # Dictionary to store consolidated backtracking assignments
        # Key: (phi_var, base_var) tuple, Value: (latest_new_value, earliest_prev_value)
        consolidated_assignments = {}
        
        # Find the maximum outer iteration to start with
        max_outer_iter = max(self.array_index_tracker.keys())
        
        # Loop through outer iterations from max to 0
        for outer_iter in range(max_outer_iter, -1, -1):
            print(f"\nOuter Iteration {outer_iter}:")
            
            # Find the phi assignment for this outer iteration
            phi_var = None
            for phi in prev_iteration_values:
                if f"φ" in phi and f"i{outer_iter}" in phi:
                    phi_var = phi.split('=')[0].strip()
                    print(f"  Phi Assignment: {phi}")
                    break
            
            if not phi_var:
                continue  # Skip if no phi variable found for this iteration
                
            # Process all inner iterations for this outer iteration
            for inner_iter in self.array_index_tracker[outer_iter]:
                print(f"  Inner Iteration {inner_iter}:")
                
                for index in self.array_index_tracker[outer_iter][inner_iter]:
                    tracker_info = self.array_index_tracker[outer_iter][inner_iter][index]
                    print(f"    Index {index}:")
                    print(f"      Previous Value: {tracker_info['prev_value']}")
                    print(f"      New Value: {tracker_info['new_value']}")
                    
                    # Get the base variable
                    base_var = tracker_info['prev_value'].split('_')[0]
                    
                    # Create a key for consolidated assignments
                    key = (phi_var, base_var)
                    
                    # Update the consolidated assignments
                    if key in consolidated_assignments:
                        # Keep the latest new_value and earliest prev_value
                        current_new, current_prev = consolidated_assignments[key]
                        
                        # Extract version numbers for comparison
                        new_version = int(tracker_info['new_value'].split('_')[1]) if '_' in tracker_info['new_value'] else 0
                        current_new_version = int(current_new.split('_')[1]) if '_' in current_new else 0
                        
                        prev_version = int(tracker_info['prev_value'].split('_')[1]) if '_' in tracker_info['prev_value'] else 0
                        current_prev_version = int(current_prev.split('_')[1]) if '_' in current_prev else 0
                        
                        # Update with latest new_value
                        if new_version > current_new_version:
                            consolidated_assignments[key] = (tracker_info['new_value'], current_prev)
                        
                        # Update with earliest prev_value
                        if prev_version < current_prev_version:
                            consolidated_assignments[key] = (consolidated_assignments[key][0], tracker_info['prev_value'])
                    else:
                        consolidated_assignments[key] = (tracker_info['new_value'], tracker_info['prev_value'])
                    
                    print(f"      Consolidated: {base_var} with {phi_var} ? {consolidated_assignments[key][0]} : {consolidated_assignments[key][1]}")
        
        # Generate final backtracking assignments
        backtracking_assignments = []
        for (phi_var, base_var), (new_value, prev_value) in consolidated_assignments.items():
            # Update the version for the final variable
            self.UpdatingVariablesVersions(base_var)
            new_version = self.get_current_variable_version(base_var)
            new_var = f"{base_var}_{new_version}"
            
            backtracking_line = f"{new_var} = {phi_var} ? {new_value} : {prev_value}"
            backtracking_assignments.append(backtracking_line)
            self.ssa_lines.append(backtracking_line)
            print(f"Final Backtracking: {backtracking_line}")
        
        print("\n@@@@@@@@@@@END OF ARRAY INDEX TRACKER@@@@@@@@@@@\n")

        return backtracking_assignments   
    
    def ssa_assignment(self, line):
        # Check if the line contains the assignment operator
        if ":=" not in line:
            raise ValueError(f"Invalid assignment line: {line}")

        # Split the line at the first encounter of := to obtain the LHS - the variable and the RHS.
        equation = line.split(":=", 1)
        lefthandsideVar = equation[0].strip()
        righthandsideEq = equation[1].strip()

        # Check for redundant assignment (left side equals right side)
        if righthandsideEq == lefthandsideVar:
            return None, lefthandsideVar  # Skip this assignment

        for letter in righthandsideEq:
            if letter in self.variable_versions:
                righthandsideEq = righthandsideEq.replace(letter, self.new_variable_with_count(letter))

        # Increment the version for the left-hand side variable
        if lefthandsideVar in self.variable_versions:
            self.variable_versions[lefthandsideVar] += 1 
        else:
            self.variable_versions[lefthandsideVar] = 0
        
        ssa_var = self.new_variable_with_count(lefthandsideVar)

        # Add the line in the Single Static Assignment Lines after combining both the LHS and the RHS.
        ssa_line = f"{ssa_var} := {righthandsideEq}"
        self.ssa_lines.append(ssa_line)
        print(f"Line 454: Added to ssa_lines:", ssa_line)

        return ssa_line, lefthandsideVar
    
     # Function to extract the loop conditions and also keep start of the iterator intialization.
    def extracting_loop_condtions(self, condition):
        # Extracting the intialization of iterator, condition and the incrementor.
        start = line.find('(') + 1
        end = line.find(')', start)
        # i = 0; i < n; i++
        inside = line[start:end]
        
        # Breaking the condition into three parts.
        parts = []

        for part in inside.split(';'):
            parts.append(part.strip())
        
        # x < 5 
        intialization = part[0]
        condition = parts[1]

        # split at < or > condition.
        if '<' in condition:
            lefthandsideVar = condition.split('<', 1)

        if lefthandsideVar in self.variable_versions:
            self.variable_versions[lefthandsideVar] += 1 
        else:
            self.variable_versions[lefthandsideVar] = 0
        
        ssa_var = self.new_variable_with_count(lefthandsideVar)
       

        # Add the line in the Single Static Assignment Lines after combing both the LHS and the RHS.
        # ssa_line = f"{ssa_var} < {righthandsideEq}"

        #return ssa_line, lefthandsideVar
        return lefthandsideVar

    def convert_into_ssa(self, code_lines):
        i = 0
        nested_for = False
        while_loop = False
        while i < len(code_lines):
            line = code_lines[i]
            # Assignments e.g x := 5
            if ":=" in line and not (line.strip().startswith("while") or line.strip().startswith("for") or line.strip().startswith("if")):
                ssa_line, var = self.ssa_assignment(line)
                self.ssa_lines.append(ssa_line)
                #print("##########HERE IN := ################")
            # If/else Block e.g if (x > 4)
            elif line.startswith("if"):
                if_branch_vars = {}
                else_branch_vars = {}
                start = line.find('(')
                end = line.find(')', start) + 1
                condition = line[start:end].strip()
                condition_var = "φ"

                if condition_var in self.variable_versions:
                    self.variable_versions[condition_var] += 1 
                else:
                    self.variable_versions[condition_var] = 0

                condition_var = self.new_variable_with_count(condition_var)

                # Find the variables used in the condition and update them to add a counter.
                for var in condition:
                    if var in self.variable_versions:
                        ssa_var = self.new_variable_with_count(var)
                        condition = condition.replace(var, ssa_var)
                
                ssa_line = f"{condition_var} = {condition}"
                self.ssa_lines.append(ssa_line)

                while i < len(code_lines) and "}" not in code_lines[i]:
                    if ":=" in code_lines[i]:
                        ssa_line, var_name = self.ssa_assignment(code_lines[i])
                        #print("##########HERE################")
                        self.ssa_lines.append(ssa_line)
                        # Store the new SSA version for this variable
                        if_branch_vars[var_name] = self.new_variable_with_count(var_name)
                    i += 1
                
                if "else" in code_lines[i]:
                    i += 1
                    while i < len(code_lines) and "}" not in line:
                        if ":=" in code_lines[i]:
                            ssa_line, var_name = self.ssa_assignment(code_lines[i])
                            #print("##########HERE################")
                            self.ssa_lines.append(ssa_line)
                            # Store the new SSA version for this variable
                            else_branch_vars[var_name] = self.new_variable_with_count(var_name)
                        i += 1

                #print(if_branch_vars)
                #print(else_branch_vars)

                # Merge variables updated in either branch
                all_updated_vars = set()
                for k in if_branch_vars.keys():
                    all_updated_vars.add(k)
                for k in else_branch_vars.keys():
                    all_updated_vars.add(k)

                for var in all_updated_vars:
                    self.variable_versions[var] += 1
                    
                    new_var = self.new_variable_with_count(var)
                    cond = self.new_variable_with_count("φ")
                    
                    if_var = if_branch_vars.get(var, self.new_variable_with_count(var))
                    else_var = else_branch_vars.get(var, self.new_variable_with_count(var))
                    
                    ssa_line = f"{new_var} = {cond} ? {if_var} : {else_var}"
                    
                    self.ssa_lines.append(ssa_line)

            # while loop.
            if line.startswith("while"):
                while_loop = True
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

            # Nested for loop and arrays.
            if line.startswith("for"):
                nested_for = True
                # Extract the condition which is between ( and )
                start = line.find("(")
                end = line.find(")")
                condition = line[start + 1:end]

                # Get loop body
                loop_body = []
                bracket_count = 1
                j = i + 1
                while j < len(code_lines) and bracket_count > 0:
                    loop_line = code_lines[j]
                    if "{" in loop_line:
                        bracket_count += 1
                    if "}" in loop_line:
                        bracket_count -= 1
                    if bracket_count > 0:
                        loop_body.append(loop_line)
                    j += 1

                # Extract unroll depth from condition
                unroll_depth = self.extract_unroll_depth(condition)
                # print("unroll:", unroll_depth)
            
                # Unroll the for loop
                self.unroll_for_loop_and_ssa(condition, loop_body, unroll_depth)
            
            if nested_for:
                i = j
            
            if while_loop:
                i += 1

    def get_versioned_variable(self, variable):
        if variable in self.variable_versions:
            return f"{variable}{self.variable_versions[variable]}"
        return variable  # case where the variable doesn't exist

############################################################# Class that changes SSA into SMT code.
class SSAToSMTCoverter:
    def __init__(self):

        # Format: {'ssa_variable_1': 'smt_variable_1',
        #          'ssa_variable_2': 'smt_variable_2'}
        # Example: {'y0': 'y0', 
        #           '@1': 'v1'}
        self.smt_variables = {}

        # Counter for unique conditions.
        self.new_condition_counter = 0

        # List to store the SMT assertions
        self.smt_assertions = []

        self.condition_mapping = {}  # φ-condition -> condX

    # Function to convert ssa assignment line in smt code.
    def convert_assignment_line_in_smt(self, ssa_line):
        condition_representation = "φ"

        left_part, right_part = ssa_line.split("=")
        left_part = left_part.strip()
        right_part = right_part.strip()

        # CHeck if it is a conditional assignment (has ?)
        # x5 := cond1 ? y : z
        if "?" in right_part:
            # Split the right part into condition and the other part.
            right_further_parts =  right_part.split("?")
            condition = right_further_parts[0].strip()
            remaining_part = right_further_parts[1].strip()

            # From the other part (y : z), extract true part (y) and false part (z)
            true_false_part = remaining_part.split(":")
            true_part = true_false_part[0].strip()
            false_part = true_false_part[1].strip()

            # Convert condition in smt.
            if condition.startswith(condition_representation):
                self.new_condition_counter += 1
                new_cond_var = f"cond{self.new_condition_counter}"
                self.smt_variables[condition] = new_cond_var
                condition_variable = new_cond_var
            
            # Create SMT assertion for conditional.
            smt_line = f"(assert (= {left_part} (ite {condition_variable} {true_part} {false_part})))"
            self.smt_assertions.append(smt_line)

        else:
            # Regular assignment: x := y + z or x := 5
            right_part = right_part.rstrip(';')
            
            # Convert arithmetic operations to SMT prefix notation.
            right_part = convert_infix_to_prefix(right_part)

            if "φ" in left_part:
                left_part = left_part.replace("φ", "cond")
            
            smt_line = f"(assert (= {left_part} {right_part}))"
            self.smt_assertions.append(smt_line)

    # Function to convert ssa into smt.
    def convert_ssa_to_smt(self, ssa_lines):
        # Iterate through every line in ssa.
        for line in ssa_lines:
            if '=' in line:
                parts = line.split('=')
                left_part = parts[0]
                left_part = left_part.strip() # Get the assigned variable.

                # Add this variable to smt variables if it is not already present there.
                if left_part not in self.smt_variables:
                    if "φ" in left_part:
                        left_part = left_part.replace("φ", "cond")
                        self.smt_variables[left_part] = left_part
                    else:
                        self.smt_variables[left_part] = left_part
        
        # Conert ssa assignment line to smt code.
        for line in ssa_lines:
            if '=' in line:
                self.convert_assignment_line_in_smt(line)

    # Function that returns list of smt code.
    def get_smt(self):
        smt_output = []

        for var in self.smt_variables.values():
            smt_output.append(f"(declare-const {var} Int)")

        for assertion in self.smt_assertions:
            smt_output.append(assertion)

        smt_output.append("(check-sat)")
        smt_output.append("(get-model)")

        return smt_output
    
# Function to convert infix expression into postfix.    
def convert_infix_to_prefix(expression):
    expression = expression.strip()

    if expression.startswith('(') and expression.endswith(')'):
        expression = expression[1:-1].strip()

    if '+' in expression:
        parts = expression.split('+')
        operator = '+'
    elif '-' in expression:
        parts = expression.split('-')
        operator = '-'
    elif '*' in expression:
        parts = expression.split('*')
        operator = '*'
    elif '>' in expression:
        parts = expression.split('>')
        operator = '>'
    elif '<' in expression:
        parts = expression.split('<')
        operator = '<'
    else:
        return expression 

    var1 = parts[0].strip()
    var2 = parts[1].strip()

    return f"({operator} {var1} {var2})"
    

############################################################# Class that solves SMT code.
class SMTSolver:
    def __init__(self):
        # Make a z3 solver instance.
        self.z3_solver = Solver()

        # Dictionary for storing actual z3 variables.
        self.z3_variables = {}

    def declare_if_needed(self, var_name):
        if var_name not in self.z3_variables and not var_name.isdigit():
            self.z3_variables[var_name] = Int(var_name)

    def smt_solver(self, smt_code_lines):
        for line in smt_code_lines:
            # If line is a variable declaration.
            if line.startswith('(declare-const'):
                # (declare-const x Int)
                line_without_brackets = line[1:-1] # declare-const x Int
                line_parts = line_without_brackets.split() # 3 parts: p1: declare-const [0], p2: x [1], p3: Int [2]

                variable_name = line_parts[1] # x
                data_type = line_parts[2] # Int

                # z3 variable making.
                if data_type == "Int":
                    #  smt_variable = Int("x")
                    #smt_variable = Int(variable_name)

                # Save varible using its name to be used later.
                # self.x = Int("x")
                # setattr(self, variable_name, smt_variable)
                    self.z3_variables[variable_name] = Int(variable_name)

            # If line is an assert statement.
            elif line.startswith('(assert'):
                inner_expression = line[len('(assert ('):-2].strip() # = x 10
                #print("inner ex:",inner_expression)

                if inner_expression.startswith('='): # = x 10
                    inner_expression = inner_expression[2:] # x 10
                    parts = inner_expression.split(maxsplit=1) # x0 10
                    print("parta[0]: ", parts[0])
                    print("parts[1]:", parts[1])


                    if len(parts) == 2:
                        left_expr = parts[0].strip()
                        right_expr = parts[1].strip()
                        print("LEFT:",left_expr)
                        print("RIGHT",right_expr)

                    # Convert these expressions into proper Z3 syntax.
                    if right_expr.isdigit():  # if it's a number, we directly use it.
                        self.z3_solver.add(self.z3_variables[left_expr] == int(right_expr))
                    else:  # otherwise it's a variable or an expression.
                        # (+ y0 1)
                        if right_expr.startswith('(') and right_expr.endswith(')'):
                            ex = right_expr[1:-1].split()
                            p1 = ex[0] # + / ite
                            p2 = ex[1] # y0
                            p3 = ex[2] # 1
                            print("p1: ", p1)
                            print("p2: ", p2)
                            print("p3: ", p3)
                            
                            self.declare_if_needed(left_expr)
                            self.declare_if_needed(p2)
                            self.declare_if_needed(p3)

                            if p1 == '+':
                                # Check if p3 is a digit (constant) or a variable.
                                if p3.isdigit():
                                    self.z3_solver.add(self.z3_variables[left_expr] == self.z3_variables[p2] + int(p3))
                                else:
                                    self.z3_solver.add(self.z3_variables[left_expr] == self.z3_variables[p2] + self.z3_variables[p3])

                            elif p1 == '-':
                                if p3.isdigit():
                                    self.z3_solver.add(self.z3_variables[left_expr] == self.z3_variables[p2] - int(p3))
                                else:
                                    self.z3_solver.add(self.z3_variables[left_expr] == self.z3_variables[p2] - self.z3_variables[p3])

                            elif p1 == '*':
                                if p3.isdigit():
                                    self.z3_solver.add(self.z3_variables[left_expr] == self.z3_variables[p2] * int(p3))
                                else:
                                    self.z3_solver.add(self.z3_variables[left_expr] == self.z3_variables[p2] * self.z3_variables[p3])

                            elif p1 == '/':
                                if p3.isdigit():
                                    self.z3_solver.add(self.z3_variables[left_expr] == self.z3_variables[p2] / int(p3))
                                else:
                                    self.z3_solver.add(self.z3_variables[left_expr] == self.z3_variables[p2] / self.z3_variables[p3])

                            elif p1 == 'ite': # Handle conditions.
                                cond = ex[1]
                                then_expression = ex[2]
                                else_expression = ex[3]
                                self.z3_solver.add(self.z3_variables[left_expr] ==
                                If(self.z3_variables[cond] != 0,  # non-zero means true.
                                    self.z3_variables[then_expression],
                                    self.z3_variables[else_expression]))
                        else:
                            # It's a simple variable assignment like (= x y).
                            self.declare_if_needed(left_expr)
                            self.declare_if_needed(right_expr)
                            self.z3_solver.add(self.z3_variables[left_expr] == self.z3_variables[right_expr])

        # Check results.
        result = self.z3_solver.check()

        if result == sat:
            # Get the model (solution) from the solver.
            model = self.z3_solver.model()

            # Create a dictionary to hold variable values.
            variable_info = {}

            # Loop through each variable in the model.
            for variable in model:
                # Convert variable to string and get its value.
                variable_info[str(variable)] = model[variable]

            # Prepare the final result
            result_final = {
                'status': 'Satisfiable',
                'model': variable_info
            }
        
        else:
            result_final = {
                'status': 'Unsatisfiable',
                'model': None
            }

        return result_final
    
############################################################# Class for program equivalence.
class ProgramEquivalenceChecker:
    def __init__(self):
        self.program_verifier = ProgramVerifier()
        self.ssa_to_smt_converter = SSAToSMTCoverter()
        self.smt_solver = SMTSolver()
    
    # FunctiOn that add prefixes to each of the 2 program variables so when combined to check equivalence, they can be differentiated. e.g. if x exists in both prorgram 1 and 2, now it will be p1_x for program 1 and p2_x for program 2.
    def add_prefixes_to_smt_variables(self, smt_lines, prefix):
        variable_matching = {}
        lines_with_prefixes = []

        for line in smt_lines:
            new_line = line

            # Declare line. (declare-const x Int)
            if line.startswith("(declare-const"):
                tokens = line.strip("()").split() # ['declare-const', 'x', 'Int']
                var_name = tokens[1] # x
                prefixed_name = f"{prefix}_{var_name}" # p1_x
                variable_matching[var_name] = prefixed_name # { 'x': 'p1_x' }
                new_line = f"(declare-const {prefixed_name} Int)" # (declare-const p1_x Int)

            # Assert line. (assert (> x 5))
            elif line.startswith("(assert"):
                for var, prefixed_var in variable_matching.items():
                    # Replace 'x' with 'p1_x' in the assertion.
                    # (assert (> x 5)) -> (assert (> p1_x 5))
                    line = line.replace(var, prefixed_var) 
                new_line = line

            lines_with_prefixes.append(new_line)

        return lines_with_prefixes, variable_matching
    
    # Function that returns the final versions of the variables so equivalence can be checked.
    #   Input: [
    #         'x0 = 0',
    #         'x1 = x0 + 1',
    #         'x2 = x1 + 1',
    #         'y0 = x2 + 1'
    #     ]
    #  Output: { 'x': 'x2', 'y': 'y0' }
    def get_final_variable_versions(self, ssa_lines):
        final_variables = {}

        for line in ssa_lines:
            if "=" not in line or line.strip().startswith("φ"):
                continue # Ignore lines that do not have any assignment or φ conditions.

            left_part, right_part = line.split("=") # ['x1', 'x0 + 1']
            left_part = left_part.strip() # x1

            if left_part.startswith("φ"):
                continue # Ignore condtion vars liek "φ".

            # get base name, that is, x0 has base name x and y9 has base name y.
            base = ''
            for ch in left_part: # x1
                if not ch.isdigit(): 
                    base += ch # x

            # versions. x10
            digits = "" # will eventually hold 10. (in case of x10).
            for char in left_part:
                if char.isdigit():
                    # 1 then 0 so 10
                    digits += char  # Add digit characters to the string.

            if digits == "":
                version = 0  # No digits found. x
            else:
                version = int(digits)  # Convert the digits to an integer. 10

            # Update if this version id greater than present one.
            if base not in  final_variables:
                final_variables[base] = left_part
            else:
                var_name = final_variables[base]
                digits = ""
                for c in var_name:
                    if c.isdigit():
                        digits += c

                if digits == "":
                    current_version = 0
                else:
                    current_version = int(digits)

                if version > current_version:
                    final_variables[base] = left_part

        return final_variables

    def check_program_equivalence(self, input_program_1_lines, input_program_2_lines):
        # Convert both programs into SSA format.
        # Program 01.
        self.program_verifier.variable_versions = {}
        self.program_verifier.ssa_lines = []
        self.program_verifier.convert_into_ssa(input_program_1_lines)
        program_1_ssa = self.program_verifier.ssa_lines.copy()
        print("\nProgram 1 SSA Form:")
        for line in program_1_ssa:
            print(line)

        # Program 02.
        self.program_verifier.variable_versions = {}  
        self.program_verifier.ssa_lines = []  
        self.program_verifier.convert_into_ssa(input_program_2_lines)
        program_2_ssa = self.program_verifier.ssa_lines.copy()
        print("\nProgram 2 SSA Form:")
        for line in program_2_ssa:
            print(line)

        # Find the final variables in each program.
        p1_final_variabless = self.get_final_variable_versions(program_1_ssa)
        p2_final_variables = self.get_final_variable_versions(program_2_ssa)
        print("Program 1 Final SSA Variables:")
        for var, final_version in p1_final_variabless.items():
            print(f"{var} -> {final_version}")

        print("\nProgram 2 Final SSA Variables:")
        for var, final_version in p2_final_variables.items():
            print(f"{var} -> {final_version}")

        # Convert both SSA forma in SMT code.
        # Program 01.
        self.ssa_to_smt_convertersmt_variables = {}  
        self.ssa_to_smt_converter.smt_assertions = []  
        self.ssa_to_smt_converter.convert_ssa_to_smt(program_1_ssa)
        program_1_smt = self.ssa_to_smt_converter.get_smt()
        print("\nProgram 1 SMT Form:")
        for line in program_1_smt:
            print(line)

        # Program 02.
        self.ssa_to_smt_convertersmt_variables = {}  
        self.ssa_to_smt_converter.smt_assertions = []  
        self.ssa_to_smt_converter.convert_ssa_to_smt(program_2_ssa)
        program_2_smt = self.ssa_to_smt_converter.get_smt()
        print("\nProgram 2 SMT Form:")
        for line in program_2_smt:
            print(line)

        # Apply prefixes to SMT variables
        program_1_smt_prefixed, p1_mapping = self.add_prefixes_to_smt_variables(program_1_smt, "p1")
        program_2_smt_prefixed, p2_mapping = self.add_prefixes_to_smt_variables(program_2_smt, "p2")

         # Combine SMT code from both programs (excluding check-sat and get-model).
        combined_smt = []
        
        # Add variable declarations from both programs.
        for line in program_1_smt_prefixed:
            if line.startswith("(declare-const"):
                combined_smt.append(line)
        
        for line in program_2_smt_prefixed:
            if line.startswith("(declare-const"):
                combined_smt.append(line)
        
        # Add assertions from both programs.
        for line in program_1_smt_prefixed:
            if line.startswith("(assert"):
                combined_smt.append(line)
        
        for line in program_2_smt_prefixed:
            if line.startswith("(assert"):
                combined_smt.append(line)

        # Assert stuff to check if final values match. EQUIVALENE PROOF PART HERE.
        # REMINDER: final_variables = { 'x': 'x2', 'y': 'y10' } -> base name of x2 is x and base name of y10 is y.
        for base_name in p1_final_variabless:
            if base_name in p2_final_variables:
                p1_variable = p1_final_variabless[base_name]
                p2_variable = p2_final_variables[base_name]
                p1_prefixed_variable = f"p1_{p1_variable}"
                p2_prefixed_variable = f"p2_{p2_variable}"
                combined_smt.append(f"(assert (= {p1_prefixed_variable} {p2_prefixed_variable}))")
        
        combined_smt.append("(check-sat)")
        combined_smt.append("(get-model)")

        print("\nCombined SMT code:")
        for line in combined_smt:
            print(line)

        # Solve the combined SMT problem
        result = self.smt_solver.smt_solver(combined_smt)
        
        print("\nEquivalence Check Result:")
        if result['status'] == 'Satisfiable':
            print("The programs are equivalent!")
            print("Model:", result['model'])
            return True, result
        else:
            print("The programs are NOT equivalent!")
            return False, result

# Function to convert list of lines of code in a single string.
def code_lines_to_string_converter(code_lines_list):
    result = "" 

    for line in code_lines_list:
        clean_line = line.strip() 
        result += clean_line + "\n" 

    return result

def main():
    # Example code to test SSA and SMT generation.
    code_lines = [
        "x := 0;",
        "while (x < 4) {",
        "    x := x + y;",
        "}",
        "assert(x == 4);"
    ]

    code_lines2 = [
    "x := 3;",
    "if (x < 5) {",
    "y := x + 1;",
    "} else {",
    "y := x - 1;",
    "}",
    "assert(y > 0);"
    ]

    print("=== Program Verifier & SSA Conversion ===")
    verifier = ProgramVerifier()
    verifier.convert_into_ssa(code_lines2)

    print("\nSSA Code:")
    for line in verifier.ssa_lines:
        print(line)

    print("\n=== SMT Conversion ===")
    converter = SSAToSMTCoverter()
    converter.convert_ssa_to_smt(verifier.ssa_lines)
    smt_output = converter.get_smt()

    print("\nSMT-LIB Code:")
    for line in smt_output:
        print(line)

    print("\n=== Solving SMT with Z3 ===")
    solver = SMTSolver()
    result = solver.smt_solver(smt_output)

    print("\nSMT Solver Result:")
    print(f"Status: {result['status']}")
    if result['model']:
        print("Model:")
        for var, val in result['model'].items():
            print(f"  {var} = {val}")

    print("\n=== Programs Equivalence Checker ===")
    program_verifier = ProgramEquivalenceChecker()
    program_verifier.check_program_equivalence(code_lines2, code_lines)

def test_ssa_conversion():
    code_lines3 = [
        "for (i := 0; i < n; i := i + 1) {",
        "    for (j := 0; j < n - i - 1; j := j + 1) {",
        "        if (arr[j] > arr[j+1]) {",
        "            temp := arr[j];",
        "            arr[j] := arr[j+1];",
        "            arr[j+1] := temp;",
        "        }",
        "    }",
        "}"
    ]

    print("=== Program Verifier & SSA Conversion ===")
    verifier = ProgramVerifier()
    verifier.convert_into_ssa(code_lines3)

    print("\nSSA Code:")
    for line in verifier.ssa_lines:
        print(line)

if __name__ == "__main__":
    main()
