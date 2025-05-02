from z3 import Solver, Int, If, sat

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
                done_conditions.add(change["condition"])




    # Function to handle increment statements
    def handle_increment_statement(self, increment_statement):
        if ":=" in increment_statement:
            increment_variable, increment_expression = increment_statement.split(":=", 1)
            increment_variable = increment_variable.strip()
            increment_expression = increment_expression.strip()

            increment_version = self.get_current_variable_version(increment_variable)

            increment_value = 1  # Default increment value

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
                    else:
                        raise ValueError(f"Invalid increment expression: {increment_expression}")

                    incremented_value = f"{incremented_variable}{increment_version} + {increment_value}"

            # Create SSA assignment for the increment
            incremented_ssa_line = f"{increment_variable}{increment_version + 1} := {incremented_value}"
            self.ssa_lines.append(incremented_ssa_line)

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
            self.ssa_lines.append(ssa_line)
     


    # Function to create phi assignment for loop conditions
    def create_phi_assignment(self, loop_condition, condition_counter):
        
        condition_number = condition_counter + 1  
        self.condition_counter = condition_number 

        phi_var = f"φ{condition_number}"
        
        # Parse the loop condition to separate variables and constants
        condition_parts = loop_condition.split("<")
        left_side = condition_parts[0].strip()  # e.g., j
        right_side = condition_parts[1].strip()  # e.g., n - i - 1

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
        



    # function to unrol nested for loop 
    def unroll_for_loop_and_ssa(self, condition, loop_body, unroll_depth):
        # Store current versions of variables before loop starts.
        list_of_variables_versions = {}
        loop_variable_versions = []  # To store versions for backtracking

        for variable in self.variable_versions:
            list_of_variables_versions[variable] = self.get_current_variable_version(variable)

        # Parse the outer for loop condition (i := 0; i < n; i := i + 1)
        parts = condition.split(";")
        init_statement = parts[0].strip()  # i := 0 or i := 1
        loop_condition = parts[1].strip()  # i < n
        incr_statement = parts[2].strip()  # i := i + 1

        # Handle init and phi without printing
        self.handle_init_statement(init_statement)
        self.create_phi_assignment(loop_condition, self.condition_counter)

        # Unroll the inner loop
        for i in range(unroll_depth):
            inner_condition = ""  # for inner loop 
            inner_loop_body = []  
            
            for line in loop_body:
                line = line.strip()
                # print("Current line:", line)  
                
                if line.startswith("for"):
                    # print("entered for loop")
                    # Extract the inner loop condition and body
                    start = line.find('(') + 1
                    end = line.find(')', start)
                    inner_condition = line[start:end].strip()
                    parts = [part.strip() for part in inner_condition.split(';')] 

                    # # Check if we have exactly three parts
                    # if len(parts) != 3:
                    #     raise ValueError(f"Invalid inner loop format: {line}")

                    inner_init_statement = parts[0]  # j := 0
                    inner_loop_condition = parts[1]  # j < n - i - 1
                    inner_incr_statement = parts[2]  # j := j + 1

                    # print("part 0: ", parts[0])
                    # print("part 1: ", parts[1])
                    # print("part 2: ", parts[2])

                    # Get inner loop body
                    inner_bracket_count = 1
                    # print("loop_body contents:", loop_body)
                    k = -1
                    for i, l in enumerate(loop_body):
                        if l.strip() == line.strip(): 
                            k = i + 1
                            break

                    # if k == -1:
                    #     raise ValueError(f"Line not found in loop_body: {line}")

                    while k < len(loop_body) and inner_bracket_count > 0:
                        inner_line = loop_body[k]
                        if "{" in inner_line:
                            inner_bracket_count += 1
                        if "}" in inner_line:
                            inner_bracket_count -= 1
                        if inner_bracket_count > 0:
                            inner_loop_body.append(inner_line)
                        k += 1
                    
                    self.extract_unroll_depth(inner_condition)

                # Handle init and phi without printing
                self.handle_init_statement(inner_init_statement)
                self.create_phi_assignment(inner_loop_condition, self.condition_counter)               

                # Handle other lines in the loop body
                if "if" in line:
                    start = line.find("(")
                    end = line.find(")")
                    if_condition = line[start + 1:end].strip()

                    # print(f"Processing if condition: {if_condition}")

                    if "[" in line and "]" in line:
                        for cond in ['<', '>', '<=', '>=', '==', '!=']:
                            if cond in if_condition:
                                parts = if_condition.split(cond)
                                left_array = parts[0].strip()
                                right_array = parts[1].strip()

                                if "[" in left_array:
                                    left_array_parts = left_array.split("[")
                                    left_array = left_array_parts[0].strip()
                                    left_index = left_array_parts[1].split("]")[0].strip()
                                    if left_index in self.variable_versions:
                                        left_index = f"{left_index}{self.get_current_variable_version(left_index)}"
                                    left_array_access = f"{left_array}{self.get_current_variable_version(left_array)}[{left_index}]"

                                    # Handle right array access
                                    right_array_parts = right_array.split("[")
                                    right_array = right_array_parts[0].strip()
                                    right_index = right_array_parts[1].split("]")[0].strip()
                                    if right_index in self.variable_versions:
                                        right_index = f"{right_index}{self.get_current_variable_version(right_index)}"
                                    right_array_access = f"{right_array}{self.get_current_variable_version(right_array)}[{right_index}]"

                                    # Create the condition line
                                    self.condition_counter += 1
                                    condition_number = self.condition_counter
                                    condition_line = f"φ{condition_number} = ({left_array_access} > {right_array_access})"
                                    self.ssa_lines.append(condition_line)

                                    # Add temp variable and array swapping
                                    temp_var = f"temp{self.get_current_variable_version('temp')}"
                                    self.ssa_lines.append(f"{temp_var} = {left_array_access}")
                                    self.ssa_lines.append(f"{left_array_access} = {right_array_access}")
                                    self.ssa_lines.append(f"{right_array_access} = {temp_var}")

                                    # Add backtracking assignments
                                    self.ssa_lines.append(f"{left_array_access} = @{condition_number} ? {left_array_access} : {left_array_access}")
                                    self.ssa_lines.append(f"{right_array_access} = @{condition_number} ? {right_array_access} : {right_array_access}")

                elif "temp" in line:
                    ssa_line, var = self.ssa_assignment(line)
                    self.ssa_lines.append(ssa_line)  

                if ":=" in line:
                    if "[" in line and "]" in line:
                        left_part, right_part = line.split(":=")
                        left_part = left_part.strip()
                        right_part = right_part.strip()

                        # array left side
                        if "[" in left_part:
                            left_array_parts = left_part.split("[")
                            left_array = left_array_parts[0].strip()
                            left_index = left_array_parts[1].split("]")[0].strip()
                            if left_index in self.variable_versions:
                                left_index = f"{left_index}{self.get_current_variable_version(left_index)}"
                            left_array_access = f"{left_array}{self.get_current_variable_version(left_array)}[{left_index}]"

                            # array right side
                            if "[" in right_part and "]" in right_part:
                                right_array_parts = right_part.split("[")
                                right_array = right_array_parts[0].strip()  
                                right_index_expression = right_array_parts[1].split("]")[0].strip()

                                # split j(version) +1
                                index_parts = [part.strip() for part in right_index_expression.split("+")]
                                processed_index_parts = []

                                # check variable version for variable e.g j in j+1
                                for part in index_parts:
                                    if part == "j":
                                        part = f"{part}{self.get_current_variable_version(part)}"
                                    elif part.isdigit():
                                        pass # is constant so do nothing
                                    processed_index_parts.append(part)

                                # join the parts again
                                processed_index_expression = "+".join(processed_index_parts)
                                right_array_access = f"{right_array}{self.get_current_variable_version(right_array)}[{processed_index_expression}]"

                                ssa_line = f"{left_array_access} := {right_array_access}"
                                self.ssa_lines.append(ssa_line)

                                # print(f"SSA assignment: {ssa_line}")
                            
                            # if expressions have temp in it
                            elif right_part == "temp":
                                ssa_line = f"{right_array_access} := temp{self.get_current_variable_version('temp')}"
                                self.ssa_lines.append(ssa_line)
                            
                            elif left_part == "temp":
                                ssa_line = f"temp{self.get_current_variable_version('temp')} := {left_array_access}"
                                self.ssa_lines.append(ssa_line)

                self.handle_increment_statement(inner_incr_statement)
            
            self.handle_increment_statement(incr_statement)
        
            # Add outer loop backtracking
            if i > 0:
                for var in self.variable_versions:
                    if var.startswith('a'):  # Only for array variables
                        current_version = self.get_current_variable_version(var)
                        prev_version = current_version - 1
                        self.ssa_lines.append(f"{var}{current_version} = @{self.condition_counter} ? {var}{current_version} : {var}{prev_version}")



    def ssa_assignment(self, line):
        # Check if the line contains the assignment operator
        if ":=" not in line:
            raise ValueError(f"Invalid assignment line: {line}")

        # Split the line at the first encounter of := to obtain the LHS - the variable and the RHS.
        equation = line.split(":=", 1)
        # Using strip to remove any leading or trailing whitespaces.
        lefthandsideVar = equation[0].strip()
        righthandsideEq = equation[1].strip()

        for letter in righthandsideEq:
        #print(letter)
            if letter in self.variable_versions:
                #print(letter)
                #print("INSIDE")
                righthandsideEq = righthandsideEq.replace(letter, self.new_variable_with_count(letter))
                #print(righthandsideEq)

        # if the variable already exists in the dict then increment it's count,
        # Otherwise at it in the dict with count starting from 0.
        if lefthandsideVar in self.variable_versions:
            self.variable_versions[lefthandsideVar] += 1 
        else:
            self.variable_versions[lefthandsideVar] = 0
        
        ssa_var = self.new_variable_with_count(lefthandsideVar)
        #print(righthandsideEq)
        #print(self.variable_versions)
       

        # Add the line in the Single Static Assignment Lines after combing both the LHS and the RHS.
        ssa_line = f"{ssa_var} := {righthandsideEq}"

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
        while i < len(code_lines):
            line = code_lines[i]
            # Assignments e.g x := 5
            if ":=" in line:
                ssa_line, var = self.ssa_assignment(line)
                self.ssa_lines.append(ssa_line)
            # If/else Block e.g if (x > 4)
            elif "if" in line:
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
                        self.ssa_lines.append(ssa_line)
                        # Store the new SSA version for this variable
                        if_branch_vars[var_name] = self.new_variable_with_count(var_name)
                    i += 1
                
                if "else" in code_lines[i]:
                    i += 1
                    while i < len(code_lines) and "}" not in line:
                        if ":=" in code_lines[i]:
                            ssa_line, var_name = self.ssa_assignment(code_lines[i])
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

            i += 1

    def get_versioned_variable(self, variable):
        if variable in self.variable_versions:
            return f"{variable}{self.variable_versions[variable]}"
        return variable  # case where the variable doesn't exist

# Class that changes SSA into SMT code.
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

    # Function to convert ssa assignment line in smt code.
    def convert_assignment_line_in_smt(self, ssa_line):
        condition_representation = "φ"

        left_part, right_part = ssa_line.split(":=")
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
            
            smt_line = f"(assert (= {left_part} {right_part}))"
            self.smt_assertions.append(smt_line)

    # Function to convert ssa into smt.
    def convert_ssa_to_smt(self, ssa_lines):
        # Iterate through every line in ssa.
        for line in ssa_lines:
            if ':=' in line:
                parts = line.split(':=')
                left_part = parts[0]
                left_part = left_part.strip() # Get the assigned variable.

                # Add this variable to smt variables if it is not already present there.
                if left_part not in self.smt_variables:
                    self.smt_variables[left_part] = left_part
        
        # Conert ssa assignment line to smt code.
        for line in ssa_lines:
            if ':=' in line:
                self.convert_assignment_line_in_smt(line)

    def get_smt(self):
        smt_output = []

        for var in self.smt_variables.values():
            smt_output.append(f"(declare-const {var} Int)")

        for assertion in self.smt_assertions:
            smt_output.append(assertion)

        smt_output.append("(check-sat)")
        smt_output.append("(get-model)")

        return smt_output
    
class ProgramEquivalenceChecker:
    def __init__(self):
        print()

def convert_infix_to_prefix(expression):
    expression = expression.strip()

    if '+' in expression:
        parts = expression.split('+')
        operator = '+'
    elif '-' in expression:
        parts = expression.split('-')
        operator = '-'
    elif '*' in expression:
        parts = expression.split('*')
        operator = '*'
    else:
        return expression 

    var1 = parts[0].strip()
    var2 = parts[1].strip()

    return f"({operator} {var1} {var2})"


class SMTSolver:
    def __init__(self):
        # Make a z3 solver instance.
        self.z3_solver = Solver()

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
                    smt_variable = Int(variable_name)

                # Save varible using its name to be used later.
                # self.x = Int("x")
                # setattr(self, variable_name, smt_variable)

            # If line is an assert statement.
            elif line.startswith('(assert'):
                # (assert(= x 10))
                assert_without_brackets = line[1:-1] # assert(= x 10)
                expression = assert_without_brackets.split("=", 1)  # Split by '='

                if len(expression) == 2:
                    left_expr = expression[0].strip()
                    right_expr = expression[1].strip()

                    # Convert these expressions into proper Z3 syntax.
                    if right_expr.isdigit():  # if it's a number, we directly use it.
                        self.z3_solver.add(Int(left_expr) == int(right_expr))
                    else:  # otherwise it's a variable or an expression.
                        self.z3_solver.add(Int(left_expr) == Int(right_expr))

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

def code_lines_to_string_converter(code_lines_list):
    result = "" 

    for line in code_lines_list:
        clean_line = line.strip() 
        result += clean_line + "\n" 

    return result

if __name__ == "__main__":
    # Example code to test SSA and SMT generation.
    code_lines = [
        "x := 0;",
        "while (x < 4) {",
        "    x := x + 1;",
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
    verifier = ProgramVerifierAndEquivalenceChecker()
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
