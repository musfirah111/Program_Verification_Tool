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

    # function to unrol nested for loop 
    def unroll_for_loop_and_ssa(self, condition, loop_body, unroll_depth):
        # Store current versions of variables before loop starts.
        list_of_variables_versions = {}

        # store condition variables numbers
        condition_variables_numbers = []

        # store condition variables numbers
        condition_variables_numbers = []

        for variable in self.variable_versions:
            list_of_variables_versions[variable] = self.get_current_variable_version(variable)

        # Parse the for loop condition (i := 0; i < n; i := i + 1)
        parts = condition.split()
        init_statement = parts[0].strip()  # i := 0 or i := 1
        loop_condition = parts[1].strip()  # i < n
        incr_statement = parts[2].strip()  # i := i + 1

        # Handle loop initialization
        ssa_line = self.ssa_assignment(init_statement)
        self.ssa_lines.append(ssa_line)
        loop_variable = init_statement.split(':=', 1)[0].strip()
        
        # unroll the loop
        for i in range(unroll_depth):
            self.condition_counter += 1
            condition_number = self.condition_counter

            # Update condition with current variable versions
            cond_parts = condition.split()
            updated_condition = []

            # Handle both < and <= conditions
            for part in cond_parts:
                if part in self.variable_versions:
                    version = self.get_current_variable_version(part)
                    updated_condition.append(f"{part}{version}")
                elif part in ['<', '<=']: 
                    updated_condition.append(part)
                else:
                    updated_condition.append(part)
            
            condition_new = " ".join(updated_condition)
            condition_line = f"φ{condition_number} = ({condition_new})"
            self.ssa_lines.append(condition_line)
        
            # loop body 
            for line in loop_body:
                # handle if statement
                if "if" in line:
                    # extract the condition
                    start = line.find("(")
                    end = line.find(")")
                    if_condition = line[start + 1:end].strip()

                    # handle if body
                    if "[" in line and "]" in line:
                        # Find which comparison operator is used
                        for cond in ['<', '>', '<=', '>=', '==', '!=']:
                            if cond in if_condition:
                                parts = if_condition.split(cond)
                                left_array = parts[0].strip()
                                right_array = parts[1].strip()

                                left_array_name = left_array.split("[")[0].strip()  # e.g arr from arr[j]
                                left_index = left_array.split("[")[1].split("]")[0].strip()
                                if left_index in self.variable_versions:
                                    left_index = f"{left_index}{self.get_current_variable_version(left_index)}"
                                # create ssa array
                                left_array_access = f"{left_array_name}{self.get_current_variable_version(left_array_name)}_{left_index}"
                
                                # Handle right array access
                                right_array_name = right_array.split("[")[0].strip()
                                right_index = right_array.split("[")[1].split("]")[0].strip()
                                if right_index in self.variable_versions:
                                    right_index = f"{right_index}{self.get_current_variable_version(right_index)}"
                                right_array_access = f"{right_array_name}{self.get_current_variable_version(right_array_name)}_{right_index}"
                                    
                                # Create the condition line
                                self.condition_counter += 1
                                condition_number = self.condition_counter
                                condition_line = f"φ{condition_number} = ({left_array_access} > {right_array_access})"
                                self.ssa_lines.append(condition_line)

                elif "temp" in line:
                        ssa_line, var = self.ssa_assignment(line)
                        self.ssa_lines.append(ssa_line)  

                # if ":=" in line:

                #     # handle array indexing
                #     if "[" in line and "]" in line:
                #         left_part, right_part = line.split(":=")
                #         left_part = left_part.strip()
                #         right_part = right_part.strip()

                #         # array left side
                #         array = left_part

                        
                        

                
        

    def ssa_assignment(self, line):
        # Split the line at the first encounter of := to otain the LHS - the variable and the RHS.
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
                
                # Unroll the for loop
                self.unroll_for_loop_and_ssa(condition, loop_body, unroll_depth)
                i = j  # Skip to the end of the loop

            i += 1

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
