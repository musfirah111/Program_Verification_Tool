from z3 import Solver, Int, If, sat

############################################################# Class for program verification.
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
                    f"{new_versioned_name} = φ{change['condition']} ? "
                    f"{variable}{change['true_version']} : {variable}{change['false_version']}"
                )


                self.ssa_lines.append(cond_backtrack_line)
                done_conditions.add(change["condition"])

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
        ssa_line = f"{ssa_var} = {righthandsideEq}"

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
                print()
                # self.ssa_lines.append(ssa_line)

            i += 1

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

                        elif p1 == 'ite': # Handle conditions.
                            cond = ex[1]
                            then_expression = ex[2]
                            else_expression = ex[3]
                            self.z3_solver.add(self.z3_variables[left_expr] ==
                            If(self.z3_variables[cond] != 0,  # non-zero means true.
                                self.z3_variables[then_expression],
                                self.z3_variables[else_expression]))

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

    def add_prefixes_to_variables(self, ssa_lines, prefix):
        variable_matching ={} # Maps OG variable names to their prefixed versions.
        # { x: p1_x }
        lines_with_prefixes = [] # Stores lines after they have been prefixed.

         # First pass: map all LHS variables.
        for line in ssa_lines:
            if "=" in line:
                left_part = line.split("=", 1)[0].strip()
                variable_matching[left_part] = f"{prefix}_{left_part}"

        # Second pass: replace the og vars.
        for line in ssa_lines:
            new_line = line

            # Regular assignment ----------- 1st CASE
            # Example:
            # Original: x2 = x1 + 1
            # Mapping: { x1: p1_x1, x2: p1_x2 }
            # Result : p1_x2 = p1_x1 + 1
            if "=" in line and not line.strip().startswith("φ") and "?" not in line:
                left_part, right_part = line.split("=", 1) # x2, x1 + 1
                left_variable_name = left_part.strip() # x2
                #prefixed_variable_name = f"{prefix}_{left_variable_name}" # p1_x
                prefixed_left_part = variable_matching[left_variable_name] # Get prefixed version (e.g., p1_x2)

                # Now, replace the variables in the right hand side of the expression.
                further_right_parts = right_part.strip().split() # ['x1', '+', '1']
                for i, part in enumerate(further_right_parts):
                    if part in variable_matching:
                        further_right_parts[i] = variable_matching[part]  # e.g., 'x1' -> 'p1_x1'
                new_right_part = " ".join(further_right_parts) # 'p1_x1 + 1' 
                
                print("\nLINE c1:", line)
                prefixed_line = f"{prefixed_left_part} = {new_right_part}" # p1_x = p1_y + p1_z
                print("PREFIXED LINE c1:", prefixed_line)
                print()

            # For handling condition variables. ---------- 2nd CASE
            # Original: φ1 = (x0 < 4)
            # Mapping: { x0: p1_x0, φ1: p1_φ1 }
            # Result : p1_φ1 = (p1_x0 < 4)
            elif line.startswith('φ'):
                condition_variable, condition = line.split("=") # use 1 in sp
                condition_variable = condition_variable.strip() # φ1
                prefixed_condition = variable_matching[condition_variable] # p1_φ1

                # Replace variables inside condition string.
                for variable, prefixed_version in variable_matching.items():
                    condition = condition.replace(variable, prefixed_version) # (x0 < 4) -> (p1_x0 < 4)

                condition = condition.strip()

                print("\nLINE c2:", line)
                prefixed_line = f"{prefixed_condition} = {condition}" 
                print("PREFIXED LINE c2:", prefixed_line)

            # AHndling of COnditional assignmetns. ----------- 3rd CASe
            # Originl: x5 = φ1 ? x4 : x3
            # Mapping: { φ1: p1_φ1, x4: p1_x4, x3: p1_x3, x5: p1_x5 }
            # Result : p1_x5 = p1_φ1 ? p1_x4 : p1_x3
            elif '?' in line and ':' in line:
                left_part, right_part = line.split("=") # ['x5', 'φ1 ? x4 : x3']
                left_variable = left_part.strip() # x5
                prefixed_left_variable = variable_matching[left_variable] # p1_x5

                # Dividng right hand side into parts. φ1 ? x4 : x3
                condition_Part, true_false_part = right_part.split("?") # ['φ1 ', ' x4 : x3']
                true_part, false_part = true_false_part.split(":") # [' x4 ', ' x3']

        return lines_with_prefixes, variable_matching
    


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

        # Add prefixes to variables in both programs.
        program_1_ssa_prefixed, p1_mapping = self.add_prefixes_to_variables(program_1_ssa, "p1")
        program_2_ssa_prefixed, p2_mapping = self.add_prefixes_to_variables(program_2_ssa, "p2")

         # Combine SMT code from both programs (excluding check-sat and get-model).
        combined_smt = []
        
        # Add variable declarations from both programs.
        for line in program_1_smt:
            if line.startswith("(declare-const"):
                combined_smt.append(line)
        
        for line in program_2_smt:
            if line.startswith("(declare-const"):
                combined_smt.append(line)
        
        # Add assertions from both programs.
        for line in program_1_smt:
            if line.startswith("(assert"):
                combined_smt.append(line)
        
        for line in program_2_smt:
            if line.startswith("(assert"):
                combined_smt.append(line)

# Function to convert list of lines of code in a single string.
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
    verifier.convert_into_ssa(code_lines)

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
    program_verifier.check_program_equivalence(code_lines, code_lines2)
