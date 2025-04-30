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

    def ssa_assignment(self, line):
        # Split the line at the first encounter of := to otain the LHS - the variable and the RHS.
        equation = line.split(":=", 1)
        # Using strip to remove any leading or trailing whitespaces.
        lefthandsideVar = equation[0].strip()
        righthandsideEq = equation[1].strip()
        # if the variable already exists in the dict then increment it's count,
        # Otherwise at it in the dict with count starting from 0.
        if lefthandsideVar in self.variable_versions:
            self.variable_versions[lefthandsideVar] += 1 
        else:
            self.variable_versions[lefthandsideVar] = 0
        
        ssa_var = self.new_variable_with_count(lefthandsideVar)
        #print(righthandsideEq)
        #print(self.variable_versions)
        for letter in righthandsideEq:
            #print(letter)
            if letter in self.variable_versions:
                #print(letter)
                #print("INSIDE")
                righthandsideEq = righthandsideEq.replace(letter, self.new_variable_with_count(letter))
                #print(righthandsideEq)

        # Add the line in the Single Static Assignment Lines after combing both the LHS and the RHS.
        ssa_line = f"{ssa_var} := {righthandsideEq}"

        return ssa_line, lefthandsideVar

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
                condition_var = "cond"

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
                    cond = self.new_variable_with_count("cond")
                    
                    if_var = if_branch_vars.get(var, self.new_variable_with_count(var))
                    else_var = else_branch_vars.get(var, self.new_variable_with_count(var))
                    
                    ssa_line = f"{new_var} = {cond} ? {if_var} : {else_var}"
                    
                    self.ssa_lines.append(ssa_line)

            i += 1    

                    






