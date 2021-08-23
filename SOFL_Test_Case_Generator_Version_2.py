import random
import time
from math import fmod

import numpy as np

import PSO_library as oPSO


#This function extract all variables (input and output) and their type
def divideVars(vars_info):
    input_Variables = {}
    output_Variables = {}
    external_Variables = {}
    #If there are some external variables save it as well
    if "ext rd" in vars_info:
        externalPart = vars_info.rsplit("ext rd")[1]
        vars_info = vars_info.rsplit("ext rd")[0]
    elif "ext wr" in vars_info:
        externalPart = vars_info.rsplit("ext wr")[1]
        vars_info = vars_info.rsplit("ext wr")[0]
    linewithInputs = vars_info.rsplit('\n')[0]
    linewithOutputs = vars_info.rsplit('\n')[1]
    linewithOutputs = linewithOutputs.replace('\t','').replace('\n','')
    linewithInputs = linewithInputs[linewithInputs.index('(')+1:linewithInputs.index(')')]
    inputList = []
    outputList = []
    split = False
    j=0
    for i,char in enumerate(linewithInputs):
        if char == ':':
            split = True
        if (split and char == ','):
            inputList.append(linewithInputs[j:i].replace(' ',''))
            j=i+1
            split = False
        elif (split and i==len(linewithInputs)-1):
            inputList.append(linewithInputs[j:].replace(' ',''))
            j=0
            split = False
    for group in inputList:
        listwithInputs = group.rsplit(':')
        for i,element in enumerate(listwithInputs):
            if i%2!=0:
                input_Variables[element] = listwithInputs[i-1].rsplit(',')
    for i,char in enumerate(linewithOutputs):
        if char == ':':
            split = True
        if (split and char == ','):
            outputList.append(linewithOutputs[j:i].replace(' ',''))
            j=i+1
            split = False
        elif (split and i==len(linewithOutputs)-1):
            outputList.append(linewithOutputs[j:].replace(' ',''))
            j=0
            split = False
    for group in outputList:
        listwithOutputs = group.rsplit(':')
        for i,element in enumerate(listwithOutputs):
            if i%2!=0:
                output_Variables[element] = listwithOutputs[i-1].rsplit(',')
    for key in input_Variables.keys():
        for i,var in enumerate(input_Variables[key]):
            input_Variables[key][i] = var.replace(' ','')
    for key in output_Variables.keys():
        for i,var in enumerate(output_Variables[key]):
            output_Variables[key][i] = var.replace(' ','')
    #Input and output variables are lists, were the key is the type and inside there's an array with variables of that type
    return input_Variables, output_Variables 

#This function take the post condition to save and return the guard conditions with the corresponding definition condition
def listOfGuards(post):
    guardConditions = []
    defConditions = []
    post = post.replace('Post', '').replace('post', '').replace('\n','')
    if " or" in post:
        clauses = post.rsplit(' or')
        for clause in clauses:
            clause = clause[clause.index('(')+1:]
            while clause[len(clause)-1] == ' ':
                clause = clause[:len(clause)-1]
            if clause[len(clause)-1] == ')':
                clause = clause[:len(clause)-1]
            if "implies" in clause:
                clDiv = clause.rsplit(" implies ")
                while clDiv[0][len(clDiv[0])-1] == ' ':
                    clDiv[0] = clDiv[0][:len(clDiv[0])-1]
                guardConditions.append(clDiv[0])
                defConditions.append(clDiv[1])
            else:
                defConditions.append(clause)
    else:
        if "implies" in post:
            clDiv = post.rsplit(" implies ")
            while clDiv[0][len(clDiv[0])-1] == ' ':
                clDiv[0] = clDiv[0][:len(clDiv[0])-1]
            guardConditions.append(clDiv[0])
            defConditions.append(clDiv[1])
        else:
            defConditions.append(post)
    #Guard and def conditions arrays with each guard and def conditions
    return guardConditions, defConditions

#This function finds and returns the corresponding relational operator in an atom
def searchAtomOp(atom):
    if '>=' in atom:
        return '>='
    elif '!=' in atom:
        return '!='
    elif '<=' in atom:
        return '<='
    elif '=' in atom:
        return '='
    elif '>' in atom:
        return '>'
    elif '<' in atom:
        return '<'
    elif 'inset' in atom:
        return 'inset'
    elif 'notin' in atom:
        return 'notin'

#This function is used to assign values to variables that are strings, that are involved in an "inset" or "notin" operator or that are an equality with 1 free variable
def assignVariableValue(atom, key,variables):
    if key == "string":
        if '=' in atom:
            return atom.rsplit('=')[1]
    elif key == "inset":
        if '{' in atom:
            actual_set = atom.rsplit("inset")[1].replace('{','').replace('}','')
            actual_set = actual_set.rsplit(',')
        else:
            for keys in variables.keys():
                if keys == "seqofint":
                    for var in variables[keys]:
                        if var in atom:
                            actual_set = np.random.randint(25, size=random.randint(5, 15)).tolist()
        return int(actual_set[random.randint(0,len(actual_set)-1)])
    elif key == "notin":
        if '{' in atom:
            actual_set = atom.rsplit("notin")[1].replace('{','').replace('}','')
            actual_set = actual_set.rsplit(',')
        else:
            for keys in variables.keys():
                if keys == "seqofint":
                    for var in variables[keys]:
                        if var in atom:
                            actual_set = np.random.randint(25, size=random.randint(5, 15)).tolist()
        value = actual_set[random.randint(0,len(actual_set)-1)]
        while value in actual_set:
            value = str(random.randint(0,50))
        return int(value)
    elif key == '=':
        for k in variables.keys():
            for var in variables[k]:
                if var in atom:
                    if k == "int" or k=="nat" or k=="nat0":
                        return int(eval(atom.rsplit('=')[1]))
                    if k=="float+":
                        return float(eval(atom.rsplit('=')[1]))

#This function returns an array with the free variables used in an atom
def getFreeVariables(atom, input_Variables):
  freeVariables = []
  for key in input_Variables.keys():
    for inVar in input_Variables[key]:
      if inVar in atom:
        freeVariables.append(inVar)
  return freeVariables

#This function verifies if the given predicate is satisfied with the values of the variables 
def satisfy(predicate, inputVarValues):
    evaluated_predicate = predicate
    if "forall" not in predicate:
        for atom in predicate.rsplit(" and "):
            #Split predicate into atoms and evaluate the variables with values
            evaluated_predicate = evaluated_predicate.replace(atom,oPSO.evalPred(atom, inputVarValues))
            if 'inset' in atom:
                actual_set = atom.rsplit(' inset ')[1]
                actual_set = actual_set.replace('}','').replace('{','')
                actual_set = actual_set.rsplit(',')
                actual_element = atom.rsplit(' inset ')[0]
                actual_element = actual_element.replace(' ','')
                for key in inputVarValues.keys():
                    if key in actual_element:
                        actual_element = str(inputVarValues[key])
                if actual_element not in actual_set:
                    return False
            elif 'notin' in atom:
                actual_set = atom.rsplit(' notin ')[1]
                actual_set = actual_set.replace('}','').replace('{','')
                actual_set = actual_set.rsplit(',')
                actual_element = atom.rsplit(' notin ')[0]
                actual_element = actual_element.replace(' ','')
                for key in inputVarValues.keys():
                    if key in actual_element:
                        actual_element = str(inputVarValues[key])
                if actual_element not in actual_set:
                    return False
        #Calculate the error in the error function with respect to the predicate
        error = oPSO.objective_function(evaluated_predicate,inputVarValues)
        #If error is 0 then predicate is satisfied, otherwise it's not
        if error == 0:
            return True
    else:
        evaluated_predicate = predicate.replace("forall",'')
        domain = evaluated_predicate[evaluated_predicate.index('('):evaluated_predicate.index(')')+1]
        evaluated_predicate = evaluated_predicate.replace(domain,'')
        domain = domain.replace('(','').replace(')','')
        newVar = {}
        name = domain[:1]
        for var in inputVarValues:
            if var in domain:
                domain = domain.replace(var,str(inputVarValues[var]))
                var_used = var
        newVar[name] = 0
        domain = domain[domain.index('[')+1:domain.index(']')].rsplit(',')
        low_limit = int(eval(domain[0]))
        high_limit = int(eval(domain[1]))
        negation = False
        if '¬' in evaluated_predicate:
            negation = True
            evaluated_predicate = evaluated_predicate.replace('¬','').replace('(','').replace(')','')
        for i in range(high_limit-low_limit +1):
            newVar[name] = low_limit+i
            if negation:
                if satisfy(evaluated_predicate,newVar):
                    return False,{var_used : newVar[name]}
        return True,{}
    return False

#This function deletes atoms that uses string type variables, "inset" and "notin" operators, and definition of variable (i.e. x=2)
def enhacePredicate(predicate, variables):
    nonNumericVariables = []
    dataForNNVariables = {}
    atoms = predicate.rsplit(" and ")
    for key in variables.keys():
        if key == "string":
            for var in variables[key]:
                for atom in atoms:
                    if var in atom:
                        option1 = " and "+atom
                        option2 = atom+" and "
                        if option1 in predicate:
                            predicate = predicate.replace(option1,'')
                        elif option2 in predicate:
                            predicate = predicate.replace(option2,'')
                        else:
                            predicate = predicate.replace(atom,'')
                        dataForNNVariables[var] = assignVariableValue(atom,"string",variables)
                        nonNumericVariables.append(var)
    if "inset" in predicate or "notin" in predicate:
        for atom in atoms:
            if "inset" in atom:
                for key in variables.keys():
                    for var in variables[key]:
                        if var in atom:
                            option1 = " and "+atom
                            option2 = atom+" and "
                            if option1 in predicate:
                                predicate = predicate.replace(option1,'')
                            elif option2 in predicate:
                                predicate = predicate.replace(option2,'')
                            else:
                                predicate = predicate.replace(atom,'')
                            dataForNNVariables[var] = assignVariableValue(atom,"inset",variables)
                            nonNumericVariables.append(var)
            elif "notin" in atom:
                for key in variables.keys():
                    for var in variables[key]:
                        if var in atom:
                            option1 = " and "+atom
                            option2 = atom+" and "
                            if option1 in predicate:
                                predicate = predicate.replace(option1,'')
                            elif option2 in predicate:
                                predicate = predicate.replace(option2,'')
                            else:
                                predicate = predicate.replace(atom,'')
                            dataForNNVariables[var] = assignVariableValue(atom,"notin",variables)
                            nonNumericVariables.append(var)
    atoms = predicate.rsplit(" and ")
    for atom in atoms:
        atom_free_vars = getFreeVariables(atom, variables)
        if len(atom_free_vars)==1 and atom_free_vars[0] in nonNumericVariables:
            if satisfy(atom,dataForNNVariables):
                option1 = " and "+atom
                option2 = atom+" and "
                if option1 in predicate:
                    predicate = predicate.replace(option1,'')
                elif option2 in predicate:
                    predicate = predicate.replace(option2,'')
                else:
                    predicate = predicate.replace(atom,'')
            else:
                return 'error', nonNumericVariables, dataForNNVariables
        elif '=' in atom and not '!=' in atom and '>=' not in atom and '<=' not in atom and len(atom_free_vars)==1 and atom_free_vars[0]==atom.rsplit('=')[0]:
            option1 = " and "+atom
            option2 = atom+" and "
            if option1 in predicate:
                predicate = predicate.replace(option1,'')
            elif option2 in predicate:
                predicate = predicate.replace(option2,'')
            else:
                predicate = predicate.replace(atom,'')
            nonNumericVariables.append(atom_free_vars[0])
            dataForNNVariables[atom_free_vars[0]] = assignVariableValue(atom,'=',variables)
    atoms = predicate.rsplit(" and ")
    for atom in atoms:
        atom_free_vars = getFreeVariables(atom, variables)
        if len(atom_free_vars)==1 and atom_free_vars[0] in nonNumericVariables:
            if satisfy(atom,dataForNNVariables):
                option1 = " and "+atom
                option2 = atom+" and "
                if option1 in predicate:
                    predicate = predicate.replace(option1,'')
                elif option2 in predicate:
                    predicate = predicate.replace(option2,'')
                else:
                    predicate = predicate.replace(atom,'')
            else:
                return 'error', nonNumericVariables, dataForNNVariables
    atoms = predicate.rsplit(" and ")
    for atom in atoms:
        predicate = predicate.replace(atom,oPSO.evalPred(atom,dataForNNVariables))
    #Returns updated predicate, a list of all variables removed and its corresponding value
    return predicate, nonNumericVariables, dataForNNVariables

#Function to generate all test cases, one per Test Condition
def generateCases(testConditions,defConditions,input_Variables,output_Variables, onlyInputData, onlyOutputData, input_test_data):
    #Initialize particle size for particle swarm optimization algorithm
    particle_size = 50
    test_cases = []
    if onlyOutputData:
        predicate = defConditions[0]
        div_predicate = predicate.rsplit(" and ")
        predicate=''
        for i,atom in enumerate(div_predicate):
            if "forall" in atom:
                atom = atom.replace("forall",'')
                div_predicate[i] = "forall" + atom.replace(atom,oPSO.evalPred(atom,input_test_data))
            else:
                div_predicate[i] = atom.replace(atom,oPSO.evalPred(atom,input_test_data))
            if i==0:
                predicate = div_predicate[0]
            else:
                predicate += " and "+div_predicate[i]
        listOfVariables = []
        typesOfVariables = []
        bounds = []
        list_bounds = {}
        nv = 0
        predicate, nonNumericVariables, dataForNNVariables = enhacePredicate(predicate,output_Variables)
        test_oracle = {}
        if len(predicate)>0:
            for key in output_Variables.keys():
                for var in output_Variables[key]:
                    if var not in nonNumericVariables:
                        listOfVariables.append(var)
                        typesOfVariables.append(key)
                        nv += 1
                        if key == 'int':
                            list_bounds[var] = [-50,500]
                            bounds.append([-50,500])
                        elif key == 'nat':
                            list_bounds[var] = [1,500]
                            bounds.append([1,500])
                        elif key == 'nat0':
                            list_bounds[var] = [0,500]
                            bounds.append([0,500])
                        elif key == 'float+':
                            list_bounds[var] = [1,500]
                            bounds.append([1,500])
            if "forall" in predicate:
                forallStatement = predicate[predicate.index("forall"):]
                domain = forallStatement[forallStatement.index('[')+1:forallStatement.index(']')].split(',')
                predicate = predicate[:predicate.index("forall")-5]
                test_oracle, errorOfOracle = oPSO.PSO(oPSO.objective_function,bounds,particle_size,predicate,nv,listOfVariables,typesOfVariables)
                if errorOfOracle == 0:
                    decision, forAllValue = satisfy(forallStatement,test_oracle)
                    while not decision:
                        for i,key in enumerate(list_bounds.keys()):
                            for j,value in enumerate(domain):
                                if key in value:
                                    if key in forAllValue.keys():
                                        list_bounds[key][j] = forAllValue[key]
                                        bounds[i][j]=forAllValue[key]
                                    test_oracle, errorOfOracle = oPSO.PSO(oPSO.objective_function,bounds,particle_size,predicate,nv,listOfVariables,typesOfVariables)
                                    decision, forAllValue = satisfy(forallStatement,test_oracle)
            else:
                test_oracle, errorOfOracle = oPSO.PSO(oPSO.objective_function,bounds,particle_size,predicate,nv,listOfVariables,typesOfVariables)
        else:
            errorOfOracle = 0
        if errorOfOracle == 0:
            for key in dataForNNVariables.keys():
                test_oracle[key]=dataForNNVariables[key]
            in_data = {}
            out_data = {}
            for key in input_Variables.keys():
                for var in input_Variables[key]:
                    in_data[var] = input_test_data[var]
            for key in output_Variables.keys():
                for var in output_Variables[key]:
                    out_data[var] = test_oracle[var]
            return [in_data,out_data]
        else:
            #print("Error al generar caso de prueba para el predicado: ", defConditions[i])
            #print("Con los datos: ", input_test_data)
            return "Error"
    else:
    #Generate a test case per test condition
        for i,testCond in enumerate(testConditions):
            input_test_data = {}
            #Enhacepredicate function deletes atoms that uses String type, 'inset' or 'notin' operator, and definitions (i.e. x=1), in order to allow PSO algorithm to work correctly
            predicate, nonNumericVariables, dataForNNVariables = enhacePredicate(testConditions[i],input_Variables)
            #If there's a contradiction as (x=2 and x<0) then return Error
            if predicate == 'error':
                return "Error"
            #If predicate's lenght is greater than 0 it means PSO algorithm can find values for the remaining variables
            if len(predicate)>0:
                #Initialize parameters for PSO algorithm (list of variables, types of variables, bounds, number of variables)
                listOfVariables = []
                typesOfVariables = []
                bounds = []
                test_oracle = {}
                nv = 0
                for key in input_Variables.keys():
                    for var in input_Variables[key]:
                        if var not in nonNumericVariables:
                            listOfVariables.append(var)
                            typesOfVariables.append(key)
                            nv += 1
                            if key == 'int':
                                bounds.append([-30,30])
                            elif key == 'nat':
                                bounds.append([1,30])
                            elif key == 'nat0':
                                bounds.append([0,30])
                            elif key == 'float+':
                                bounds.append([0,30])
                input_test_data, errorOfPredicate = oPSO.PSO(oPSO.objective_function,bounds,particle_size,predicate,nv,listOfVariables,typesOfVariables)
            else:
                errorOfPredicate=0
            #If the input data was successfully generated, return it or generate output data
            for key in dataForNNVariables.keys():
                input_test_data[key]=dataForNNVariables[key]
            checkVars = []
            for key in input_test_data.keys():
                checkVars.append(key)
            for key in input_Variables.keys():
                for inVar in input_Variables[key]:
                    if inVar not in checkVars:
                        input_test_data[inVar] = random.randint(0,30)
            #If only input data = True return test data
            if errorOfPredicate == 0 and onlyInputData:
                return input_test_data
            #If error = 0 and only input data = False, calculate values for output variables (oracle task)
            elif errorOfPredicate == 0 and not onlyInputData:
                #Reset parameters for PSO algorithm and instantiate input variables in definition condition
                predicate = defConditions[i]
                div_predicate = predicate.rsplit(" and ")
                predicate=''
                for i,atom in enumerate(div_predicate):
                    if "forall" in atom:
                        atom = atom.replace("forall",'')
                        div_predicate[i] = "forall" + atom.replace(atom,oPSO.evalPred(atom,input_test_data))
                    else:
                        div_predicate[i] = atom.replace(atom,oPSO.evalPred(atom,input_test_data))
                    if i==0:
                        predicate = div_predicate[0]
                    else:
                        predicate += " and "+div_predicate[i]
                listOfVariables = []
                typesOfVariables = []
                bounds = []
                list_bounds = {}
                nv = 0
                predicate, nonNumericVariables, dataForNNVariables = enhacePredicate(predicate,output_Variables)
                test_oracle = {}
                if len(predicate)>0:
                    for key in output_Variables.keys():
                        for var in output_Variables[key]:
                            if var not in nonNumericVariables:
                                listOfVariables.append(var)
                                typesOfVariables.append(key)
                                nv += 1
                                if key == 'int':
                                    list_bounds[var] = [-50,500]
                                    bounds.append([-50,500])
                                elif key == 'nat':
                                    list_bounds[var] = [1,500]
                                    bounds.append([1,500])
                                elif key == 'nat0':
                                    list_bounds[var] = [0,500]
                                    bounds.append([0,500])
                                elif key == 'float+':
                                    list_bounds[var] = [1,500]
                                    bounds.append([1,500])
                    if "forall" in predicate:
                        forallStatement = predicate[predicate.index("forall"):]
                        domain = forallStatement[forallStatement.index('[')+1:forallStatement.index(']')].split(',')
                        predicate = predicate[:predicate.index("forall")-5]
                        test_oracle, errorOfOracle = oPSO.PSO(oPSO.objective_function,bounds,particle_size,predicate,nv,listOfVariables,typesOfVariables)
                        if errorOfOracle == 0:
                            decision, forAllValue = satisfy(forallStatement,test_oracle)
                            while not decision:
                                for i,key in enumerate(list_bounds.keys()):
                                    for j,value in enumerate(domain):
                                        if key in value:
                                            if key in forAllValue.keys():
                                                list_bounds[key][j] = forAllValue[key]
                                                bounds[i][j]=forAllValue[key]
                                            test_oracle, errorOfOracle = oPSO.PSO(oPSO.objective_function,bounds,particle_size,predicate,nv,listOfVariables,typesOfVariables)
                                            decision, forAllValue = satisfy(forallStatement,test_oracle)
                    else:
                        test_oracle, errorOfOracle = oPSO.PSO(oPSO.objective_function,bounds,particle_size,predicate,nv,listOfVariables,typesOfVariables)
                else:
                    errorOfOracle = 0
                if errorOfOracle == 0:
                    for key in dataForNNVariables.keys():
                        test_oracle[key]=dataForNNVariables[key]
                    in_data = {}
                    out_data = {}
                    for key in input_Variables.keys():
                        for var in input_Variables[key]:
                            in_data[var] = input_test_data[var]
                    for key in output_Variables.keys():
                        for var in output_Variables[key]:
                            out_data[var] = test_oracle[var]
                    return [in_data,out_data]
                else:
                    #print("Error al generar caso de prueba para el predicado: ", defConditions[i])
                    #print("Con los datos: ", input_test_data)
                    return "Error"
            else:
                #print("Error al generar caso de prueba para el predicado: ", testConditions[i])
                return "Error"
    return test_cases

#This function generates all forms of a predicate (i.e. having x>=0, extract x>0, x=0)
def getPredicateFamily(guardConditions, input_Variables, defConditions, output_Variables, pre):
    family = {}
    everyone = []
    tests = []
    dicTests = {}
    #Generates all forms of each guard condition
    for k,guard in enumerate(guardConditions):
        family[guard] = []
        guard_copy = guard
        atoms = guard_copy.rsplit(' and ')
        permutation = 0
        for atom in atoms:
            if '>=' in atom:
                permutation += 1
            elif '<=' in atom:
                permutation += 1
            elif '!=' in atom:
                permutation += 1
        permutation = 2**permutation
        ops_found = 2
        switch = True
        for i in range(permutation):
            family[guard].append('')
        for atom in atoms:
            if '>=' in atom:
                for j in range(permutation):
                    if j%(permutation/ops_found)==0:
                        if switch:
                            switch = False
                        else:
                            switch = True
                    if switch:
                        if ops_found == 2 and len(family[guard][j])<2:
                            family[guard][j] += atom.replace('>=','>')
                        else:
                            family[guard][j] += " and " + atom.replace('>=', '>')
                    else:
                        if ops_found == 2 and len(family[guard][j])<2:
                            family[guard][j] += atom.replace('>=','=')
                        else:
                            family[guard][j] += " and " + atom.replace('>=', '=')
                ops_found *= 2
            elif '<=' in atom:
                for j in range(permutation):
                    if j%(permutation/ops_found)==0:
                        if switch:
                            switch = False
                        else:
                            switch = True
                    if switch:
                        if ops_found == 2 and len(family[guard][j])<2:
                            family[guard][j] += atom.replace('<=','<')
                        else:
                            family[guard][j] += " and " + atom.replace('<=', '<')
                    else:
                        if ops_found == 2 and len(family[guard][j])<2:
                            family[guard][j] += atom.replace('<=','=')
                        else:
                            family[guard][j] += " and " + atom.replace('<=', '=')
                ops_found *= 2
            elif '!=' in atom:
                for j in range(permutation):
                    if j%(permutation/ops_found)==0:
                        if switch:
                            switch = False
                        else:
                            switch = True
                    if switch:
                        if ops_found == 2 and len(family[guard][j])<2:
                            family[guard][j] += atom.replace('!=','>')
                        else:
                            family[guard][j] += " and " + atom.replace('!=', '>')
                    else:
                        if ops_found == 2 and len(family[guard][j])<2:
                            family[guard][j] += atom.replace('!=','<')
                        else:
                            family[guard][j] += " and " + atom.replace('!=', '<')
                ops_found *= 2
            else:
                for j in range(permutation):
                    if len(family[guard][j])<2:
                        family[guard][j] += atom
                    else:
                        family[guard][j] += " and " + atom
        for element in family[guard]:
            if pre == "True":
                tc = generateCases([element],[defConditions[k]], input_Variables, output_Variables, False, False, [])
                if tc != "Error":
                    tests.append(tc.copy())
                    dicTests[element] = tc.copy()
            else:
                tc = generateCases([pre+" and "+element],[defConditions[k]], input_Variables, output_Variables, False, False, [])
                if tc != "Error":
                    tests.append(tc.copy())
                    dicTests[element] = tc.copy()
    for key in family.keys():
        for individual in family[key]:
            if pre == "True":
                everyone.append(individual)
            else:
                everyone.append(pre+" and "+individual)
    return family, everyone, tests, dicTests

#This function generates mutants from each guard condition and a test case for each mutant
def getMutants(families, everyone, pre, input_Variables, defConditions, output_Variables):
    new_mutants = []
    all_mutants = []
    rejected_mutants = []
    #Generate mutants for each family member
    for i,key in enumerate(families.keys()):
        if pre == "True":
            fullTestCond = key
        else:
            fullTestCond = pre + " and " + key
        for individual in families[key]:
            #Save the corresponding definition condition
            definitionCondition = defConditions[i]
            if pre == "True":
                partial_testCond = individual
            else:
                partial_testCond = pre + " and " + individual
            #Split guard condition into atoms
            guardAtoms = individual.rsplit(' and ')
            #Mutate each atom in the guard condition
            for atom in guardAtoms:
                #Identify relational operator in atom
                logicOperator = searchAtomOp(atom)
                atom_copy = atom
                test_copy = partial_testCond
                freePass = False
                #Find logic operator in atom, mutate it and save valid mutants
                if logicOperator == '>':
                    atom_copy = atom_copy.replace('>','=')
                    test_copy = test_copy.replace(atom,atom_copy)
                    if atom_copy.replace('=', '<') not in test_copy and atom_copy.replace('=', '>') not in test_copy and atom_copy.replace('=', '!=') not in test_copy and test_copy not in everyone:
                        new_input_data = generateCases([test_copy],[definitionCondition],input_Variables,output_Variables, True, False, [])
                        everyone.append(test_copy)
                        if new_input_data != "Error":
                            new_mutants.append(test_copy)
                        else:
                            rejected_mutants.append(test_copy)
                    test_copy = test_copy.replace(atom_copy,atom_copy.replace('=','<'))
                    if atom_copy not in test_copy and atom_copy.replace('=', '>=') not in test_copy and atom_copy.replace('=', '>') not in test_copy and test_copy not in everyone:
                        new_input_data = generateCases([test_copy],[definitionCondition],input_Variables,output_Variables, True, False, [])
                        everyone.append(test_copy)
                        if new_input_data != "Error":
                            new_mutants.append(test_copy)
                        else:
                            rejected_mutants.append(test_copy)
                elif logicOperator == '<':
                    atom_copy = atom_copy.replace('<','=')
                    test_copy = test_copy.replace(atom,atom_copy)
                    if atom_copy.replace('=', '<') not in test_copy and atom_copy.replace('=', '>') not in test_copy and atom_copy.replace('=', '!=') not in test_copy and test_copy not in everyone:
                        new_input_data = generateCases([test_copy],[definitionCondition],input_Variables,output_Variables, True, False, [])
                        everyone.append(test_copy)
                        if new_input_data != "Error" and test_copy not in testConditions and test_copy not in all_mutants:
                            new_mutants.append(test_copy)
                        elif new_input_data == "Error":
                            rejected_mutants.append(test_copy)
                    test_copy = test_copy.replace(atom_copy,atom_copy.replace('=','>'))
                    if atom_copy not in test_copy and atom_copy.replace('=', '<=') not in test_copy and atom_copy.replace('=', '<') not in test_copy and test_copy not in everyone:
                        new_input_data = generateCases([test_copy],[definitionCondition],input_Variables,output_Variables, True, False, [])
                        everyone.append(test_copy)
                        if new_input_data != "Error":
                            new_mutants.append(test_copy)
                        else:
                            rejected_mutants.append(test_copy)
                elif logicOperator == '=':
                    atom_copy = atom_copy.replace('=','>')
                    test_copy = test_copy.replace(atom,atom_copy)
                    if atom_copy.replace('>', '=') not in test_copy and atom_copy.replace('>', '<') not in test_copy and atom_copy.replace('>', '<=') not in test_copy and test_copy not in everyone:
                        new_input_data = generateCases([test_copy],[definitionCondition],input_Variables,output_Variables, True, False, [])
                        everyone.append(test_copy)
                        if new_input_data != "Error":
                            new_mutants.append(test_copy)
                        else:
                            rejected_mutants.append(test_copy)
                    test_copy = test_copy.replace(atom_copy,atom_copy.replace('>','<'))
                    if atom_copy not in test_copy and atom_copy.replace('>', '>=') not in test_copy and atom_copy.replace('>', '=') not in test_copy and test_copy not in everyone:
                        new_input_data = generateCases([test_copy],[definitionCondition],input_Variables,output_Variables, True, False, [])
                        everyone.append(test_copy)
                        if new_input_data != "Error":
                            new_mutants.append(test_copy)
                        else:
                            rejected_mutants.append(test_copy)
                elif logicOperator == 'inset':
                    atom_copy = atom_copy.replace('inset','notin')
                    test_copy = test_copy.replace(atom,atom_copy)
                    if test_copy not in everyone:
                        new_mutants.append(test_copy)
                        everyone.append(test_copy)
                elif logicOperator == 'notin':
                    atom_copy = atom_copy.replace('notin','inset')
                    test_copy = test_copy.replace(atom,atom_copy)
                    if test_copy not in everyone:
                        new_mutants.append(test_copy)
                        everyone.append(test_copy)
    #New mutants has all valid mutants, here identify the satisfied test condition for data generated from each mutant
    tests = []
    mut_tests = {}
    for j in range(len(new_mutants)):
        newMutData = generateCases([new_mutants[j]],[definitionCondition],input_Variables,output_Variables, True, False, [])
        if newMutData != "Error":
            for i,key in enumerate(families.keys()):
                if pre == "True":
                    fullTestCond = key
                else:
                    fullTestCond = pre + " and " + key
                #If data from mutant satisfies test condition then append it
                if satisfy(fullTestCond,newMutData):
                    tc = generateCases([new_mutants[j]],[defConditions[i]],input_Variables,output_Variables, False, True, newMutData)
                    mut_tests[new_mutants[j]+" implies "+defConditions[i]] = tc.copy()
                    tests.append(tc.copy())
    return tests, mut_tests

#This function generates a python UnitTest file
def build_python_test_file(name, cases):
    file_name = "/home/roman/Documents/Maestria/venv/bin/test_"+name+".py"
    file = open(file_name,"w+")
    file.write("from unittest import TestCase \n")
    import_name = "from "+name+" import "+name+" \n\n"
    file.write(import_name)
    name_of_class = "class "+name+"Test(TestCase):\n"
    file.write(name_of_class)
    for i,case in enumerate(cases):
        file.write("\tdef test_"+str(i)+"(self):\n")
        oneReturnValue = True
        for j,key in enumerate(case[1].keys()):
            if j>0:
                oneReturnValue = False
        if oneReturnValue:
            argument = "self.assertEqual("+name+'('
            for j,key in enumerate(case[0].keys()):
                if j==0:
                    argument += str(case[0][key])
                else:
                    argument += ','+str(case[0][key])
            argument += "),"
            for j,key in enumerate(case[1].keys()):
                if j==0:
                    argument += str(case[1][key])
                else:
                    argument += ','+str(case[1][key])
            argument += ")\n"
            file.write("\t\t"+argument)
        else:
            for j,key in enumerate(case[1].keys()):
                if j==0:
                    substraction = key
                else:
                    substraction += ','+key
            substraction += " = "+name+'('
            for j,key in enumerate(case[0].keys()):
                if j==0:
                    substraction += str(case[0][key])
                else:
                    substraction += ','+str(case[0][key])
            substraction += ')\n'
            file.write("\t\t"+substraction)
            for j,key in enumerate(case[1].keys()):
                argument = "self.assertEqual("+key+','+str(case[1][key])+')\n'
                file.write("\t\t"+argument)
    file.close()

def testRawSpecs(testConditions, defConditions, input_Variables, output_Variables):
    testsRS = []
    for i,testCond in enumerate(testConditions):
        tc = generateCases([testCond],[defConditions[i]], input_Variables, output_Variables, False, False, [])
        testsRS.append(tc.copy())
    return testsRS

#Load the specs file
start = time.time()
#Jorgensen Examples
#specs_file = open("/home/roman/Documents/Maestria/projects/Test_Case_Generation/triangleProblemSpecs.txt")
#specs_file = open("/home/roman/Documents/Maestria/projects/Test_Case_Generation/NextDateSpecs.txt")
#specs_file = open("/home/roman/Documents/Maestria/projects/Test_Case_Generation/commissionProblem.txt")
#Liu Examples
specs_file = open("/home/roman/Documents/Maestria/projects/Test_Case_Generation/modFunctionSpecs.txt")
#specs_file = open("/home/roman/Documents/Maestria/projects/Test_Case_Generation/gcd_specification.txt")
#Aditya example
#specs_file = open("/home/roman/Documents/Maestria/projects/Test_Case_Generation/programAdityaSpecs.txt")
#Extra example
#specs_file = open("/home/roman/Documents/Maestria/projects/Test_Case_Generation/multipleVariablesSpecs.txt")

#To see examples
#specs_file = open("/home/roman/Documents/Maestria/projects/Test_Case_Generation/LCMSpecs.txt")
#specs_file = open("/home/roman/Documents/Maestria/projects/Test_Case_Generation/binarySearchSpecs.txt")
SOFL_specs = specs_file.read()
specs_file.close()

#Extract information from specs (pre,post, input variables, output variables)
if 'pre' in SOFL_specs:
    operation_name = SOFL_specs[SOFL_specs.index("process"):SOFL_specs.index('(')].replace('process ','')
    vars_info = SOFL_specs[SOFL_specs.index('process'):SOFL_specs.index('pre')]
    input_Variables, output_Variables = divideVars(vars_info)
    pre = SOFL_specs[SOFL_specs.index('pre')+4:SOFL_specs.index('post')].replace('\n','')
    post = SOFL_specs[SOFL_specs.index('post'):SOFL_specs.index('end_process')]
else:
    pre = 'True'
    operation_name = SOFL_specs[SOFL_specs.index("process"):SOFL_specs.index('(')].replace('process ','')
    vars_info = SOFL_specs[SOFL_specs.index('process'):SOFL_specs.index('post')]
    input_Variables, output_Variables = divideVars(vars_info)
    post = SOFL_specs[SOFL_specs.index('post'):SOFL_specs.index('end_process')]

#Divide guard condition and defining condition from post
testConditions, defConditions = listOfGuards(post)
guardConditions = testConditions.copy()
if 'True' not in pre:
    for i,cond in enumerate(testConditions):
        testConditions[i] = pre + " and "  + cond
if len(testConditions)>0:
    if len(testConditions[len(testConditions)-1]) == 0:
        testConditions.pop(len(testConditions)-1)
        defConditions.pop(len(testConditions)-1)

print("\nSPEC INFO")
print('----------------------------------------------------------------------------------------')
print("Input Variables:")
print(input_Variables)
print("\nOutput Variables:")
print(output_Variables)
print("\nTest Conditions:")
print(testConditions)
print("\nDefinition Conditions:")
print(defConditions)

#Test for raw specs
testsSpecs = testRawSpecs(testConditions, defConditions, input_Variables, output_Variables)
time_raw_specs = time.time()

#Generate mutants 
print("\n\nMUTANTS")
print('----------------------------------------------------------------------------------------')
families, everyone, familiesTests, dicFamiliesTests = getPredicateFamily(guardConditions, input_Variables, defConditions, output_Variables, pre)
time_predicateFamilies = time.time()
just_tests, mutant_tests = getMutants(families, everyone, pre, input_Variables, defConditions, output_Variables)
time_generating_mutants = time.time()
print("Raw specs time:", time_raw_specs-start)
print("Pred decomposition time: ", time_predicateFamilies - start)
print("Time mutants: ", time_generating_mutants-start)

#Number of test cases
print("Number of raw test cases:", len(testsSpecs))
print("Number of fam test cases:", len(familiesTests))
print("Number of mutant test cases:", len(just_tests))

#Generate test for mutants
print("\n\nTEST CASES")
print('----------------------------------------------------------------------------------------')
for famtest in dicFamiliesTests.keys():
    print("Predicate: ", famtest)
    print("Test case: ", dicFamiliesTests[famtest])
    print('')
for mtest in mutant_tests:
    print("Predicate:           ", mtest)
    print("Generates test case: ", mutant_tests[mtest])
    print('')
for test in familiesTests:
    just_tests.append(test.copy())
build_python_test_file(operation_name,just_tests)

#mut.py --target nextDate --unit-test test_nextDate -m
#mut.py --target nextDate --unit-test test_nextDate_noMT -m
#mut.py --target multipleVars --unit-test test_multipleVars -m
#mut.py --target multipleVars --unit-test test_multipleVars_noMT -m
#mut.py --target mod --unit-test test_mod -m
#mut.py --target mod --unit-test test_mod_noMT -m
#mut.py --target commission --unit-test test_commission -m
#mut.py --target commission --unit-test test_commission_noMT -m
#mut.py --target triangle --unit-test test_triangle -m
#mut.py --target triangle --unit-test test_triangle_noMT -m
#mut.py --target programAditya --unit-test test_programAditya -m
#mut.py --target programAditya --unit-test test_programAditya_noMT -m
#mut.py --target gcd --unit-test test_gcd -m
#mut.py --target gcd --unit-test test_gcd_noMT -m
#mut.py --target LCM --unit-test test_LCM -m
