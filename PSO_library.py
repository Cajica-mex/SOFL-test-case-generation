import random
import math
import numpy as np
from math import fmod

#Predicate treatment to generate values
#------------------------------------------------------------
def evalPred(thecase,valueOfVars):
    for key in valueOfVars.keys():
        if key+' ' in thecase:
            thecase = thecase.replace(key,str(valueOfVars[key]))
        elif ' '+key in thecase:
            thecase = thecase.replace(key,str(valueOfVars[key]))
        elif '+'+key in thecase:
            thecase = thecase.replace(key,str(valueOfVars[key]))
        elif '-'+key in thecase:
            thecase = thecase.replace(key,str(valueOfVars[key]))
        elif '/'+key in thecase:
            thecase = thecase.replace(key,str(valueOfVars[key]))
        elif '*'+key in thecase:
            thecase = thecase.replace(key,str(valueOfVars[key]))
        elif '='+key in thecase:
            thecase = thecase.replace(key,str(valueOfVars[key]))
        elif '<'+key in thecase:
            thecase = thecase.replace(key,str(valueOfVars[key]))
        elif '>'+key in thecase:
            thecase = thecase.replace(key,str(valueOfVars[key]))
        elif '!'+key in thecase:
            thecase = thecase.replace(key,str(valueOfVars[key]))
        elif '|'+key in thecase:
            thecase = thecase.replace(key,str(valueOfVars[key]))
        elif '['+key in thecase:
            thecase = thecase.replace(key,str(valueOfVars[key]))
        elif key+'+' in thecase:
            thecase = thecase.replace(key,str(valueOfVars[key]))
        elif key+'-' in thecase:
            thecase = thecase.replace(key,str(valueOfVars[key]))
        elif key+']' in thecase:
            thecase = thecase.replace(key,str(valueOfVars[key]))
        elif key+'*' in thecase:
            thecase = thecase.replace(key,str(valueOfVars[key]))
        elif key+'/' in thecase:
            thecase = thecase.replace(key,str(valueOfVars[key]))
        elif key+'%' in thecase:
            thecase = thecase.replace(key,str(valueOfVars[key]))
        elif key+'=' in thecase:
            thecase = thecase.replace(key,str(valueOfVars[key]))
        elif key+'>' in thecase:
            thecase = thecase.replace(key,str(valueOfVars[key]))
        elif key+'!' in thecase:
            thecase = thecase.replace(key,str(valueOfVars[key]))
        elif key+'<' in thecase:
            thecase = thecase.replace(key,str(valueOfVars[key]))
        elif key+'|' in thecase:
            thecase = thecase.replace(key,str(valueOfVars[key]))
    return thecase

def findRelationalOperator(atom):
    if ">=" in atom:
        return ">="
    elif "<=" in atom:
        return "<="
    elif '<' in atom:
        return '<'
    elif '>' in atom:
        return '>'
    elif "!=" in atom:
        return "!="
    elif '=' in atom:
        return '='
    elif "inset" in atom:
        return "inset"
    elif "notin" in atom:
        return "notin"

def findAritmeticOperators(atom):
    aritOps = []
    for e in atom:
        if e == '+':
            aritOps.append('+')
        elif e == '-':
            aritOps.append('-')
        elif e == '*':
            aritOps.append('*')
        elif e == '/':
            aritOps.append('/')
        elif e == '%':
            aritOps.append('%')
        elif e == '|':
            aritOps.append('|')
    return aritOps


def kindOfErrorMethod(rightSide,leftSide, relationalOperator):
    rightSide = float(rightSide)
    leftSide = float(leftSide)
    if relationalOperator == '>':
        error = leftSide-rightSide-1
        if error > 0:
            error = 0
        else:
            error = abs(error)
    elif relationalOperator == '<':
        error = rightSide-1-leftSide
        if error > 0:
            error = 0
        else:
            error = abs(error)
    elif relationalOperator == ">=":
        error = leftSide-rightSide
        if error > 0:
            error = 0
        else:
            error = abs(error)
    elif relationalOperator == "<=":
        error = rightSide-leftSide
        if error > 0:
            error = 0
        else:
            error = abs(error)
    elif relationalOperator == "!=":
        if rightSide-leftSide != 0:
            error = 0
        else:
            error = 1
    else:
        error = abs(rightSide-leftSide)
    return error

def computeAbs(side):
    parts = side.rsplit('|')
    absPart = parts[1]
    calculation = abs(float(str(eval(absPart))))
    side = side.replace('|','').replace(absPart,str(calculation))
    return side

def computeErrorOnAtom(atom):
    relationalOperator = findRelationalOperator(atom)
    rightSide = atom.rsplit(relationalOperator)[1]
    leftSide = atom.rsplit(relationalOperator)[0]
    if relationalOperator != "inset" and relationalOperator != "notin":
        rightAritmeticOperators = findAritmeticOperators(rightSide)
        leftAritmeticOperators = findAritmeticOperators(leftSide)
        if '|' in rightAritmeticOperators:
            rightSide = computeAbs(rightSide)
        if '|' in leftAritmeticOperators:
            leftSide = computeAbs(leftSide)
        if len(rightAritmeticOperators)>0:
            rightSide = str(eval(rightSide))
        if len(leftAritmeticOperators)>0:
            leftSide = str(eval(leftSide))
        error = kindOfErrorMethod(rightSide,leftSide, relationalOperator)
    else:
        error = 0
    return error
#End of predicate section

#Particle swarm optimization algorithm
#-----------------------------------------------------------------------------------------------
#Define the objective function: sum of every predicate error
def objective_function(case, particlePosition):
    atoms = case.rsplit(" and ")
    errorFunction = 0
    for atom in atoms:
        evalAtom = evalPred(atom,particlePosition)
        errorFunction += computeErrorOnAtom(evalAtom)
    return errorFunction

class Particle:
    def __init__(self,bounds,initial_fitness,test_case,nv,listOfVariables, typesOfVariables):
        self.particle_position=[]                     # particle position
        self.particle_velocity=[]                     # particle velocity
        self.local_best_particle_position=[]          # best position of the particle
        self.fitness_local_best_particle_position = initial_fitness 
        self.fitness_particle_position = initial_fitness
        self.particle_position_with_variables = {}
        self.case = test_case
        for i in range(nv):
            if typesOfVariables[i] == 'int' or typesOfVariables[i] == 'nat' or typesOfVariables[i] == 'nat0':
                self.particle_position.append(round(random.uniform(bounds[i][0],bounds[i][1]))) #Generate random integer initial position
            else:
                self.particle_position.append(random.uniform(bounds[i][0],bounds[i][1])) #Generate random float initial position
            self.particle_velocity.append(random.uniform(-1,1)) #Generate random initial velocity
            self.particle_position_with_variables[listOfVariables[i]]=self.particle_position[i]

    def evaluate(self,objective_function,test_case):
        self.fitness_particle_position = objective_function(self.case,self.particle_position_with_variables)
        if self.fitness_particle_position < self.fitness_local_best_particle_position:
            self.local_best_particle_position = self.particle_position                  # update the local best
            self.fitness_local_best_particle_position = self.fitness_particle_position  # update the fitness of the local best
 
    def update_velocity(self,global_best_particle_position,w,nv):
        c1=1                                # Cognative constant
        c2=2                                # Social constant
        for i in range(nv):
            r1=random.random()
            r2=random.random()
  
            cognitive_velocity = c1*r1*(self.local_best_particle_position[i] - self.particle_position[i])
            social_velocity = c2*r2*(global_best_particle_position[i] - self.particle_position[i])
            self.particle_velocity[i] = w*self.particle_velocity[i]+ cognitive_velocity + social_velocity
  
    def update_position(self,bounds,nv,listOfVariables, typesOfVariables):
        for i in range(nv):
            if typesOfVariables[i] == 'int' or typesOfVariables[i] == 'nat' or typesOfVariables[i] == 'nat0':
                self.particle_position[i]=round(self.particle_position[i]+self.particle_velocity[i])
            else:
                self.particle_position[i]=self.particle_position[i]+self.particle_velocity[i]
            # check and repair to satisfy the upper bounds
            #if self.particle_position[i]>bounds[i][1]:
            #    self.particle_position[i]=bounds[i][1]
            #check and repair to satisfy the lower bounds
            if self.particle_position[i]<bounds[i][0]:
                self.particle_position[i]=bounds[i][0]
                if self.particle_velocity[i]<0:
                    self.particle_velocity[i] *= -1
            self.particle_position_with_variables[listOfVariables[i]] = self.particle_position[i]
    
    def restart_particle(self,bounds,initial_fitness,test_case,nv,listOfVariables, typesOfVariables):
        self.particle_position=[]                     # particle position
        self.particle_velocity=[]                     # particle velocity
        self.local_best_particle_position=[]          # best position of the particle
        self.fitness_local_best_particle_position = initial_fitness 
        self.fitness_particle_position = initial_fitness
        self.particle_position_with_variables = {}
        self.case = test_case
        for i in range(nv):
            if typesOfVariables[i] == 'int' or typesOfVariables[i] == 'nat' or typesOfVariables[i] == 'nat0':
                self.particle_position.append(round(random.uniform(bounds[i][0],bounds[i][1]))) #Generate random integer initial position
            else:
                self.particle_position.append(random.uniform(bounds[i][0],bounds[i][1])) #Generate random float initial position
            self.particle_velocity.append(random.uniform(-1,1)) #Generate random initial velocity
            self.particle_position_with_variables[listOfVariables[i]]=self.particle_position[i]
    
    def setPosition(self,new_particle_position,nv,listOfVariables):
        self.particle_position=new_particle_position.copy()                     #set particle position
        for i in range(nv):
            self.particle_position_with_variables[listOfVariables[i]]=self.particle_position[i] #Set particle position

    def findingValues(self,nv,bounds,particle_size,listOfVariables, typesOfVariables):
        copy_bounds = bounds.copy()
        copy_listOfVariables = listOfVariables.copy()
        copy_typesOfVariables = typesOfVariables.copy()
        if nv-1 > 0:    
            copy_nv = nv-1
            for i in range(nv):
                valuedVariable = {}
                valuedVariable[copy_listOfVariables.pop(i)] = self.particle_position[i]
                copy_bounds.pop(i)
                copy_typesOfVariables.pop(i)
                new_test_case = evalPred(self.case,valuedVariable)
                position, error = PSO(objective_function,copy_bounds,particle_size,new_test_case,copy_nv,copy_listOfVariables, copy_typesOfVariables)
                if error == 0:
                    for key in position.keys():
                        valuedVariable[key] = position[key]
                    self.particle_position_with_variables = valuedVariable.copy()
                    for j,key in enumerate(self.particle_position_with_variables.keys()):
                        self.particle_position[j] = self.particle_position_with_variables[key]
                    self.fitness_particle_position = 0
                    break
                else:
                    for key in valuedVariable.keys():
                        valuedVariable[key] += 1
                    new_test_case = evalPred(self.case,valuedVariable)
                    position, error = PSO(objective_function,copy_bounds,particle_size,new_test_case,copy_nv,copy_listOfVariables, copy_typesOfVariables)
                    if error == 0:
                        for key in position.keys():
                            valuedVariable[key] = position[key]
                        self.particle_position_with_variables = valuedVariable.copy()
                        for j,key in enumerate(self.particle_position_with_variables.keys()):
                            self.particle_position[j] = self.particle_position_with_variables[key]
                        self.fitness_particle_position = 0
                        break
                    else:
                        for key in valuedVariable.keys():
                            valuedVariable[key] -= 2
                        new_test_case = evalPred(self.case,valuedVariable)
                        position, error = PSO(objective_function,copy_bounds,particle_size,new_test_case,copy_nv,copy_listOfVariables, copy_typesOfVariables)
                        if error == 0:
                            for key in position.keys():
                                valuedVariable[key] = position[key]
                            self.particle_position_with_variables = valuedVariable.copy()
                            for j,key in enumerate(self.particle_position_with_variables.keys()):
                                self.particle_position[j] = self.particle_position_with_variables[key]
                            self.fitness_particle_position = 0
                            break
                        else:
                            copy_typesOfVariables = typesOfVariables.copy()
                            copy_listOfVariables = listOfVariables.copy()
                            copy_bounds = bounds.copy()
        else:
            valuedVariable = {}
            valuedVariable[copy_listOfVariables.pop(0)] = self.particle_position[0]+1
            new_test_case = evalPred(self.case,valuedVariable)
            error = objective_function(new_test_case,valuedVariable)
            if error == 0:
                for key in self.particle_position_with_variables.keys():
                    self.particle_position_with_variables[key] += 1
                self.particle_position[0] += 1
                self.fitness_particle_position = 0
            else:
                for key in valuedVariable.keys():
                    valuedVariable[key] -= 2
                new_test_case = evalPred(self.case,valuedVariable)
                error = objective_function(new_test_case,valuedVariable)
                if error == 0:
                    for key in self.particle_position_with_variables.keys():
                        self.particle_position_with_variables[key] -= 1
                    self.particle_position[0] -= 1
                    self.fitness_particle_position = 0

#PSO algorithm
def PSO(objective_function,bounds,particle_size,test_case,nv,listOfVariables, typesOfVariables):
    #Not changeable parameters  
    maxIterations = 50                  # Max numer of iterations allowed per cycle
    w=0.6                               # Initial inertia
    wrate=0.001                         # Inertia decreasing rate
    initial_fitness = float('inf')      # Initial fitness value (infinite)
    #Initialize global values
    fitness_global_best_particle_position=initial_fitness
    global_best_particle_position=[]
    swarm_particle=[]
    global_particle = Particle(bounds,initial_fitness,test_case,nv,listOfVariables, typesOfVariables)
    #Create all particles and save them in swarm_particle vector
    for i in range(particle_size):
        swarm_particle.append(Particle(bounds,initial_fitness,test_case,nv,listOfVariables, typesOfVariables))
    i=0         #Number of iterations
    k=1         #Number of resets
    reset = False       #Reset bool variable

    #Start minimizing error down to 0
    while fitness_global_best_particle_position != 0:
        #Calculate error for each particle and save the best
        for j in range(particle_size):
            swarm_particle[j].evaluate(objective_function,test_case)
            if swarm_particle[j].fitness_particle_position < fitness_global_best_particle_position:
                global_best_particle_position = swarm_particle[j].particle_position.copy()
                fitness_global_best_particle_position = float(swarm_particle[j].fitness_particle_position)
        #Update particle's velocity and position
        for j in range(particle_size):
            swarm_particle[j].update_velocity(global_best_particle_position,w,nv)
            swarm_particle[j].update_position(bounds,nv,listOfVariables, typesOfVariables)
        #If the decrease of inertia is more than 0 keep decreasing it
        if w - wrate > 0 :
            w -= wrate                                  #Decrease inertia
        i+=1                                            #Increase number of iterations
        #If error equals 0 then break
        if fitness_global_best_particle_position == 0:
            global_particle.setPosition(global_best_particle_position,nv,listOfVariables)
            break
        #If round(error) equals 0 then a variable it's close to its correct value, do the following to find the right values per variable
        if round(fitness_global_best_particle_position,2) == 0.00:
            #Round each global best particle position value
            for j in range(nv):
                if typesOfVariables[j] == "int" or typesOfVariables[j] == "nat" or typesOfVariables[j] == "nat0":
                    global_best_particle_position[j] = round(global_best_particle_position[j])
                else:
                    global_best_particle_position[j] = round(global_best_particle_position[j],2)
            #Assign that new rounded position to the best global particle and evaluate it
            global_particle.setPosition(global_best_particle_position,nv,listOfVariables)
            global_particle.evaluate(objective_function,test_case)
            #If error equals 0 then save position and break
            if global_particle.fitness_particle_position == 0:
                global_best_particle_position=global_particle.particle_position
                fitness_global_best_particle_position=global_particle.fitness_particle_position
                break
            #Assuming at least one variable is nearby to its correct value, try to find recursively the correct solution    
            global_particle.findingValues(nv,bounds,particle_size,listOfVariables, typesOfVariables)
            #If correct solution was found then save position and break
            if global_particle.fitness_particle_position == 0:
                global_best_particle_position=global_particle.particle_position
                fitness_global_best_particle_position=global_particle.fitness_particle_position
                break
            #If no correct solution was found then reset is set True
            if fitness_global_best_particle_position != 0:
                reset = True
        #If number of restarts reach maximum then break
        if k>50:
            break
        if reset or i>maxIterations*k:
            #Restart particles, best global values and add 1 to number of restarts
            k += 1
            for j in range(nv):
                if global_best_particle_position[j] > bounds[j][1]:
                    bounds[j][1] = global_best_particle_position[j]
            for j in range(particle_size):
                swarm_particle[j].restart_particle(bounds,initial_fitness,test_case,nv,listOfVariables, typesOfVariables)
            fitness_global_best_particle_position = initial_fitness
            global_best_particle_position=[]
            global_particle.restart_particle(bounds,initial_fitness,test_case,nv,listOfVariables, typesOfVariables)
            reset = False
    
    return global_particle.particle_position_with_variables,fitness_global_best_particle_position