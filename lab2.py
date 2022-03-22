import sys
from itertools import combinations
"""
file: lab2.py
description: This is a program to resolution of CNF clauses using PL-Resolution and Unification Algorithm
language: python3
author: Aditya Ajit Tirakannavar(at2650@rit.edu)
"""
# global keywords
Predicates = []
Variables = []
Constants = []
Functions = []
Clauses = set()

def read_file(filename):
    """
    Reads the input file and stores the data in respective data structure
    :param filename: file name
    :return: None
    """
    with open(filename) as file:
        # read entire file in lines
        lines = file.readlines()
        for line in lines:
            # read line by line and store into the appropriate list/set
            if line.startswith('Predicates:'):
                line = line.replace('Predicates: ', '')
                line = line.strip().split()
                for i in line:
                    Predicates.append(i)
            elif line.startswith('Variables:'):
                line = line.replace('Variables: ', '')
                line = line.strip().split()
                for i in line:
                    Variables.append(i)
            elif line.startswith('Constants:'):
                line = line.replace('Constants: ', '')
                line = line.strip().split()
                for i in line:
                    Constants.append(i)
            elif line.startswith('Functions:'):
                line = line.replace('Functions: ', '')
                line = line.strip().split()
                for i in line:
                    Functions.append(i)
            else:
                if line != '' and not line.startswith('Clauses:'):
                    Clauses.add(line.strip())


def Negation(query: str):
    """
    This function Negates the statement by appending or removing '!' symbol to the query
    :param query: input query
    :return: str: Negated Query
    """
    if query.endswith('!'):
        return query.rstrip('!')
    else:
        return '!' + query


def Unification(a: str, b: str):
    """
    This UNIFY algorithm takes two sentences and returns a unifier for them (a substitution) if one exists
    :param a: expression 1: str
    :param b: expression 2: str
    :return: a,b : tuple
    """
    if a.count(',') == 1 and b.count(',') == 1:
        # check if there are multiple variables associated with single predicate
        # Extracting Variables & constants i.e. whatever that is in round brackets
        a_variable = a[a.index('(') + 1:a.rindex(')')]
        b_variable = b[b.index('(') + 1:b.rindex(')')]
        # split variable further based on ','
        a_var_set = a_variable.split(',')
        b_var_set = b_variable.split(',')
        rem = list()
        # check for valid variables and replace the variable
        for i in range(len(a_var_set)):
            if a_var_set[i] in Variables:
                a = a.replace(a_var_set[i], b_var_set[i])
                rem.append(b_var_set[i])
        for i in rem:
            b_var_set.remove(i)
        for i in range(len(b_var_set)):
            if b_var_set[i] in Variables:
                b = b.replace(b_var_set[i], a_var_set[i])
        return a, b

    else:
        a_variable = a[a.index('(') + 1:a.rindex(')')]
        b_variable = b[b.index('(') + 1:b.rindex(')')]

        if (a.count('(') == 1 and a.count(')') == 1) and (b.count('(') == 1 and b.count(')') == 1):
            # only one variable or const
            if a_variable in Variables:
                a = a.replace(a_variable, b_variable)
            elif b_variable in Variables:
                b = b.replace(b_variable, a_variable)
            return a, b

        else:
            if (a.count('(') == 2 and a.count(')') == 2) and (b.count('(') == 2 and b.count(')') == 2):
                x_function = a[a.index('(') + 1:a.rindex(')')]
                y_function = b[b.index('(') + 1:b.rindex(')')]
                if x_function[:x_function.index('(')] in Functions:
                    a_variable = x_function[x_function.index('(') + 1:x_function.rindex(')')]
                    b_variable = y_function[y_function.index('(') + 1:y_function.rindex(')')]
                    if a_variable in Variables:
                        a = a.replace(a_variable, b_variable)
                    elif b_variable in Variables:
                        b = b.replace(b_variable, a_variable)
                return a, b

            elif (a.count('(') == 1 and a.count(')') == 1) and (b.count('(') == 2 and b.count(')') == 2):
                y_function = b[b.index('(') + 1:b.rindex(')')]
                if y_function[:y_function.index('(')] in Functions:
                    a_variable = a[a.index('(') + 1:a.rindex(')')]
                    if a_variable in Variables:
                        a = a.replace(a_variable, y_function)
                return a, b
            elif (a.count('(') == 2 and a.count(')') == 2) and (b.count('(') == 1 and b.count(')') == 1):
                x_function = a[a.index('(') + 1:a.rindex(')')]
                if x_function[:x_function.index('(')] in Functions:
                    b_variable = b[b.index('(') + 1:b.rindex(')')]
                    if b_variable in Variables:
                        b = b.replace(b_variable, x_function)
                return a, b


def Resolver(C1, C2):
    """
    This function takes 2 clauses and negates either clause and removes the predicate 
    if negation condition is satisfies or else a clause is generated by unification
    :param C1: Clause #1
    :param C2: Clause #1
    :return: result: list : list of resolvents after unification of pairs of clauses
    """
    # return all possibility from two Clauses
    res = list()
    for a in C1.split():
        for b in C2.split():
            x, y = Unification(a, b)
            # Unification two to see if it can be same
            if x == Negation(y) or Negation(x) == y:  
                # Removes the a and b value which can be elimated after the 
                # unification equivalent satifies the negate conditions
                temp1 = C1.strip().split()
                temp1.remove(a)
                temp2 = C2.strip().split()
                temp2.remove(b)
                temp3 = ''
                temp4 = ''
                # check if other predicates remain after elimination
                for i in temp1:
                    if temp3 == '':
                        temp3 = i
                    else:
                        temp3 += (' ' + i)

                for j in temp2:
                    if temp4 == '':
                        temp4 = j
                    else:
                        temp4 += (' ' + j)
                # append the remaining predicates to resolvents list
                if temp3 == '' and temp4 == '':
                    res.append({})
                elif temp4 == '' or temp3 == '':
                        res.append(temp3 + temp4)
                elif temp3 != '' and temp4 != '':
                    res.append(temp3 + ' ' + temp4)
    return res


def Resolution():
    """
    This function is a simple resolution algorithm for propositional logic.
    It returns the set of all possible clauses obtained by resolving its two inputs.
    :return:    'No' :  The empty clause is equivalent to No (True) and the empty clause arises only from
                        resolving two contradictory unit clauses such as P and ¬P
                Else 'Yes'
    """

    new_set = set()
    while True:
        # unique pairs of clauses
        pairs = combinations(Clauses, 2)
        for i in pairs:
            # call resolver function to check if empty clause for all pair of combinations
            resolvents = Resolver(i[0], i[1])
            # if there exists atleast one empty clause for all pair of combinations then return 'No'
            if {} in resolvents:      
                return 'No'
            # update the result of resolver function in new_set
            new_set.update(resolvents)
        # check if the resolver function is generating the same clauses again and again, 
        # if so return 'Yes', meaning empty clause is not possible
        flag = True
        for item in new_set:
            if item not in Clauses:
                flag = False
                break
            else:
                flag = True
        if flag:
            return 'Yes'
        # add new_set elements to clauses set and loop again 
        for i in new_set:
            Clauses.add(i)


def main():
    read_file(sys.argv[1])
    print(Resolution())


if __name__ == '__main__':
    main()