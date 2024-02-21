RHSItem: B[..] | LHS

Production:
     LHS := RHSItem & RHSItem & ...
 |   LHS := LHS | LHS | ...
     assert(..) 
     assert(..) 
     ...

BNF: a list of Productions

def cmp_BNF (BNF1, BNF2):
    # S1, S2 are the first product of BNF1, BNF2
    cmp_product(S1, S2)
    
def cmp_product (product1, product2):
    # conjunction: B[..]L[]B[..]L[] or B[..]B[..]
    if product1.getRHS() is conjunction, product2.getRHS() is conjunction:
        for conj1, conj2 in enumerate(product1,getRHS(), product2.getRHS()):
            if conj1 is B[..] and conj2 is B[..]:
                cmp_asserts(conj1, conj2) # the assertions related to conj1, conj2 are in conjunction form
            else if conj1 is L[] and conj2 is L[]:
                cmp_product(conj1,conj2)

    # disjunction: L[]|L[]|L[]
    else if product1.getRHS() is disjunction and product2.getRHS() is disjunction:
        # group disjuntions with the same RHS in product1 and product2
        map<RHS, <list<LHS>>> m1,m2
        for RHS in m1:
            init F1, F2
            for LHS in m1[RHS]:
                F1 = F1 | GetAsserts1(LHS)
            for LHS in m2[RHS]:
                F2 = F2 | GetAsserts2(LHS)
            if cmp_asserts(F1, F2) == False:
                cmp_Formula(F1, F2) # F1, F2 are in disjunction form

def cmp_Formula(F1, F2):
    packet = SMT_solver(F1 != F2)
    if packet unsatisfy F1:
        condition = UNSAT_Core(F1 and packet)
    if packet unsatisfy F2:
        condition = UNSAT_Core(F2 and packet)


