from pysmt.shortcuts import Symbol, Not, And, Or, Implies, Ite, BVAdd, BV, BVExtract
from pysmt.shortcuts import is_sat, is_unsat, Solver,Interpolator, TRUE
from pysmt.typing import BOOL, BVType
from pysmt.logics import QF_BV

a = Symbol('a', BVType(8))
b = Symbol('b', BVType(8))
c = Symbol('c', BVType(4))

s = Solver(name='msat')

b_plus_0 = BVAdd(BVExtract(b,start = 0, end = 3),Ite(BVExtract(a,start = 0, end = 3).Equals(0),BVExtract(a,start = 0, end = 3),BV(0, 4)))
print (s.solve([b_plus_0.Equals(0), b.Equals(1)]))
        


itp_solver = Interpolator(logic=QF_BV)
Itp = itp_solver.binary_interpolant( a = b_plus_0.Equals(0), b= b.Equals(1) )
print (Itp)



