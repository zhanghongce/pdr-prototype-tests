from pysmt.shortcuts import Symbol, Not, And, Or, Implies, Ite, BVAdd, BV
from pysmt.shortcuts import is_sat, is_unsat, Solver, TRUE
from pysmt.typing import BOOL, BVType
from pysmt.solvers.interpolation import Interpolator

a = Symbol('a', BVType(4))
b = Symbol('b', BVType(4))
c = Symbol('c', BVType(4))

s = Solver()
b_plus_0 = BVAdd(b,Ite(a.Equals(0),a,BV(0, 4)))
print (s.solve([Not(b_plus_0.Equals(b))]))

md = s.get_model()

