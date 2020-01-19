from pysmt.shortcuts import Symbol, Not, And, Or, Implies, Ite, BVAdd, BV
from pysmt.shortcuts import is_sat, is_unsat, Solver, TRUE
from pysmt.typing import BOOL, BVType
a = Symbol('a', BVType(4))
b = Symbol('b', BVType(4))
c = Symbol('c', BVType(4))
s = Solver(name='z3')
s.solve([Ite(a.Equals(0),b,c).Equals(4)])
md = s.get_model()
print (md)
for v,val in md:
  #val = md.get_value(v, False)
  print (v,'=',val)
  print ('v is a', v is a)
  print ('v is b', v is b)
print (c in md)
