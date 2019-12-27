from pysmt.shortcuts import Symbol, Not, And, Or, Implies, Ite, BVAdd, BV
from pysmt.shortcuts import is_sat, is_unsat, Solver, TRUE
from pysmt.typing import BOOL, BVType

nbits = 4

base = Symbol('base', BVType(nbits))
addr = Symbol('addr', BVType(nbits))
cnt  = Symbol('cnt',  BVType(nbits))

solver = Solver()

solver.solve([base.Equals(0)])

for v, val in solver.get_model():
    print (val)
    print (val)
    print (val.bv_str())\

tg1 = base.Equals(0)
print (tg1.to_smtlib(daggify=True))
