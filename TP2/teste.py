from pysmt.shortcuts import *
from pysmt.typing import INT
import random as rn

def BVLast(n):
    return BV(2**(n-1),n)
# vou declarar aqui um exemplo depois passamos para exemplos separados
n = 5 # [0,0] [0,1] [1,0] [1,1]
a = 5
b = 2
k = 2*n
def toInt(s):
    return sum([int(x)*2**(len(s)-i-1) for i,x in (enumerate(s))])


print('x = ', BV(a,n).bv_str())
print('y = ', BV(b,n).bv_str())


x = Symbol('x'+str(0),types.BVType(n))
y = Symbol('y'+str(0),types.BVType(n))

print(BV(2**(n-1),n).bv_str())


print(is_sat(Equals(BVAnd(y,BVOne(n)),BVZero(n))))
print(is_sat(Equals(BVAnd(x,BV(2**(n-1),n)),BVZero(n))))
print(is_sat(And(Equals(x,BV(a,n)), Equals(BVAnd(x,BV(2**(n-1),n)),BVZero(n)))))



def tError(curr,prox):
    tPcZero = Equals(curr['pc'],Int(0))
    tYLast = Equals(BVAnd(curr['y'],BVOne(n)),BVZero(n))
    tXFirst = Equals(BVAnd(curr['x'],BV(2**(n-1),n)),BVOne(n))
    tX = Equals(prox['x'], curr['x'])
    tY = Equals(prox['y'],curr['y'])
    tZ = Equals(prox['z'],curr['z'])
    tPc = Equals(prox['pc'],Int(2))
    return And(tPcZero,tYLast,tXFirst,tX,tY,tZ,tPc)



