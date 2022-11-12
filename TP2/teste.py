from pysmt.shortcuts import *
from pysmt.typing import INT
import random as rn

def PontosProximos(pos):
    return [(pos[0]+1,pos[1]),(pos[0]-1,pos[1]),(pos[0],pos[1]+1),(pos[0],pos[1]-1),(pos[0]-1,pos[1]-1),(pos[0]+1,pos[1]+1),(pos[0]-1,pos[1]+1),(pos[0]+1, pos[1]-1)]


N = 10
i,j = 4,4

print(len(list(filter(lambda x: x[0] < N+1 and x[1] < N+1,  PontosProximos((i,j))))))

d = 0
for k in filter(lambda x: x[0] < N+1 and x[1] < N+1,  PontosProximos((i,j))):
    d += 1
print(d)


print((1,5) < (4,4))