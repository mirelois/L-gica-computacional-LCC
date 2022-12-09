# %% [markdown]
# # TP3
# ## Grupo 15
# 
# Carlos Eduardo Da Silva Machado A96936
# 
# Gonçalo Manuel Maia de Sousa A97485

# %% [markdown]
# ## Problema 1

# %% [markdown]
# ### Descrição do Problema

# %% [markdown]
# 
# 1. Pretende-se construir uma implementação simplificada do algoritmo “model checking” orientado aos interpolantes seguindo a estrutura apresentada nos apontamentos onde no passo $(n,m)\,$na impossibilidade de encontrar um interpolante invariante se dá ao utilizador a possibilidade de incrementar um dos índices $n$ e $m$ à sua escolha.
#     Pretende-se aplicar este algoritmo ao problema da da multiplicação de inteiros positivos em `BitVec`  (apresentado no TP2).

# %% [markdown]
# ### Abordagem do Problema

# %%


# %% [markdown]
# ## Código Python

# %%
from pysmt.shortcuts import *
from pprint import pprint
from pysmt.typing import INT
import random as rn

# %%
def genState(vars,s,i,n):
    state = {}
    for v in vars:
        state[v] = Symbol(v+'!'+s+str(i),types.BVType(n+1))
    return state

def init(state,a,b,n):
    if b > a:
        a,b = b,a
        
    tPc = Equals(state['pc'],BVZero(n+1)) # Program counter a zero
    tZ = Equals(state['z'],BVZero(n+1)) # Z a zero
    tX = Equals(state['x'], BV(a,n+1)) # x inicilizado com valor de a
    tY = Equals(state['y'], BV(b,n+1)) # y inicilizado com valor de b
    return And(tPc,tX,tY,tZ)

# %%
def BVFirst(n):
    return BV(2**(n-1),n)

def tEven(curr,prox,n):
    tPcZero = Equals(curr['pc'],BVZero(n+1))
    tYLast = Equals(BVAnd(curr['y'],BVOne(n+1)),BVZero(n+1))#ultimo bit = 0
    tYGt = BVUGT(curr['y'],BVZero(n+1))#y > 0
    tX = Equals(prox['x'], BVLShl(curr['x'],BVOne(n+1)))#2*x
    tY = Equals(prox['y'], BVLShr(curr['y'],BVOne(n+1)))#y/2
    tZ = Equals(prox['z'],curr['z'])#z
    tPc = Equals(prox['pc'],BVZero(n+1))
    return And(tPcZero,tYLast,tYGt,tX,tY,tZ,tPc)

def tOdd(curr,prox,n):
    tPcZero = Equals(curr['pc'],BVZero(n+1))
    tYLast = Equals(BVAnd(curr['y'],BVOne(n+1)),BVOne(n+1))
    tX = Equals(prox['x'], curr['x'])
    tY = Equals(prox['y'],BVSub(curr['y'],BVOne(n+1)))
    tZ = Equals(prox['z'],BVAdd(curr['x'],curr['z'])) 
    tPc = Equals(prox['pc'],BVZero(n+1))   
    return And(tPcZero,tYLast,tX,tY,tZ,tPc)

def tStop(curr,prox,n):
    tPcZero = Equals(curr['pc'],BVZero(n+1))
    tYZero = Equals(curr['y'],BVZero(n+1))#y=0
    tZFirst = Equals(BVAnd(curr['z'],BVFirst(n+1)),BVZero(n+1))#primriro bit de z = 0
    tX = Equals(prox['x'],curr['x'])
    tY = Equals(prox['y'],curr['y'])
    tZ = Equals(prox['z'],curr['z'])
    tPc = Equals(prox['pc'],BVOne(n+1))
    return And(tYZero,tZFirst,tPcZero,tX,tY,tZ,tPc)

def tEnd(curr,prox,n):
    tPcOne = Equals(curr['pc'],BVOne(n+1))
    tX = Equals(prox['x'],curr['x'])
    tY = Equals(prox['y'],curr['y'])
    tZ = Equals(prox['z'],curr['z'])
    tPc = Equals(prox['pc'],BVOne(n+1))
    return And(tPcOne,tX,tY,tZ,tPc)

def trans(curr,prox,n):
    tToStop = tStop(curr,prox,n)
    tToEven   = tEven(curr,prox,n)
    tToOdd    = tOdd(curr,prox,n)
    tToEnd    = tEnd(curr,prox,n)
    return Or(tToStop,tToEven,tToOdd,tToEnd)

# %%
def error(state,n):
    tYFirst = Equals(BVAnd(state['y'],BVFirst(n+1)),BVFirst(n+1))
    tXFirst = Equals(BVAnd(state['x'],BVFirst(n+1)),BVFirst(n+1))
    tZFirst = Equals(BVAnd(state['z'],BVFirst(n+1)),BVFirst(n+1))
    return Equals(Int(2),Int(3)) 

# %%
def baseName(s):
    return ''.join(list(itertools.takewhile(lambda x: x!='!', s)))

def rename(form,state):
    vs = get_free_variables(form)
    pairs = [ (x,state[baseName(x.symbol_name())]) for x in vs ] # Descobrir os pares # symbol_name dá o nome aka string da var
    return form.substitute(dict(pairs)) # recebe um dicionário e substitui as chaves do dicionário pelo o que está no value

def same(state1,state2): # ver se as duas vars têm o mesmo valor
    return And([Equals(state1[x],state2[x]) for x in state1])

def invert(trans,n):
    return (lambda u, v: trans(v,u,n))

# %%
def model_checking(vars,init,trans,error,N,M,a,b,tamanho):
    with Solver(name="z3") as s:
        
        # Criar todos os estados que poderão vir a ser necessários.
        X = [genState(vars,'X',i,tamanho) for i in range(N+1)] # Com a função genState, criar todos os estados que possam ser necessário, TODOS. # X SFOTS original
        Y = [genState(vars,'Y',i,tamanho) for i in range(M+1)] # Y SFOTS invertido

        # Estabelecer a ordem pela qual os pares (n,m) vão surgir. Por exemplo:
        order = sorted([(a,b) for a in range(1,N+1) for b in range(1,M+1)],key=lambda tup:tup[0]+tup[1]) # Estabelecer ordem que criamos o n e o m # ideia da stora: usar o sorted,
                                                                                                         # gerar todos os pares possíveis 
                                                                                                         # e ter como critério de ordenação as soma dos elementos dos pares
        
        for (n,m) in order: # Seguir o algoritmo
            # completar
            I = init(X[0],a,b,tamanho) # o X é uma lista de estados
            Tn = And([trans(X[i],X[i+1],tamanho) for i in range(n)])
            Rn = And(I,Tn) # estados acessíveis em n transições
            
            E = error(Y[0],tamanho)
            
            print(E.serialize())
            print()
            Bm = And([invert(trans,tamanho)(Y[i],Y[i+1]) for i in range(m)])
            Um = And(E,Bm) # estados inseguros em m transições
            
            Vnm = And(Rn,same(X[n],Y[m]),Um) # temos de testar se dois estados estão iguais e, portanto, usamos a função same dada acima
            
            print(Vnm.serialize())
            
            if s.solve([Vnm]):
                print("unsafe")
                return 
           
            # Se for insatisfazível, temos de criar o interpolante para n fórmulas
            C = binary_interpolant(And(Rn,same(X[n],Y[m])), Um)
            if C is None:
                print("Interpolante None")
                continue
            
            C0 = rename(C,X[0]) # Rename do C com o estado envolvido, neste caso o X[0] 
            C1 = rename(C,X[1])
            # Trabalhamos com X[0] e X[1] porque T pode ser escrito como T = (X0,X1)
            
            T = trans(X[0],X[1])
            
            if not s.solve([C0,T,Not(C1)]):
                print("Safe")
                return
            else:
                    #### gerar o S (Parte que descreve o Majorante S)
                
                #Passo 1:
                S = rename(C,X[n])
                while True:
                    #Passo 2:
                    A = And(S,trans(X[n],Y[m],tamanho))
                    if s.solve([A,Um]):
                        print("Não foi possível encontrar o majorante.")
                        break
                    else:
                        CNew = binary_interpolant(A,Um) # as duas formulas têm de ser inconsistentes para que faça sentido para usar binary_interpolant
                        Cn = rename(CNew,X[n])
                        
                        if s.solve([Cn,Not(S)]):
                            S = Or(S,Cn)
                        else:
                            print("Safe")
                            return
            
        print("unknown")    

# %%
model_checking(['pc','x','y','z'], init, trans, error, 100, 100,1,1,100)    


