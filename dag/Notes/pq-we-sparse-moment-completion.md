---
title: Sparse NAND constraints admit explicit low-rank normalized moments
refs: [note:pq-we-private-moment-products, note:pq-we-gate-moment-noise]
tags: [witness-encryption, compilation, rank, complexity]
---

For the raw NAND compiler with N>=1 wires and G<=N gates, the symmetric moment matrix has d=N+1 rows, k=d(d+1)/2 coordinates and at most N+G+1 independent gate/Boolean/output equations. Its kernel dimension h therefore satisfies 2h >= N²+N-2G >= N²-N. For N>=3 this already exceeds d, so the previous coarse sufficient inequality rho>=2h+s for positive s cannot certify even one such raw compiler instance having a normalized affine moment. If no normalized moment exists, the shift vanishes in the quotient and hiding is exact. The counting argument alone says nothing about the tighter Fourier sum.

**Which directions can carry rank?** An off-diagonal entry between distinct wires occurs in a gate test only when those wires are inputs of the same NAND. Make the simple undirected graph of these pairs. Write delta for its degeneracy: repeatedly remove a minimum-degree vertex and reverse the removal order, so every vertex has at most delta earlier neighbors. For odd prime q>=N and ANY consistent assignment to the specified entries of a normalized moment matrix, there is a completion of rank at most

    min(N+1, 1+2(delta+1)).

This includes false circuits whenever their normalized linear moment constraints are consistent. Write the first row as (1,x^T) and subtract (1,x)(1,x)^T. The remaining wire-by-wire partial symmetric matrix has prescribed diagonal entries and one prescribed value per graph edge. Set a=delta+1. Give wire i a public vector p_i=(1,i,...,i^(a-1)) over distinct field points. Construct y_i in order. For each earlier neighbor j prescribe p_j^T y_i as the required edge entry minus y_j^T p_i. Also impose p_i^T y_i equal to half the prescribed diagonal. These at most a equations have independent rows by Vandermonde, hence always admit a solution. Then P Y^T+Y P^T completes the residual with rank at most 2a. Restoring the subtracted rank-one matrix proves the bound. Repeated-input gates only constrain a diagonal and repeated edges reuse their agreed value. Normalized feasibility is ordinary field elimination and no satisfying assignment is used. Since a graph of degeneracy delta contains a subgraph with at least delta(delta+1)/2 edges, even if every gate uses a distinct pair the resulting bound is O(sqrt(G)+1).

**Limitation of deleting all unspecified coordinates.** The construction chooses one completion. It need not preserve the rank-one completion used by a valid witness, nor the linear coordinates used to combine ciphertext blocks. For example a free pair of independent Boolean inputs contributes the bilinear function xy. On all four assignments xy cannot be reconstructed as an affine-linear combination of 1,x,y (or their Boolean squares). Adjoin these unused inputs to any satisfiable fixed circuit and fix a satisfying trace of its other wires; mixed moments with fixed wires are only linear in x,y. Therefore dropping every unused pair and linearly rebuilding its witness moment cannot preserve the earlier rank test in general. Recognizing unused wires and removing them before compilation is valid but is a different operation. These arguments exclude the coarse rank/width estimate on the raw compiler and give an explicit cap on any minimum-affine-rank estimate from these sparse constraints. They do not show insecurity of an arbitrary computational construction. A different compiler or a fixed-game reduction that uses more than minimum normalized rank remains necessary.

**Checks.** The listing exercises 120 deterministic sparse graphs with arbitrary diagonals, edge values and first rows over F_101. It verifies all prescribed entries and the rank bound after completing the whole matrix.
~~~python
from itertools import combinations
from random import Random

q=101
def eliminate(rows,n):
    basis={}
    for original in rows:
        v=[x%q for x in original]
        for j in sorted(basis):
            c=v[j]
            v=[(x-c*y)%q for x,y in zip(v,basis[j])]
        j=next((i for i in range(n) if v[i]),None)
        if j is not None:
            basis[j]=[x*pow(v[j],-1,q)%q for x in v]
        elif len(v)>n:
            assert v[-1]==0
    return basis

def dot(a,b):
    return sum(x*y for x,y in zip(a,b))%q

rng=Random(2971)
for trial in range(120):
    n=2+trial%20
    x=[rng.randrange(q) for i in range(n)]
    diag=[rng.randrange(q) for i in range(n)]
    edges={(i,j):rng.randrange(q) for i,j in combinations(range(n),2)
           if rng.random()<(1+trial%8)/10}
    left=set(range(n))
    order=[]
    delta=0
    while left:
        degree,i=min((sum(tuple(sorted((i,j))) in edges for j in left),i) for i in left)
        delta=max(delta,degree)
        order.append(i)
        left.remove(i)
    a=delta+1
    P=[[pow(i,k,q) for k in range(a)] for i in range(n)]
    Y={}
    for i in reversed(order):
        rows=[P[i]+[(diag[i]-x[i]**2)*pow(2,-1,q)%q]]
        for j,y in Y.items():
            key=tuple(sorted((i,j)))
            if key in edges:
                rows.append(P[j]+[edges[key]-x[i]*x[j]-dot(y,P[i])])
        basis=eliminate(rows,a)
        coeff=[0]*a
        for j in sorted(basis,reverse=True):
            coeff[j]=(basis[j][-1]-dot(basis[j][:a],coeff))%q
        Y[i]=coeff
    M=[[1]+x]+[[x[i]]+[(x[i]*x[j]+dot(P[i],Y[j])+dot(Y[i],P[j]))%q
                          for j in range(n)] for i in range(n)]
    assert all(M[i+1][i+1]==diag[i] for i in range(n))
    assert all(M[i+1][j+1]==v for (i,j),v in edges.items())
    assert len(eliminate(M,n+1))<=1+2*a
print("120 partial matrix completions verified")
~~~
