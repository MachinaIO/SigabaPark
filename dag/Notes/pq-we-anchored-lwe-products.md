---
title: Embedding standard LWE errors inside rank-correctable moment products
refs: [note:pq-we-rank-coded-shifts, note:pq-we-shared-column-criterion]
tags: [witness-encryption, reduction, correctness, complexity]
---

**Modified factors.** Keep the square b-by-b rank-code ciphertext C_i=L K_i R^T+gamma_i Z_m, with b>=3. Reserve n+b left and right coordinates in a public layout for the entire size class. On the left take L=[A | I_b | L_rest] with A uniform b-by-n and L_rest uniform independently. In each independent row of R take a uniform n-dimensional secret z, b iid errors e with law chi, and a fresh independently sampled remainder w. The same row contributes to every observed block. These factor laws apply on YES and NO alike. For any valid circuit witness whose normalized moment is x y^T, the combined deviation is still exactly (Lx)(Ry)^T. In particular the Gabidulin radius-one decoder is perfectly correct regardless of the sizes of the errors or the nonuniformity of L. Adding iid LWE errors *after* forming every public block would not give this rank guarantee.

**Restricted NO condition.** Let P be the coordinate inclusion of the first n+b left slots. On the first n+b right slots require K_i[:,0:n+b]=gamma_i P for every i. All other columns of every K_i are arbitrary, including rows that multiply the challenge design A. For any fixed L, the joint block-column j then has entries

    C_i[:,j] = gamma_i (A z_j + e_j + Z_m[:,j]) + L K_i[:,rest] w_j.

This is the full law, including auxiliaries with gamma_i=0 and all their correlations. The single-secret decisional LWE challenger takes only q,n,b and chi, samples A uniformly, and returns A and either A z+e or a uniform b-vector. Its hidden-bit score is efficiently decidable. It receives no statement and no witness. To switch one column in the whole transcript, embed its response, simulate all earlier common pads uniformly and all later common pads with fresh known z,e using the same A. Draw all remainders and form the displayed residual terms. After b switches all common pads are independent uniform conditional on A and hide every message translation exactly. For two fixed messages the advantage is at most 2b times the quantum single-secret advantage with the complete simulation time charged. No statistical extraction, obfuscation, evaluation oracle or extra instance-dependent hardness game occurs. With uniform z and b<=n a high-probability full-row-rank A alone can explain hiding; the reduction does not ascribe that case to computational hardness. In other regimes the actual LWE hardness at the prescribed dimensions, noise and sample count remains a premise.

**Boundary for circuit compilation.** Whenever gamma·c=1 the normalized combination on the reserved columns equals P and hence has rank at least n+b. A rank-one YES solution is impossible there. The displayed NO condition in a prescribed layout is decidable by checking matrix entries. A uniform compiler satisfying this condition for every false CircuitSAT instance, while preserving every YES witness, would decide CircuitSAT in polynomial time. Allowing polynomial-size, efficiently checked layout certificates as nonuniform reduction advice at best changes that consequence to UNSAT in NP, assuming the certificates retain the rank argument. The preceding rectangular compiler supplies the rank-one YES property; it gives no such NO layouts in general. The contribution is a way to insert *both* the design and the error of a fixed LWE game inside the bilinear factors, and an exact limited-case security proof. Extending it to local rather than globally certifying embeddings would require a new hybrid argument.

**Small distribution check.** In F_3 take b=2,n=1 for a column-law check only (the rank code needs b>=3), a fair binary error per row, and a binary remainder. Three output blocks have gamma=(1,2,0) with different residuals including the shared design. Compare matrix multiplication directly with the challenge simulator, and check translation invariance in the uniform-pad hybrid for every A and every shift. Independent columns conditional on A give the multicolumn law.
~~~python
from collections import Counter
from itertools import product

def multiply(M,x):
    return tuple(sum(a*b for a,b in zip(row,x))%3 for row in M)

gamma=(1,2,0)
def matrices():
    result=[]
    for g,extra in zip(gamma,((1,0,1),(2,1,0),(1,1,0))):
        result.append([[g*int(i==j) for j in range(3)]+[extra[i]] for i in range(3)])
    return result

mats=matrices()
vectors=list(product(range(3),repeat=2))
count=0
for A in vectors:
    L=[[A[0],1,0],[A[1],0,1]]
    def simulate(pad,w,shift):
        blocks=[]
        for g,M in zip(gamma,mats):
            residual=multiply(L,[row[-1]*w for row in M])
            blocks.append(tuple((g*(v+s)+r)%3 for v,s,r in zip(pad,shift,residual)))
        return tuple(blocks)
    uniform=Counter(simulate(u,w,(0,0)) for u in vectors for w in range(2))
    for shift in vectors:
        actual=Counter()
        simulated=Counter()
        for z,e,w in product(range(3),product(range(2),repeat=2),range(2)):
            blocks=[multiply(L,multiply(M,(z,*e,w))) for M in mats]
            actual[tuple(tuple((v+g*s)%3 for v,s in zip(col,shift))
                         for col,g in zip(blocks,gamma))]+=1
            pad=tuple((a*z+x)%3 for a,x in zip(A,e))
            simulated[simulate(pad,w,shift)]+=1
            count+=1
        assert actual==simulated
        assert uniform==Counter(simulate(u,w,shift) for u in vectors for w in range(2))
print(count,"real samples; 81 conditional translation checks")
~~~
