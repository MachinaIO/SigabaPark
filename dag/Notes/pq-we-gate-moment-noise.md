---
title: Exact three-value witness noise from NAND constraints and the dimension required for hiding
refs: [note:pq-we-witness-finite-support-decoder, note:pq-we-rank-gap-lattice-barriers]
tags: [witness-encryption, compilation, correctness, rank, complexity]
---

**Compiler and YES experiment.** Index the N Boolean circuit wires by 1,...,N and add wire 0 with value 1. Over a prime field of odd order q>3, put d=N+1 and k=d(d+1)/2. The witness vector a has entries a_ij=x_i x_j for i<=j. Define E_ij to be the matrix unit for i=j and the sum of the two transposed units for i<j. Thus sum a_ij E_ij=xx^T over the field. Construct a public matrix Q of homogeneous linear tests on moments: a_ii-a_0i=0 for Boolean wires, a_0z+a_uv-a_00=0 for each NAND(u,v)=z (canonicalize the pair u,v), and a_0out-a_00=0. Every satisfying assignment with a_00=1 passes. Conversely a symmetric rank-one moment matrix normalized by a_00=1 equals xx^T by its first column, and these tests then force a Boolean satisfying trace. Repeated gate inputs and an output equal to an input are covered.

Draw uniform t-by-d S and one field vector r independently. Define the t-by-k array Y with columns S E_ij r. Add B Q for independent uniform B of the appropriate shape and add f to just column 00, where each entry of f lies in {-1,0,1}. Compare this mode with independent uniform Y at the same S. On a satisfying trace,

    Ya = (S x)(x^T r) + f.

The gate masks cancel simultaneously for all valid traces without enumerating them. This gives a concrete polynomial compiler achieving the three-value witness-support property with b=1. For an especially simple decoder, one row with nonzero (Sx)_j yields at most three candidate values of c=x^T r. Test those candidates on all rows. If Sx vanishes everywhere, just test every y_j for membership in the support. Real-mode acceptance is certain. In uniform mode the chance of acceptance is at most q(3/q)^t by a union bound over c, conditional on any S. The decoder never lists the field or uses a hardness assumption. Compilation, ciphertext size t(d+k) field elements and both honest running times are polynomial for polynomial t,d,log q.

**What the gate masks leave visible.** Let g=rank(Q). Conditional on S the base array is a *linear* function of a single d-dimensional vector r. Per row the gate masks span g dimensions and the 00 direction contributes at most one more even if f is allowed to range over the whole field. Thus the real support lies in a publicly specified linear space of dimension at most d+t(g+1) in tk coordinates. When the deficit D=t(k-g-1)-d is positive, a uniform array belongs to this space with probability at most q^-D. Membership is polynomial-time linear algebra. This difference holds on false statements too. In particular linear gate masks alone with an independent uniform comparison mode do not give computational hiding. If the circuit has G NAND gates then g<=N+G+1, whereas k grows quadratically in N. The condition on D is sufficient; overlapping directions can make the actual support smaller. For any additional linear masks with arbitrary coefficients, their total conditional image dimension must be at least D just to eliminate this particular dimension deficit. Adding more random scalars in the same gate-equation span has no effect. Changing the comparison law to a fresh draw of r,B,f with these same constraints preserves the YES identity and therefore also preserves the zero decoder's acceptance. Obtaining a different comparison law with both properties is an open design issue.

**Controls.** The listing enumerates all normalized symmetric moments for a one-gate circuit over F_5. The YES gate has a repeated input. A three-gate identically false circuit checks the gate equations and the deficit using the actual gate-row rank.
~~~python
from itertools import combinations_with_replacement, product

def rank(rows,q):
    pivots={}
    for row in rows:
        v=[x%q for x in row]
        for i in sorted(pivots):
            c=v[i]
            v=[(a-c*b)%q for a,b in zip(v,pivots[i])]
        if any(v):
            i=next(i for i,a in enumerate(v) if a)
            pivots[i]=[a*pow(v[i],-1,q)%q for a in v]
    return len(pivots)

def compile_rows(n,gates,out):
    pairs=list(combinations_with_replacement(range(n+1),2))
    tests=[[(i,i,1),(0,i,-1)] for i in range(1,n+1)]
    for u,v,z in gates:
        tests.append([(0,z,1),(min(u,v),max(u,v),1),(0,0,-1)])
    tests.append([(0,out,1),(0,0,-1)])
    rows=[]
    for terms in tests:
        row=[0]*len(pairs)
        for i,j,c in terms:
            row[pairs.index((i,j))]+=c
        rows.append(row)
    return pairs,rows

q=5
pairs,rows=compile_rows(2,[(1,1,2)],2)
solutions=[]
for tail in product(range(q),repeat=len(pairs)-1):
    a=(1,)+tail
    x=(1,a[1],a[2])
    if all(a[h]==x[i]*x[j]%q for h,(i,j) in enumerate(pairs)) and all(
            sum(u*v for u,v in zip(row,a))%q==0 for row in rows):
        solutions.append(x)
assert solutions==[(1,0,1)]
# NAND(x,NOT x) is identically true. Its negation is identically false.
pairs,rows=compile_rows(4,[(1,1,2),(1,2,3),(3,3,4)],4)
for bit in (0,1):
    x=(1,bit,1-bit,1,0)
    a=[x[i]*x[j] for i,j in pairs]
    assert [sum(u*v for u,v in zip(row,a))%q for row in rows]==[0]*(len(rows)-1)+[4]
g=rank(rows,q)
t=4
print("normalized moments checked",q**5,"false example",len(pairs),g,t*(len(pairs)-g-1)-5)
~~~
