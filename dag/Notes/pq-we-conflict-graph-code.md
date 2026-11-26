---
title: Polynomial witness conversion for conflict-guarded monotone CircuitSAT
refs: [definition:WE_CircuitSAT]
tags: [witness-encryption, circuit-sat]
---

Consider a public circuit presented as a monotone predicate P on n input bits conjoined with a guard that forbids selecting both endpoints of any edge of a public simple graph G. Monotonicity under inclusion among independent sets suffices. For a compiler the public decomposition must be certified or recognized from syntax. On an arbitrary NAND list one can always retain the original verifier. The following gives a short witness for the split-witness ABE construction of PR #64. Both conversion of a given witness and verification run in polynomial time.

Extend the independent support of the given witness greedily in vertex order to a maximal independent set I. This preserves acceptance. On remaining vertex set R select a minimum-degree vertex v of the induced graph (ties by vertex index). Its closed neighborhood has k vertices. Maximality implies that at least one of them belongs to I. Choose the first such u in increasing order, record its index j starting at zero and delete the closed neighborhood of u. This deletes at least k vertices by the minimum-degree choice. The residual I remains maximal: every remaining vertex outside I had a neighbor in I, and its neighbor cannot have been u. No other member of I was deleted.

Use the capacity U(0)=1, U(m)=max over 1≤k≤m of k U(m-k). It is monotone by the term k=1. At each node with m vertices, allocate a block of size U(m-k) to every branch. Prepend index j by adding j U(m-k) to the recursive child code. The child code fits because at most m-k vertices remain, and the entire node fits in U(m). The decoder divides by the same block to recover the branch and remainder, checks all local ranges and checks for zero remainder at the leaf. Finally evaluate P on the recovered set. Each successful path yields a maximal independent set: chosen vertices are independent and their closed neighborhoods cover the graph. Induction on the remaining size shows that encoding any independent input and then decoding recovers precisely its greedy extension. Multiple paths to the same maximal set cause no problem. Neither direction needs to count sets in the particular graph. The public capacity table takes O(n²) multiplications by small integers and comparisons on O(n)-bit values, and graph operations and division at each of at most n levels also cost polynomially many bit operations.

The branching argument follows [Wood's proof of the Miller–Muller and Moon–Moser bound](https://arxiv.org/abs/1104.1243). Here the padded blocks additionally give an efficiently computable witness map. The recurrence maximizes a product over integer partitions. Splitting a part t≥5 into 3 and t-3 improves the product, three twos can be replaced by two threes, and a part of one is unnecessary for m≥2. Thus U(128)=2·3^42=218837978263024718418. Forty-two disjoint triangles and one edge attain the bound on the number of distinct maximal independent sets. It takes 68 bits to represent all codes. This is a capacity bound for decoding such sets, not a lower bound for every encryption strategy.

At n=128 a balanced split gives 2^34 functional keys and 2^34 encrypted attributes, versus 2^64 of each for a raw 128-bit split. These are counts, not bytes or execution times. The new verifier pays for decoding, which can materially increase ABE depth and cost. POLY-time decoding alone does not establish concrete feasibility, an instantiated post-quantum ABE security reduction, or the clocked WE submission. Direct evaluation of P on all codes provides an assumption-free alternative with at most U(128) candidates. General graph guards with a nonmonotone body require another argument.

For a matching of 64 disjoint edges, extension selects exactly one endpoint per edge. Encoding those choices directly gives 64 bits and 2^32 items per table. This includes the dual-rail representation of 3SAT: use two rails for each source variable, forbid selecting both, and form a monotone conjunction of disjunctions of the rails corresponding to each clause. A satisfying partial selection extends to a total satisfying assignment and conversely. The growing family can therefore encode NP-complete instances. When the 64-variable source CNF is already given its ordinary assignment already uses 64 bits. The gain here is against the raw rail encoding.

## Reproducible checks

The reference implementation exhausts simple labelled graphs on zero through five vertices, every independent input and every code below capacity. It also checks 200 witness round trips on the 128-vertex extremal graph. It uses Python 3 with integer bit sets.

~~~python
from itertools import combinations
from random import Random

def capacity(n):
    u=[1]
    for i in range(1,n+1):u.append(max(k*u[i-k] for k in range(1,i+1)))
    return u

def indices(mask):
    while mask:
        bit=mask & -mask
        yield bit.bit_length()-1
        mask^=bit

def branch(adj,active,U):
    v=min(indices(active),key=lambda j:((adj[j]&active).bit_count(),j))
    choices=list(indices(((1<<v)|adj[v])&active))
    block=U[active.bit_count()-len(choices)]
    return choices,block

def maximal(adj,x):
    for i,neighbors in enumerate(adj):
        if not neighbors&x:x|=1<<i
    return x

def encode(adj,x,U):
    I=maximal(adj,x);active=(1<<len(adj))-1;code=0
    while active:
        choices,block=branch(adj,active,U)
        j=next(j for j,u in enumerate(choices) if I>>u&1)
        u=choices[j]
        code+=j*block
        active &= ~((1<<u)|adj[u])
    return code

def decode(adj,code,U):
    active=(1<<len(adj))-1;I=0
    while active:
        if code>=U[active.bit_count()]:return None
        choices,block=branch(adj,active,U)
        j,code=divmod(code,block)
        if j>=len(choices):return None
        u=choices[j];I|=1<<u
        active &= ~((1<<u)|adj[u])
    return I if code==0 else None

def independent(adj,x):
    return all(not (adj[i]&x) for i in indices(x))

def graph(n,edges):
    adj=[0]*n
    for i,j in edges:
        adj[i]|=1<<j;adj[j]|=1<<i
    return adj

checked=0
for n in range(6):
    U=capacity(n);edges=list(combinations(range(n),2))
    for mask in range(1<<len(edges)):
        adj=graph(n,[e for i,e in enumerate(edges) if mask>>i&1])
        actual={decode(adj,c,U) for c in range(U[n])}-{None}
        expected=set()
        for x in range(1<<n):
            if not independent(adj,x):continue
            I=maximal(adj,x);expected.add(I)
            c=encode(adj,x,U)
            assert c<U[n] and decode(adj,c,U)==I and x&I==x
        assert expected==actual
        checked+=1
U=capacity(128)
print(checked,'graphs including the empty graph;',U[-1],(U[-1]-1).bit_length(),'bits')
edges=[e for start in range(0,126,3) for e in combinations(range(start,start+3),2)]+[(126,127)]
adj=graph(128,edges);r=Random(7401)
for _ in range(200):
    x=0
    for j in r.sample(range(128),128):
        if not adj[j]&x and r.randrange(2):x|=1<<j
    code=encode(adj,x,U)
    assert decode(adj,code,U)==maximal(adj,x)
print('200 full-size round trips passed')
~~~
