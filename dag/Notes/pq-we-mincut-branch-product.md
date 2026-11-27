---
title: Optimizing the mixed separator branch product on 3-CNF partitions
refs: [definition:WE_CircuitSAT]
tags: [witness-encryption, compilation, cost]
---

For a fixed clause partition build a triple (A,x,B) whenever left clause
A and right clause B contain opposite literals on x. Covering all triples
with clauses and variables yields the construction described in the mixed
separator note: branch on one literal per selected clause or a bit per
selected variable. Minimize the *pre-pruning* product T of those factors.
This leaves leaf encryption and simplification costs to be evaluated.

**Network.** Pay log2(length) on source-to-left-clause and right-clause-to-sink
arcs. For each variable and left polarity create an input and output port.
Connect each corresponding left clause to the input and the output to every
opposite right clause by arcs of effectively infinite capacity. Split the
port with an arc of weight one. All triples of one polarity form a complete
bipartite graph between their two lists, so every surviving source-sink
path represents an actual conflict. If a variable supports both orientations
it is a single purchase for the mixed separator. Enumerate buy/forbid for
these b variables. Buying removes both ports and costs one; forbidding
makes both split arcs infinite. Take a minimum cut and add the bought
cost, then minimize across the 2^b cases. Reading the finite cut arcs
recovers an optimal cover: a cover disconnects all paths by cutting its
arcs, and disconnection covers every path. Infinite capacity can exceed
the sum of all clause and variable weights. Unit clauses cost zero.

**Polynomial fallback.** Keep both orientation arcs separately purchasable
at full unit price and solve one cut. Buy a cut variable just once in the
output. Any optimal original cover disconnects this network by paying for
at most two copies per selected variable and one per clause. Hence the
returned product is at most the square of the optimal product. If the
optimal mixed separator gives polynomially many branches, the one-cut
algorithm also gives polynomially many. This conclusion avoids using an
exponential optimizer in the encryption time bound.

**Exact integer capacities.** If at most m ternary clauses are present,
replace log2(3) by a fraction strictly between max_j floor(j log2 3)/j
and min_j (floor(j log2 3)+1)/j for 1<=j<=max(1,m), e.g. the mediant.
Each floor is the bit length of 3^j minus one. Both bounds straddle the
irrational log2(3). Comparison of any two costs a+b log2(3) with b in
[0,m] is preserved, since the only potential sign-change points have a
denominator at most m. Scale by the denominator to get integer capacities.
The argument applies separately to each network and to comparisons across
purchase cases.

**Check.** Exact enumeration of all clause subsets (then buying precisely
the necessary variables) matched the solver on 100 sampled 3-CNFs. On
24 small Tseitin encodings (six inputs, eight NAND gates, output unit),
a four-gate/four-gate split gave identical aggregate pre-pruning counts
of 616 for branching on all conflict variables and for the optimal mixed
separator. Splitting all negative gate clauses from all positive clauses
and the output unit gave 238592 versus 137069, with improvement on 19/24.
The first partition still wins in aggregate. These are branch counts, not
measured encryption costs or a guarantee on arbitrary circuits. The code
below reproduces the counts; it tests the exact solver. The polynomial
fallback bound above is an analytical result.

~~~python
from collections import defaultdict, deque
from fractions import Fraction
from itertools import combinations, product
from math import prod
from random import Random

def cut_value(arcs):
    graph = defaultdict(dict)
    for u, v, cap in arcs:
        graph[u][v] = graph[u].get(v, 0) + cap
        graph[v].setdefault(u, 0)
    value = 0
    while True:
        parent = {'s': None}
        todo = deque(['s'])
        while todo and 't' not in parent:
            u = todo.popleft()
            for v, cap in graph[u].items():
                if cap and v not in parent:
                    parent[v] = u
                    todo.append(v)
        if 't' not in parent:
            return value
        path = []
        v = 't'
        while parent[v] is not None:
            path.append((parent[v], v))
            v = parent[v]
        delta = min(graph[u][v] for u,v in path)
        value += delta
        for u,v in path:
            graph[u][v] -= delta
            graph[v][u] += delta

def solve(left, right, check=False):
    clauses = left + right
    triples = {(i,abs(l),len(left)+j,l>0) for i,c in enumerate(left)
               for l in c for j,e in enumerate(right) if -l in e}
    xs = {x for _,x,_,_ in triples}
    dual = sorted(x for x in xs if len({s for _,y,_,s in triples if y==x})==2)
    m = max(1,sum(len(c)==3 for c in clauses))
    floors = [(3**j).bit_length()-1 for j in range(1,m+1)]
    lo = max(Fraction(a,j) for j,a in enumerate(floors,1))
    hi = min(Fraction(a+1,j) for j,a in enumerate(floors,1))
    two,three = lo.denominator+hi.denominator, lo.numerator+hi.numerator
    costs = [0,two,three]
    inf = 1 + two*len(xs) + sum(costs[len(c)-1] for c in clauses)
    best = inf
    for bits in product(range(2), repeat=len(dual)):
        bought = {x for x,b in zip(dual,bits) if b}
        arcs = [('s',i,costs[len(c)-1]) for i,c in enumerate(left)]
        arcs += [(len(left)+j,'t',costs[len(c)-1]) for j,c in enumerate(right)]
        live = [(i,x,j,s) for i,x,j,s in triples if x not in bought]
        arcs += list({(i,(x,s,0),inf) for i,x,j,s in live})
        arcs += list({((x,s,1),j,inf) for i,x,j,s in live})
        arcs += [((x,s,0),(x,s,1),inf if x in dual else two)
                 for x,s in {(x,s) for _,x,_,s in live}]
        best = min(best,two*len(bought)+cut_value(arcs))
    # Distinct attainable products have distinct encoded costs.
    val = next(2**a*3**b for a in range(len(xs)+len(clauses)+1)
               for b in range(m+1) if two*a+three*b==best)
    if check:
        brute=2**len(xs)
        for bits in product(range(2),repeat=len(clauses)):
            needed={x for i,x,j,s in triples if not bits[i] and not bits[j]}
            brute=min(brute,2**len(needed)*prod(len(c) for b,c in zip(bits,clauses) if b))
        assert val==brute
    return 2**len(xs),val,len(dual)

rng=Random(109)
for _ in range(100):
    cs=[tuple(x*rng.choice((-1,1)) for x in rng.sample(range(1,6),rng.randint(1,3)))
        for _ in range(8)]
    solve(cs[:4],cs[4:],True)
samples=[]
polarity=[]
for _ in range(24):
    groups=[]
    for z in range(7,15):
        a,b=rng.sample(range(1,z),2)
        groups.append([(a,z),(b,z),(-a,-b,-z)])
    samples.append(solve(sum(groups[:4],[]),sum(groups[4:],[])+[(14,)]))
    polarity.append(solve([g[2] for g in groups],sum((g[:2] for g in groups),[])+[(14,)]))
print(sum(x for x,y,d in samples),sum(y for x,y,d in samples),
      sum(x>y for x,y,d in samples),max(d for x,y,d in samples))
print(sum(x for x,y,d in polarity),sum(y for x,y,d in polarity),
      sum(x>y for x,y,d in polarity),max(d for x,y,d in polarity))
~~~
