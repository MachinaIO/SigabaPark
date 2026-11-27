---
title: Choosing both the partition and duplicated gates in one directed cut
refs: [definition:WE_CircuitSAT]
tags: [witness-encryption, compilation, cost]
---

Let each gate run on L, R, or both. Some gates may be required on one
side, still permitting duplication. Require the output gate on the side
checking acceptance. The evaluated-leaf compiler guesses primary bits
used by both sides and outputs needed on a side missing the producer.
Write c for this total, l,r for private primary counts, and k for the
number of duplicated gates. One directed cut minimizes

    a(c+l) + b(c+r) + d c + e k

over *all* legal schedules, for any nonnegative integer weights. This
removes the outer search over native partitions of the previous compiler.
Gate-specific duplication penalties also work. Keep the same per-branch
local verification and XOR-share compilation. A duplicate computes the
same value by topological induction on accepting local witnesses.

**Network.** A vertex is true on the source side. Use vertices L_z for
executing z on the left and N_z for omitting it on the right. The hard
implication N_z -> L_z excludes omission on both. The reverse arc L_z ->
N_z of cost e charges duplication exactly. Pins force L_z true or N_z
false. For each wire x introduce A_x and B_x for required on the left
and *not* required on the right. For every consuming gate z enforce
L_z -> A_x and B_x -> N_z. The cheapest choices may always take A_x true
only on left demand and B_x false only on right demand: switching either
to this extremal value when feasible cannot increase any finite cost below.

* For a primary input use arcs A_x -> sink (a), source -> B_x (b) and
  A_x -> B_x (d). They count side touches and shared inputs.
* For a produced wire x use A_x -> L_x and N_x -> B_x each with cost
  a+b+d. They charge a guessed gate value exactly once when demanded on
  a missing side; the two cases cannot coincide.

Every schedule extends to a cut of exactly its cost and every finite cut
can be normalized as above. Use a hard capacity exceeding the sum of all
finite capacities. Network size is linear in gates plus incidences. The
compiler can score several resulting schedules by the balanced two-split
ABE item formula or by its chosen leaf cost model. A linear objective
need not attain the minimum of the nonlinear item count.

**Check.** For the preceding 24 seeded eight-gate circuits require gates
1,2 on the left and 7,8 on the right (generation order). Every instance
has 2^4 times 3^4 = 1296 legal schedules. All six weighted optimum values
matched exhaustive search on all 24. Selecting the lowest item count
among the six returned schedules totals 1002, versus 994 for exhaustive
scheduling; they match on 23 circuits. The previous enumeration of 16
native partitions and five cuts per partition reached 994 in this sample.
Direct ABE enumeration still totals 296. These are item counts and numbers
of optimizer calls; byte sizes, run times and a polynomial general NP
encryption bound do not follow. Local security premises are unchanged.

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
            return value, set(parent)
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

def bag(z):return 2**(z//2)+2**((z+1)//2)
def run(g):
    G=set(g); P={x for ab in g.values() for x in ab}-G
    def profile(L,R):
        rows=[{x for z in S for x in g[z]} for S in (L,R)]
        a,b=rows
        c=len(P&a&b)+len((a&G)-L)+len((b&G)-R)
        return c,len((a-b)&P),len((b-a)&P),len(L&R)
    def best(w):
        a,b,d,e=w
        arcs=[]
        inf=1+(len(G)+len(P))*(3*(a+b+d)+e+1)
        for z in G:
            l,r=('l',z),('r',z)
            arcs.extend([(r,l,inf),(l,r,e)])
            if z in (7,8):arcs.append(('s',l,inf))
            if z in (13,14):arcs.append((r,'t',inf))
            for x in g[z]:
                arcs.extend([(l,('A',x),inf),(('B',x),r,inf)])
        for x in G|P:
            A,B=('A',x),('B',x)
            if x in P:arcs.extend([(A,'t',a),('s',B,b),(A,B,d)])
            else:arcs.extend([(A,('l',x),a+b+d),(('r',x),B,a+b+d)])
        cost,S=cut_value(arcs)
        row=profile({z for z in G if ('l',z) in S},
                    {z for z in G if ('r',z) not in S})
        return cost,row
    exact=[]
    for states in product(*[(1,3) if z in (7,8) else (2,3) if z in (13,14)
                            else (1,2,3) for z in sorted(G)]):
        L={z for z,k in zip(sorted(G),states) if k&1}
        R={z for z,k in zip(sorted(G),states) if k&2}
        exact.append(profile(L,R))
    def items(row):
        c,l,r,e=row
        return 2**c*(bag(l)+bag(r))
    scores=[]
    for w in ((0,0,1,0),(1,1,0,0),(1,2,0,0),(2,1,0,0),(1,1,2,0),(1,1,0,1)):
        a,b,d,e=w
        f=lambda p:a*(p[0]+p[1])+b*(p[0]+p[2])+d*p[0]+e*p[3]
        val,p=best(w)
        assert f(p)==val==min(map(f,exact))
        scores.append(items(p))
    return min(scores),min(map(items,exact))
rng=Random(109)
for _ in range(800):
    vs=rng.sample(range(1,6),rng.randint(1,3))
    for x in vs:rng.choice((-1,1))
rows=[run({z:rng.sample(range(1,z),2) for z in range(7,15)}) for _ in range(24)]
print(sum(a for a,b in rows),sum(b for a,b in rows),sum(a==b for a,b in rows))
~~~
