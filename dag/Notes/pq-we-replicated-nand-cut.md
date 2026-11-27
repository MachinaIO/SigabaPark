---
title: Computing on both sides of a WE cut to replace boundary guesses
refs: [definition:WE_CircuitSAT]
tags: [witness-encryption, compilation, cost]
---

Give every NAND gate a fixed native side. Each gate may additionally run on
the opposite side. A leaf computes every scheduled gate in original order.
Guess one bit for each primary input now read on both sides and each gate
output imported by a side that does not compute it. Check the latter guess
at its producer. A gate computed twice requires no guessed output: by
induction both copies equal its global value on accepting local witnesses.
This induction uses the equality checks on all imported wires and the
single guesses for shared primary inputs. Conversely a genuine witness
determines all branch bits by one evaluation. The two local checks and
per-branch independent XOR shares have the same NO-instance hybrid as
without replication. Charge the added gate evaluations to the leaf costs.

Let c be the new guess count, l,r the private primary input counts.
For a fixed native partition, nonnegative integer weights a,b,d, the best
duplication set for a(c+l)+b(c+r)+dc is found by one directed minimum cut.
Place a decision vertex for each gate z on the source side if duplicated.
Introduce the following arcs, with infinity larger than the total finite
cost. Constants are charged outside the cut.

* For each produced wire z, make a need vertex H. If any consumer is
  native to the opposite side force H to the source side. For each
  same-native-side consumer y add an infinite y->H arc. Add H->z of
  weight a+b+d. Exactly when there is remote demand and z is not
  duplicated, the cheapest placement incurs this charge.
* A primary input with native consumers on both sides always costs a+b+d.
  With consumers on only the left, pay a unconditionally, add arcs from
  its consumer decision vertices to a need vertex with infinite capacity,
  then a need-to-sink arc of weight b+d. This charges the extra right-side
  touch and the boundary penalty only if some consumer is duplicated.
  Interchange a,b for exclusively right-native inputs. Omit unused inputs.

Thus restricted witness enumeration may trade a feed of many values for
recomputation from comparatively few inputs. For example let k shared-source
primary bits feed all m=k(k-1)/2 pairwise NAND gates native to the left,
with each output consumed on both sides and these k inputs initially used
only on the left. If these are the only boundary wires, duplicating the m
producers changes the branch count from 2^m to 2^k. Each duplicated gate
costs a local NAND, and the left leaf loses those k private witness bits.
This compares two schedules for the same partition; additional algebraic
compression or a different partition could improve either choice.

**Validation and limits.** On the preceding 24 seeded circuits, enumerate
the same 16 pinned native partitions. For each, verify five weighted cuts
against all 256 duplication sets. For the balanced KP-ABE item count
2^c (B(l)+B(r)), B(n)=2^floor(n/2)+2^ceil(n/2), score these five cuts
and the empty duplication set. The aggregate best count drops from 1390
without duplication to 994. Exhaustive duplication search gives the same
aggregate. The weighted cuts need not attain the exact item optimum on
other circuits. Direct encryption still costs only 296 items in aggregate.
Counts omit setup, key and ciphertext byte sizes and per-gate work.
The experiment uses exhaustive native partitions for this small control;
the polynomial algorithm is for a *given* native partition. There is no
general NP size bound or new assumption in this scheduling result.

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
def run(g,L):
    G=set(g); R=G-L
    inp={x for ab in g.values() for x in ab}-G
    users={x:{z for z,ab in g.items() if x in ab} for x in G|inp}
    def metrics(D):
        sites=[L|(D&R),R|(D&L)]
        P=[{x for x in inp if users[x]&S} for S in sites]
        c=len(P[0]&P[1])+sum(any(z not in S and users[z]&S for S in sites) for z in G)
        return c,len(P[0]-P[1]),len(P[1]-P[0])
    def bestcut(a,b,d):
        big=1+(a+b+d)*(len(G)+len(inp))*3
        arcs=[]
        for z in G:
            own,other=(L,R) if z in L else (R,L)
            h=('need',z)
            if users[z]&other:arcs.append(('s',h,big))
            arcs.extend((u,h,big) for u in users[z]&own)
            arcs.append((h,z,a+b+d))
        constant=0
        for x in inp:
            A,B=users[x]&L,users[x]&R
            if A and B:
                constant+=a+b+d
                continue
            constant+=a if A else b
            h=('input',x)
            arcs.extend((z,h,big) for z in A|B)
            arcs.append((h,'t',(b if A else a)+d))
        val,S=cut_value(arcs)
        c,l,r=metrics(G&S)
        assert val+constant==a*(c+l)+b*(c+r)+d*c
        return G&S
    def work(row):
        c,l,r=row
        return 2**c*(bag(l)+bag(r))
    profiles=[metrics({z for i,z in enumerate(sorted(G)) if m>>i&1}) for m in range(2**len(G))]
    options=[work(metrics(set()))]
    for a,b,d in ((0,0,1),(1,1,0),(1,2,0),(2,1,0),(1,1,2)):
        row=metrics(bestcut(a,b,d))
        f=lambda p:a*(p[0]+p[1])+b*(p[0]+p[2])+d*p[0]
        assert f(row)==min(map(f,profiles))
        options.append(work(row))
    return options[0],min(options),min(map(work,profiles))
rng=Random(109)
for _ in range(800):
    vs=rng.sample(range(1,6),rng.randint(1,3))
    for x in vs:rng.choice((-1,1))
sums=[0,0,0,0]
for case in range(24):
    g={z:rng.sample(range(1,z),2) for z in range(7,15)}
    rows=[run(g,{7,8}|set(z)) for j in range(5) for z in combinations(range(9,13),j)]
    for i in range(3):sums[i]+=min(r[i] for r in rows)
    sums[3]+=bag(len({x for ab in g.values() for x in ab if x<7}))
print(sums)
~~~
