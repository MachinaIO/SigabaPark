---
title: Anchored gate partitions with a certified leaf enumeration cost
refs: [definition:WE_CircuitSAT]
tags: [witness-encryption, compilation, cost]
---

Keep each NAND gate's Tseitin clauses together and pin the output unit to
its gate. Treat every variable occurring in some gate as a hyperedge on
all its incident gates. The NAND encoding uses both polarities of each
operand and output. Hence a variable occurring on both sides requires
a branch in the all-crossing-variable compiler. Let c count such variables
and l,r the variables purely on the left and right. Fixing the c bits gives
two disjoint residual witness domains. Measure 2^c branches and the
pre-simplification assignment enumeration proxy W=2^c(2^l+2^r).
A pair of local leaves is required per branch in the XOR-share construction.
The proxy counts exhaustive assignments across the two leaves, not actual
encryption work. In particular, gate evaluation and simplification may
shrink these domains, and ABE item sizes can differ. Pin nonempty groups
of gates to both sides to specify the allowed class of partitions.

**Cut oracle.** Write u=c+l and v=c+r. Minimize a u+b v+d c for nonnegative
integer weights. Represent each variable by ports I,O, add infinite arcs
from every incident gate to I and from O to every incident gate. Add arcs
I->sink of cost a, source->O of cost b, and I->O of cost d. Put left gates
on the source side. A left incidence forces I left, a right incidence
forces O right, and otherwise placing both ports with their incident gates
is optimal. The costs are exactly the requested touches and split cost.
Pin gates with infinite arcs, taking infinity above the total finite
capacity. The graph is linear in the number of incidences. One cut obtains
the minimum c; several weight choices provide candidate partitions which
the sender can score by W or by a different public estimator.

**Exact optional search.** Maintain an incumbent W and partial terminal
assignments. Compute minima m_ab of a u+b v at this node for several
weights by the oracle. Every completion has integer u,v in [0,n] where
n is the number of variables, and satisfies a u+b v >= m_ab for every
computed pair. Enumerate these two integers; if no admissible pair has
2^u+2^v below the incumbent, prune. Otherwise branch on the side of one
unpinned gate. Scoring the feasible partitions returned by each cut can
improve the incumbent. Exhausting the tree gives a certificate of exact
optimality within the pinned partition family and stated cost model.
The worst-case search is exponential; the fixed list of candidate cuts
is a polynomial-time option without an optimality claim for W.

**Comparison.** On the preceding note's 24 sampled six-input/eight-gate
NAND circuits, pin gates 1,2 left and 7,8 right, with generation order
numbered from 1. Aggregate branches fall from 616 (four-gate prefix)
to 182 (minimum c). Yet aggregate W rises from 24448 to 37632 for the
particular minimum cuts returned here. Scoring the prefix and six cut
candidates by W gives 17728. The exact search gives 15232 and visits
130 partial partitions over all instances (at most 744 in the full binary
trees). Exhaustively checking the 16 permitted partitions per circuit
confirms both the minimum split count and optimal W on every instance.
These small examples demonstrate the tradeoff and are not an asymptotic
security or timing result. The compiler still needs efficient secure local
encryptions for any instance on which enumeration remains large.

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

def run(groups):
    n=len(groups); vertices=set(range(n))
    pins={x:{i for i,g in enumerate(groups) if x in g} for x in set.union(*groups)}
    def profile(S):
        l=sum(bool(S & g) for g in pins.values())
        r=sum(bool((vertices-S) & g) for g in pins.values())
        c=l+r-len(pins)
        return c,l-c,r-c
    def work(p):
        c,l,r=p
        return 2**c*(2**l+2**r)
    def plan(a,b,d,A=(0,1),B=(6,7)):
        inf=1+len(pins)*(a+b+d)
        arcs=[('s',i,inf) for i in A]+[(i,'t',inf) for i in B]
        for x,g in pins.items():
            u,v=('u',x),('v',x)
            arcs.extend((i,u,inf) for i in sorted(g))
            arcs.extend((v,i,inf) for i in sorted(g))
            arcs.extend([(u,v,d),(u,'t',a),('s',v,b)])
        val,S=cut_value(arcs)
        c,l,r=profile(S & vertices)
        assert val==a*(l+c)+b*(r+c)+d*c
        return c,l,r
    base=profile(set(range(4)))
    options=[plan(a,b,d) for a,b,d in ((0,0,1),(1,1,0),(2,1,1),(1,2,1),(3,2,0),(2,3,0))]
    opt=min(options+[base],key=work)
    exact=[profile({0,1}|set(z)) for k in range(5) for z in combinations(range(2,6),k)]
    assert options[0][0]==min(c for c,l,r in exact)
    best=work(opt)
    visited=0
    def search(A,B,free):
        nonlocal visited,best
        visited+=1
        bounds=[]
        for a,b in ((1,0),(0,1),(1,1),(2,1),(1,2)):
            p=plan(a,b,0,A,B)
            c,l,r=p
            bounds.append((a,b,a*(l+c)+b*(r+c)))
            best=min(best,work(p))
        # If no pair of touched widths improves the incumbent, prune.
        if not free or not any(2**u+2**v<best and
                all(a*u+b*v>=w for a,b,w in bounds)
                for u in range(len(pins)+1) for v in range(len(pins)+1)):
            return
        x,*tail=free
        search(A+[x],B,tail)
        search(A,B+[x],tail)
    search([0,1],[6,7],[2,3,4,5])
    assert best==min(map(work,exact))
    return [2**base[0],2**options[0][0],work(base),work(options[0]),work(opt),min(map(work,exact)),visited]
rng=Random(109)
# Match the input stream used in the preceding mixed-separator check.
for _ in range(800):
    vs=rng.sample(range(1,6),rng.randint(1,3))
    for x in vs:rng.choice((-1,1))
rows=[run([set([z]+rng.sample(range(1,z),2)) for z in range(7,15)]) for _ in range(24)]
print([sum(c) for c in zip(*rows)])
~~~
