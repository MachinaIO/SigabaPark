---
title: Replay fixed-code leakage, weighted fault assignments and routing
refs: [note:fixed-target-ball-transport, definition:FixedTargetGeometry]
tags: [witness-encryption, reproducibility]
---

Run each Python program independently. The first enumerates exact rational distributions including the header. The second routes all eight-port permutations and checks full-size nearest-codeword witnesses.

### Block tests

```python
"""Exact conditional parity-law and nearest certificate checks."""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import product
from math import comb,prod
from random import Random
rng=Random(225)
def exact(n,gs,t,ps):
    v=defaultdict(Q)
    for r in range(1<<n):
        y=tuple((g&r).bit_count()%2 for g in gs)
        p=prod(ps[i] if r>>i&1 else 1-ps[i] for i in range(n))
        v[y]+=(-1)**((r&t).bit_count())*p
    return sum(map(abs,v.values()))
def block_case(ps,gs,t):
    ans=Q(1)
    for g in gs:
        def bias(mask):return prod(1-2*p for i,p in enumerate(ps) if mask>>i&1)
        ans*=max(bias(t&g),bias(g^(t&g)))
    return ans
def majority(n,x):
    pp=(1+x)/2
    return 2*sum(comb(n,i)*pp**i*(1-pp)**(n-i) for i in range(n//2+1,n+1))-1
samples=0
for n in range(2,9):
    for _ in range(40):
        sep=rng.randrange(1,n)
        gs=[(1<<sep)-1,((1<<n)-1)^((1<<sep)-1)]
        ps=[Q(rng.randrange(5),8) for i in range(n)]
        t=rng.randrange(1<<n)
        assert exact(n,gs,t,ps)==block_case(ps,gs,t)
        samples+=1
for k in range(12):
    for x in map(lambda i:Q(i,16),range(17)):
        s=Q(7,8)
        def poly(y):return y*sum(Q(comb(2*j,j),4**j)*(1-y*y)**j for j in range(k+1))
        assert majority(2*k+1,x)==poly(x)
        assert majority(2*k+1,s*x)>=s*majority(2*k+1,x)
g=4095
for _ in range(128):
    weights=[rng.randrange(301) for i in range(g)]
    j=min(range(g),key=weights.__getitem__)
    wire=1;cost=0
    for i,w in enumerate(weights):
        z=(1-wire)^(i==j)
        cost+=w*sum(a!=b for a,b in zip((z,z^wire,z^wire,z),(1,1,1,0)))
        wire=z
    assert wire==1 and cost==sum(weights)+2*weights[j] and g*weights[j]<=sum(weights)
print(samples,'exact block laws; 204 majority identities; 128 full-length weighted NO certificates')

```

### Fixed NAND code routing

```python
"""Route named NAND ports through a full Beneš network and count all code mismatches."""
from itertools import permutations
from random import Random


def route(perm, values):
    """Source i has destination perm[i]. Return values in destination order and cost."""
    n = len(perm)
    if n == 2:
        out = values[::-1] if perm[0] else values[:]
        return out, switch_cost(values, out, perm[0])
    inv = [0] * n
    for i, dest in enumerate(perm):
        inv[dest] = i
    color = [-1] * n
    for i in range(n):
        if color[i] >= 0:
            continue
        color[i] = 0
        todo = [i]
        while todo:
            j = todo.pop()
            for neighbor in (j ^ 1, inv[perm[j] ^ 1]):
                if color[neighbor] < 0:
                    color[neighbor] = 1 - color[j]
                    todo.append(neighbor)
                assert color[neighbor] != color[j]
    tracks = [[], []]
    subperm = [[], []]
    cost = 0
    for i in range(0, n, 2):
        sel = color[i]
        pair = [values[i + sel], values[i + 1 - sel]]
        cost += switch_cost(values[i:i+2], pair, sel)
        for side in (0, 1):
            tracks[side].append(pair[side])
            subperm[side].append(perm[i + (sel ^ side)] // 2)
    top, a = route(subperm[0], tracks[0])
    bot, b = route(subperm[1], tracks[1])
    out = []
    for i, pair in enumerate(zip(top, bot)):
        sel = color[inv[2*i]]
        dest = pair[::-1] if sel else pair
        cost += switch_cost(pair, dest, sel)
        out.extend(dest)
    return out, cost + a + b


def switch_cost(x, y, sel):
    return sum(2 * (x[i] != y[j]) if i ^ j == sel else 1
               for i in range(2) for j in range(2))


def circuit(inputs, gates, witness, flip_terminal=False):
    vals = [1, *witness]
    reads = []
    gate_cost = 0
    for i, (a, b) in enumerate(gates):
        a = a if 0 <= a < len(vals) else 0
        b = b if 0 <= b < len(vals) else 0
        x, y = vals[a], vals[b]
        z = (1 - x*y) ^ (flip_terminal and i == len(gates)-1)
        gate_cost += sum(v != u for v, u in zip((z, z^x, z^y, z^x^y), (1,1,1,0)))
        reads.extend(((a, x), (b, y)))
        vals.append(z)
    entries = list(enumerate(vals)) + reads
    n = 1 << (len(entries)-1).bit_length()
    entries.extend([(len(vals), 0)] * (n-len(entries)))
    order = sorted(range(n), key=lambda i: entries[i][0])
    dest = [0] * n
    for j, i in enumerate(order):
        dest[i] = j
    out, cost = route(dest, [v for _, v in entries])
    assert out == [entries[i][1] for i in order]
    keys = [entries[i][0] for i in order]
    for j in range(1, n):
        cost += 2 * (out[j] != out[j-1]) if keys[j] == keys[j-1] else 1
    assert len(witness) == inputs
    return cost + gate_cost + 2*(1-vals[-1]), vals[-1]


if __name__ == "__main__":
    for p in permutations(range(8)):
        out, _ = route(p, list(range(8)))
        assert all(out[j] == i for i, j in enumerate(p))
    rng = Random(225)
    random_gates = [(rng.randrange(129+i), rng.randrange(129+i)) for i in range(4095)]
    for terminal in ((0,0), (128+4095, 128+4095), (99999,99999)):
        gates = random_gates + [terminal]
        witness = [rng.randrange(2) for _ in range(128)]
        w, z = circuit(128, gates, witness)
        assert w == 450689 + 2*(1-z)
        w2, z2 = circuit(128, gates, witness, True)
        assert w2 == 450689 + 2 + 2*(1-z2)
    print("40320 eight-port permutations and six 16384-port NAND encodings passed")

```
