---
title: An assumption-free CircuitSAT baseline parameterized by live wires
refs: [definition:WE_CircuitSAT, note:we-circuitsat-bruteforce-explicit-cost]
tags: [witness-encryption, baseline, circuit-sat, dynamic-programming]
---

A useful control for cryptographic WE is how much time the encryptor needs to decide the *public* statement on the circuit family being measured. The existing machine baseline evaluates all 2^128 assignments. There is also an exact instance-sensitive decision algorithm using the registered gate order and the actual forward-reference convention. This is a specialization of [variable elimination](https://ics.uci.edu/~dechter/publications/r48b.pdf) to a gate-by-gate scan.

Normalize each read of wire zero or of a not-yet-created gate to constant true at the particular gate reading it. Keep a future-read counter for each real wire, counting both operands even when they coincide. Add a final read of the output wire. After each gate retain only the distinct bit tuples on already introduced wires with a positive future count. At first use of an input bit, extend each tuple both ways, once per distinct new input. Compute the NAND, consume the reads, append the output if needed, project onto the remaining live wires, and merge duplicate tuples. The single empty tuple starts the scan. A zero-gate instance has the evaluator's initial output true.

**Invariant.** The table after each gate is exactly the projection of all assignment prefixes evaluated so far onto the retained wires. At first use, every new bit is independent of every prefix. NAND is deterministic on the extended tuple. A removed coordinate has no subsequent read, so its existential projection preserves every possible future result. Induction gives exact satisfiability by testing whether the final output can be true. Set Enc to the message bit AND this answer, and Dec to the ciphertext bit. This yields perfect per-witness correctness and identical ciphertexts on false circuits, including against a quantum distinguisher receiving that classical bit.

Let w be the maximum number of retained coordinates **after first-use expansion and before computing a gate**. For s gates, at most s times 2^min(w,n) candidate tuples are processed. The width bound counts available bit patterns; the n bound follows because every candidate is realized by some assignment to the n inputs. The code below counts candidates before projection, including those that yield duplicates. This excludes parsing, width per tuple, indexing and deduplication. Tables can be canonicalized deterministically by sorting. A capped version can drop the table and restart the existing exhaustive algorithm on the original statement once the next expansion would exceed its budget. Its worst-case cost includes the abandoned prefix. There is no resulting certified improvement in the worst-case machine clock yet.

**Reproducible controls.** The reference implementation below compares against direct evaluation on all 625 two-input two-gate circuits, including repeated and forward reads, plus 1500 seeded cases. The full-size SAT control computes the conjunction of all inputs. The UNSAT control conjoins that result with the negation of the first input, which forces the first bit to remain live. Both have exactly 4096 gates after padding with unused NANDs. The SAT control gives 4604 candidate tuples at peak width 2. The UNSAT control gives 4987 at peak width 3. These deliberately narrow controls test opposite outcomes at the registered sizes; no width distribution for general circuits is assumed. The open machine problem is to bound parsing the unary indices and constructing/projecting/deduplicating the tables on sequential tapes.

~~~python
from itertools import product
from collections import Counter
from random import Random

def frontier(n, gates):
    normalized = [tuple(x if 0 < x < n+1+j else 0 for x in g)
                  for j,g in enumerate(gates)]
    refs = Counter(x for g in normalized for x in g if x)
    refs[n+len(gates)] += 1
    live, rows = [], {()}
    count = peak = 0
    for j,g in enumerate(normalized):
        z = n+1+j
        fresh = sorted({x for x in g if 0 < x <= n and x not in live})
        current = live+fresh
        peak = max(peak,len(current))
        for x in g:
            refs[x] -= 1
        keep = [x for x in current+[z] if refs[x] > 0]
        out = set()
        for row in rows:
            for bits in product((False,True), repeat=len(fresh)):
                vals = dict(zip(current,row+bits))
                vals[0] = True
                vals[z] = not (vals[g[0]] and vals[g[1]])
                out.add(tuple(vals[x] for x in keep))
                count += 1
        live, rows = keep,out
    return (not gates or (True,) in rows), count, peak

def brute(n,gs):
    for bits in product((False,True),repeat=n):
        wires=[True,*bits]
        for u,v in gs:
            wires.append(not ((u>=len(wires) or wires[u]) and (v>=len(wires) or wires[v])))
        if not gs or wires[-1]:
            return True
    return False

def check(n,gs):
    assert frontier(n,gs)[0] == brute(n,gs)

for gs in product(product(range(5),repeat=2),repeat=2):
    check(2,gs)
rng=Random(1701)
for _ in range(1500):
    n,s=rng.randrange(1,7),rng.randrange(1,11)
    check(n,[(rng.randrange(n+s+1),rng.randrange(n+s+1)) for _ in range(s)])

def full(contradiction):
    n=128
    gs=[(0,0)]*(4096-254-(3 if contradiction else 0))
    def gate(u,v):
        gs.append((u,v))
        return n+len(gs)
    acc=1
    for j in range(2,129):
        t=gate(acc,j)
        acc=gate(t,t)
    if contradiction:
        t=gate(1,1)
        q=gate(acc,t)
        gate(q,q)
    assert len(gs)==4096
    return gs
for flag in (False,True):
    print(flag,frontier(128,full(flag)))
~~~
