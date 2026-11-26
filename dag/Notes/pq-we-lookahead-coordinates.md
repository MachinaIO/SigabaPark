---
title: Reducing tensor widths with public one-step lookahead coordinates
refs: [definition:WE_CircuitSAT, note:pq-we-rectangular-levels, note:pq-we-unit-output-clause-groups]
tags: [witness-encryption, compilation, correctness, complexity]
---

A witness selecting one of two matrices at each cut needs only the values that determine the outputs of both possible next steps. We construct new coordinates that measure those outputs early. This can reduce the peak width even when no two original coordinates are equal.

Start from the live, duplicate-free Boolean coordinates of the rectangular compiler. At the terminal cut retain every coordinate. Work backwards. Each retained feature is a sum of original coordinates that takes values in {0,1} on every attainable row. Pull each next feature back through each branch. Its coefficients are nonnegative integers. Every input coordinate is live on some attainable row, so a coefficient above one would force a Boolean feature to exceed one. The pullback is therefore another binary form, and all its summands have disjoint support on attainable inputs. Consider a dictionary of the original coordinates and these pullbacks. Record their values on a rational spanning basis chosen from attainable rows for both messages. Equal signatures represent equal linear functions throughout the reachable space. A disjoint union on the basis gives exact integer addition throughout that space by linearity.

For each target allow its original atomic expansion, its directly stored value, and any disjoint pair of dictionary signatures summing to it. Greedily remove entries while all targets have covers. Keep the smallest among four deterministic orders and the original atoms. On each branch the cover gives the incoming binary edges for its target. By forward induction the computed coordinates are precisely the selected features of the corresponding original row. All terminal entries, including each rejecting unit, survive identically. The construction uses at most the original width at each cut. The basis has at most that width, and the dictionary has at most the input width plus twice the successor width. All loops and exact elimination have polynomial bit cost (the basis rows are binary, hence minors have polynomial bit length). No witness enumeration is used by the compiler. There is no optimality claim. Logical rows on actual prefixes have one-norm at most the new width. Fanout can increase, so bounds on arbitrary subproducts of the old deterministic routing matrices require a fresh check.

**Costs per encrypted bit.** For H choices, maximum width W, lattice dimension n, modulus bit length k and m=2nWk, padding gives at most 2k(nm+(H-1)m²) payload bits, 2(H-1)m trapdoor column samples and n(H-1)m² dense modular multiply-adds for decryption, plus the root scan. Rectangular keys reduce these upper bounds by using neighboring actual widths. Encryption also performs key generation, target products and noise draws. With polynomial-bit parameters and polynomial-time clocked implementations, the total honest bit costs are polynomial. For NAND circuits of size s with d inputs, H=d+s and W is at most one plus the linear number of gate and output clauses. Choosing parameters that jointly establish correctness and quantum hiding at the target security level remains open. The unchanged terminal function alone does not prove the quantum evasive-LWE root hop for the transformed distribution.

**Reproduction.** Run the two listings in one Python namespace from the DAG root. For the 60 seeded circuits used in the rectangular note, all 61,440 witness/message combinations reproduce the original terminal row. Peak width fell on six circuits. The rows below total the same 60 instances at n=4 and k=32. They price general encodings of publicly solvable controls and exclude compilation and key setup.

| Width policy | Full-root payload bits | Preimage columns | Dense Dec multiply-adds |
| --- | ---: | ---: | ---: |
| Previous fixed maximum | 106764500992 | 1740800 | 6671040512 |
| Lookahead fixed maximum | 103609991168 | 1716224 | 6473908224 |
| Previous rectangular | 66312667136 | 1358848 | 4143710208 |
| Lookahead rectangular | 61499244544 | 1315328 | 3843031040 |

~~~python
def feature_fold(initial, layers, widths, independent):
    """Input has only live Boolean coordinates. Preserve all terminal outputs."""
    bases = [independent([tuple(row) for row in initial])]
    for pair, width in zip(layers, widths[1:]):
        rows = []
        for edges in pair:
            for row in bases[-1]:
                dest = [0] * width
                for i, j in edges:
                    dest[j] += row[i]
                rows.append(tuple(dest))
        bases.append(independent(rows))

    forms = [frozenset([i]) for i in range(widths[-1])]
    compiled = []
    sizes = [len(forms)]
    for stage in reversed(range(len(layers))):
        rows = bases[stage]
        def signature(form):
            values = [sum(row[i] for i in form) for row in rows]
            assert all(x in (0, 1) for x in values)
            return sum(x << k for k, x in enumerate(values))

        atoms = [signature([i]) for i in range(widths[stage])]
        dictionary = {a: frozenset([i]) for i, a in enumerate(atoms)}
        assert len(dictionary) == len(atoms) and 0 not in dictionary
        choices = []
        for edges in layers[stage]:
            for form in forms:
                sources = [i for i, j in edges if j in form]
                assert len(set(sources)) == len(sources)
                mask = signature(sources)
                if mask:
                    dictionary.setdefault(mask, frozenset(sources))
                direct = frozenset(atoms[i] for i in sources)
                options = [direct, frozenset([mask])] if mask else [direct]
                choices.append(options)

        # Also allow a target to split into two other known functions.
        for opts in choices:
            mask = sum(opts[0])
            for a in dictionary:
                b = mask ^ a
                if a < b and a & mask == a and b in dictionary:
                    opts.append(frozenset([a, b]))
        def select(order):
            active = set(dictionary)
            for key in order:
                rest = active - {key}
                if all(any(o <= rest for o in opts) for opts in choices):
                    active = rest
            return sorted(active)
        keys = list(dictionary)
        orders = [keys, keys[::-1], sorted(keys, key=int.bit_count),
                  sorted(keys, key=int.bit_count, reverse=True)]
        kept = min([sorted(atoms)] + [select(o) for o in orders], key=len)
        ids = {key: i for i, key in enumerate(kept)}
        edges = [set(), set()]
        for index, opts in enumerate(choices):
            branch, j = divmod(index, len(forms))
            chosen = min((o for o in opts if o <= ids.keys()), key=len)
            for key in chosen:
                edges[branch].add((ids[key], j))
        compiled.append(edges)
        forms = [dictionary[key] for key in kept]
        sizes.append(len(forms))
    start = [[sum(row[i] for i in form) for form in forms] for row in initial]
    return start, compiled[::-1], sizes[::-1]
~~~

~~~~python
from pathlib import Path
from random import Random
import runpy
g={}
exec(Path('dag/Notes/pq-we-unit-output-clause-groups.md').read_text().split('~~~python\n',1)[1].split('\n~~~',1)[0],g)
front={}
s=Path('dag/Notes/pq-we-live-clause-matrix-product.md').read_text()
exec(s.split('~~~python\n')[1].split('def run_tests')[0],front)
from itertools import product
from fractions import Fraction
sf={}
exec(Path('dag/Notes/pq-we-contextual-interval-products.md').read_text().split('~~~python\n',1)[1].split('\n~~~',1)[0],sf)
red={}
exec(Path('dag/Notes/pq-we-rectangular-levels.md').read_text().split('~~~python\n',1)[1].split('\n~~~',1)[0],red)
def eval_row(r,layers,bits,widths):
    for pair,bit,w in zip(layers,bits,widths):
        nxt=[0]*w
        for i,j in pair[bit]:nxt[j]+=r[i]
        r=nxt
    return r
rng=Random(712)
totals=[[0,0,0] for _ in range(4)]
num=0;improved=0
for _ in range(60):
    C=front['nand_cnf'](4,[(rng.randrange(5+j),rng.randrange(5+j)) for j in range(5)])
    gs,row,old=g['pack_groups'](C,9,4);w=len(row)
    init,new,widths,restore=red['reduce_layers'](row,old,sf['independent'])
    prev=widths
    init,new,widths=feature_fold(init,new,widths,sf["independent"])
    improved+=max(widths)<max(prev)
    assert all(a<=b for a,b in zip(widths,prev))
    for bits in product((0,1),repeat=9):
        for mu in (0,1):
            answer=eval_row(init[mu],new,bits,widths[1:])
            actual=eval_row([mu]+row[1:],old,bits,[w]*9)
            assert [0 if j is None else answer[j] for j in restore]==actual
            num+=1
    for t,ws in zip(totals,[[max(prev)]*10,[max(widths)]*10,prev,widths]):
        for j,v in enumerate(red['resources'](ws,4,32)):t[j]+=v
print(num,totals,improved)
~~~~
