---
title: Selecting witness order by ciphertext and honest-operation costs
refs: [definition:WE_CircuitSAT, note:pq-we-lookahead-coordinates, note:pq-we-live-clause-matrix-product]
tags: [witness-encryption, compilation, complexity, correctness]
---

Which witness bit is consumed first changes the intermediate dimensions of a tensor ciphertext. In particular, gate-output bits are available to a decryptor who first evaluates the circuit on the witness. They need not follow the original circuit inputs in the matrix program. A variable renaming preserves literals, clauses, and assignments bijectively. On a valid trace the renamed program therefore recovers the same message. On a false instance every permuted assignment still has a failing clause, so the group program still outputs a unit coefficient. The chronological NAND evaluation to obtain the trace happens before the permutation and costs linear time in the circuit size.

For a nonempty trace of H bits, try four public orders, deduplicated. Try the natural order and its reverse. Construct a third order by repeatedly choosing the variable that leaves the fewest clauses meeting both the prefix and its complement. Break ties by larger clause occurrence count and then variable number. Try this order and its reverse. Compile all candidates with the same cap, equality reduction and lookahead compiler. Discard any candidate exceeding the natural-order raw payload, preimage-column count or dense Dec multiply-add count. Among the rest minimize those three counts lexicographically. This protects all three structural accounts for the fixed parameters used by the selector. It can miss better permutations.

The selector can be run as public preprocessing once per statement. If charged to Enc it invokes the polynomial compiler at most four times, and a naive boundary-score computation costs O(H³ L) elementary set operations for total clause length L (including clause headers). No witness or message enters the selector. Dec can obtain the permutation from public preprocessing, or the ciphertext can name the candidate with two bits when the statement and order-generation rule are shared. Reading a permuted word costs O(H) indexed accesses once the trace and order are available. The accounts below exclude these metadata, preprocessing, key generation and sampling time. If each candidate needs different parameters for correctness and hiding, price the verified parameter sets individually before selecting. In a reduction for any public instance, the modified program and permutation are deterministic public functions of that instance. A uniform hiding theorem for all such programs at the chosen dimensions would transport directly. The missing quantum evasive-LWE hop remains necessary for the proposed backend.

**Checks.** At n=4 and k=32 on the previous 60 four-input five-NAND controls, candidate selection improves payload on 59. All 61,440 assignments and message bits recover their entire expected group-output vector. The direct clause check uses the original, unpermuted assignment as an independent oracle. The larger control uses one seeded 16-variable, 28-clause random 3-CNF and checks 1,024 sampled assignments/messages. These are logical checks and raw arithmetic accounts for one-bit messages. The small NAND controls are publicly solvable, and neither experiment estimates the difficulty of the chosen parameters.

| Corpus and order | Full-root payload bits | Preimage columns | Dense Dec multiply-adds |
| --- | ---: | ---: | ---: |
| 60 NAND, natural | 61499244544 | 1315328 | 3843031040 |
| 60 NAND, selected | 26669940736 | 859648 | 1666187264 |
| Single 3-CNF, natural | 18316722176 | 128000 | 1144782848 |
| Single 3-CNF, selected | 13895925760 | 110080 | 868483072 |

Run the listing from the DAG root with Python 3.

~~~~python
def orders(clauses, height):
    natural = tuple(range(1, height + 1))
    supports = [set(map(abs, c)) for c in clauses]
    seen = set()
    order = []
    while len(order) < height:
        def score(x):
            prefix = seen | {x}
            return (sum(bool(c & prefix) and not c <= prefix for c in supports),
                    -sum(x in c for c in supports), x)
        x = min((x for x in natural if x not in seen), key=score)
        order.append(x)
        seen.add(x)
    greedy = tuple(order)
    return list(dict.fromkeys((natural, natural[::-1], greedy, greedy[::-1])))

def select_order(clauses, height, n, k, pack, reduce, fold, independent, resources):
    best = None
    for order in orders(clauses, height):
        position = {v: i for i, v in enumerate(order, 1)}
        renamed = [[position[abs(v)] * (1 if v > 0 else -1) for v in c]
                   for c in clauses]
        groups, row, raw = pack(renamed, height, 4)
        init, layers, widths, restore = reduce(row, raw, independent)
        init, layers, widths = fold(init, layers, widths, independent)
        cost = resources(widths, n, k)
        result = (cost, order, init, layers, widths, restore, groups)
        if best is None:
            baseline = cost
            best = result
        elif all(a <= b for a, b in zip(cost, baseline)) and cost < best[0]:
            best = result
    return baseline, best

from pathlib import Path
from itertools import product
from random import Random

def listing(slug):
    content = Path('dag/Notes/pq-we-' + slug + '.md').read_text()
    namespace = {}
    exec(content.split('~~~python\n', 1)[1].split('\n~~~', 1)[0], namespace)
    return namespace

pack = listing('unit-output-clause-groups')['pack_groups']
red = listing('rectangular-levels')
fold = listing('lookahead-coordinates')['feature_fold']
independent = listing('contextual-interval-products')['independent']
source = Path('dag/Notes/pq-we-live-clause-matrix-product.md').read_text()
front = {}
exec(source.split('~~~python\n', 1)[1].split('def run_tests')[0], front)
rng = Random(712)
totals = [[0]*3 for _ in range(2)]
wins = 0
checks = 0
for trial in range(60):
    clauses = front['nand_cnf'](4, [(rng.randrange(5+j), rng.randrange(5+j))
                                    for j in range(5)])
    base, chosen = select_order(clauses, 9, 4, 32, pack, red['reduce_layers'],
                                fold, independent, red['resources'])
    cost, order, init, layers, widths, restore, groups = chosen
    for total, values in zip(totals, (base, cost)):
        for j, value in enumerate(values):
            total[j] += value
    wins += cost[0] < base[0]
    for bits in product((0, 1), repeat=9):
        word = [bits[x-1] for x in order]
        def fails(c, assignment):
            return all(assignment[abs(x)-1] != (x > 0) for x in c)
        flags = [int(any(fails(c, word) for c in group)) for group in groups]
        assert any(flags) == any(fails(c, bits) for c in clauses)
        for mu in (0, 1):
            row = init[mu]
            for pair, width, bit in zip(layers, widths[1:], word):
                dest = [0]*width
                for i, j in pair[bit]:
                    dest[j] += row[i]
                row = dest
            output = [0 if j is None else row[j] for j in restore]
            assert output == [mu] + flags + [0]*(len(output)-1-len(flags))
            checks += 1
print(totals, wins, checks)

def larger_control(pack, red, fold, independent):
    rng = Random(20261127)
    clauses = [tuple(x if rng.randrange(2) else -x for x in rng.sample(range(1, 17), 3))
               for _ in range(28)]
    base, chosen = select_order(clauses, 16, 4, 32, pack, red['reduce_layers'],
                                fold, independent, red['resources'])
    cost, order, init, layers, widths, restore, groups = chosen
    for trial in range(1024):
        bits = [rng.randrange(2) for _ in range(16)]
        mu = trial % 2
        row = init[mu]
        for pair, width, x in zip(layers, widths[1:], order):
            dest = [0]*width
            for i, j in pair[bits[x-1]]:
                dest[j] += row[i]
            row = dest
        out = [0 if j is None else row[j] for j in restore]
        assert out[0] == mu and all(y in (0, 1) for y in out)
        assert any(out[1:]) == any(all(bits[abs(v)-1] != (v>0) for v in c) for c in clauses)
    print(base, cost, len(groups), widths)
larger_control(pack, red, fold, independent)
~~~~
