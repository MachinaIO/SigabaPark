---
title: Bounded transition products as a public witness alphabet
refs: [definition:WE_CircuitSAT, note:pq-we-costed-block-alphabet, note:pq-we-costed-witness-order]
tags: [witness-encryption, correctness, compilation, complexity]
---

The block encoder transmits a fresh lattice block for every local bit string. Its logical matrix can coincide with those of many other strings. Generate the distinct products instead. Start at the identity at an old cut and extend each current matrix by the next zero and one branches. Merge identical products, record the two successor indices, and stop extending this interval as soon as a layer would exceed a public cap K. The products are binary by the live-coordinate argument of the block note. A table entry per distinct product now suffices. All grouping uses public matrices before the root message is applied. Encrypt directly for the resulting alphabet with independent randomness for each distinct label. The decryptor scans the bits of its block through the public selector and picks the final label.

**Why an artificial label path cannot change a NO instance.** Induction shows every state in the selector has a realizing bit prefix, and selection returns the exact ordered matrix product of the supplied bits. For each chosen block label there is a local preimage word. Blocks cover disjoint intervals, so concatenating these words realizes any tuple of labels. The circuit relation enforces wire consistency through the logical program. It follows that every label path on a NO instance has the original unit rejection coefficient, while the valid trace computed by a YES decryptor yields the original message row. This change acts on the public program *before* lattice encoding. A quantum hiding result for all eligible programs over the new label alphabets would apply to the compiled instance with identical challenge distribution in the reduction. Joint multi-label hiding and the quantum root hop still need justification at the actual dimensions. The relevant hybrid prefix counts are products of retained alphabet sizes.

**Binary-backend variant.** With K=2 and all single bits as permitted boundaries, each chosen interval has one or two distinct products. For a one-product interval use that same logical matrix at both binary labels and generate both ciphertext branches independently. A decryptor may always choose label zero there. Every binary path has a realizing original *matrix sequence*, including paths that use a redundant second label. This variant recovers a binary branching program, so it adds no multi-label security hypothesis to those already needed by the chosen binary backend. Where a theorem also requires fixed width, pad first and account for the padded costs separately. The rectangular figures below include two fresh branches at every binary level.

**Selection and costs.** Start with the previous block partition, and consider coarsenings. Set K at least the largest original block alphabet, so every old block is feasible. At each old boundary explore bounded product sets forward. Permit a coarsened interval only if its three counts are each at most the sum for the old intervals it replaces. Use the shortest-path recurrence of the block note, substituting the number of distinct products for the alphabet size. The selector reads H bits in total. At most K matrices per depth and at most H starting cuts give polynomial public compilation and selector size for polynomial K, even for a long interval. A selected plan has at most 2 H K selector transitions. These public arrays may be recomputed or supplied with explicit cuts. One-block outputs with polynomially many labels admit public SAT decision by inspecting every distinct terminal row with message zero. They can use the existing decided-instance encryption shortcut. The counts below still charge them the full single-root residue encoding.

**Experiment.** Same circuit generator, order, parameters and original block policy as the preceding note. At K=8, 57 of the 60 circuits collapsed to one block. The 60 circuits together had 161 retained labels versus 1,210 original table entries, and their selector transition targets require 8,412 bits at three bits per target, excluding framing and cuts. The multi-block subset gives the gain without any newly single-block program. All these small circuits were already publicly solvable by other means. A separate seeded 16-variable 28-clause 3-CNF returned exactly the same three counts as its previous blocking. These controls do not establish typical gains on hard instances. The listing exhaustively checks all 61,440 messages/words on the small corpus for both variants, and samples 1,024 message/word pairs on the larger control.

| Corpus and policy | Raw tensor payload bits | Preimage columns | Dense Dec multiply-adds |
| --- | ---: | ---: | ---: |
| 60 circuits, previous block partition | 18282577920 | 586752 | 657719296 |
| Same circuits, distinct products K=8 | 675086336 | 15360 | 20709376 |
| Three multi-block circuits, previous | 2180382720 | 48128 | 77594624 |
| Same three, distinct products K=8 | 666042368 | 15360 | 20709376 |
| 60 circuits, previous one-bit binary backend | 26669940736 | 859648 | 1666187264 |
| Same circuits, binary-backend variant | 20898906112 | 614912 | 1305477120 |

Run the listing from the DAG root with Python 3.

~~~~python
def product_automata(layers, widths, start, cap):
    """Yield a selector transition table and the distinct products at each cut."""
    states = [frozenset((i,i) for i in range(widths[start]))]
    for pair in layers[start:]:
        outputs = {}
        transitions = []
        for prefix in states:
            row = []
            for edges in pair:
                paths = [(a,d) for a,b in prefix for c,d in edges if b == c]
                target = frozenset(paths)
                assert len(paths) == len(target)
                if target not in outputs:
                    if len(outputs) == cap:
                        return
                    outputs[target] = len(outputs)
                row.append(outputs[target])
            transitions.append(tuple(row))
        states = list(outputs)
        yield transitions, states

def distinct_plan(layers, widths, oldcuts, n, k, cap, binary=False):
    assert cap >= (1 << max(j-i for i,j in zip((0,)+tuple(oldcuts),oldcuts)))
    assert not binary or cap == 2
    limits = [0, *oldcuts]
    def cost(i,j,labels):
        rows = 2*n*k*widths[i] if i else n
        cols = 2*n*k*widths[j]
        return (labels*k*rows*cols, labels*cols if i else 0,
                n*rows*cols if i else 0)
    prior = [cost(i,j,1<<(j-i)) for i,j in zip(limits,limits[1:])]
    best = {0: ((0,0,0), ())}
    for t,i in enumerate(limits[:-1]):
        for j,(_,states) in enumerate(product_automata(layers,widths,i,cap),i+1):
            if j not in limits:
                continue
            v = limits.index(j)
            candidate = cost(i,j,2 if binary else len(states))
            budget = tuple(map(sum,zip(*prior[t:v])))
            if all(x <= y for x,y in zip(candidate,budget)):
                total, path = best[i]
                offer = (tuple(x+y for x,y in zip(total,candidate)),path+(j,))
                if j not in best or offer < best[j]:
                    best[j] = offer
    total, cuts = best[limits[-1]]
    tables = []
    i = 0
    for j in cuts:
        automaton = []
        gen = product_automata(layers,widths,i,cap)
        for _ in range(j-i):
            step, states = next(gen)
            automaton.append(step)
        tables.append((automaton,states))
        i = j
    return total, cuts, tables

old_src = __import__('pathlib').Path('dag/Notes/pq-we-costed-block-alphabet.md').read_text()
exec(old_src.split('~~~~python\n',1)[1].split('def materialize')[0])
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
order_source = Path('dag/Notes/pq-we-costed-witness-order.md').read_text()
exec(order_source.split('~~~~python\n',1)[1].split('from pathlib import Path')[0])
rng = Random(712)
totals = [[0]*3 for _ in range(2)]
wins = 0
checks = 0
block_count = 0
root_only = 0
multiblock = [[0]*3 for _ in range(2)]
binary_total = [0]*3
binary_levels = 0
max_length = 0
label_count = 0
selector_bits = 0
baseline_labels = 0
for trial in range(60):
    clauses = front['nand_cnf'](4, [(rng.randrange(5+j), rng.randrange(5+j))
                                    for j in range(5)])
    base, chosen = select_order(clauses, 9, 4, 32, pack, red['reduce_layers'],
                                fold, independent, red['resources'])
    cost, order, init, layers, widths, restore, groups = chosen
    blocked,cuts = choose_blocks(widths,4,32,3)
    baseline_labels += sum(1<<(j-i) for i,j in zip((0,)+cuts,cuts))
    next_cost,cuts,tables = distinct_plan(layers,widths,cuts,4,32,8)
    if len(cuts)>1:
        for bucket,values in zip(multiblock,(blocked,next_cost)):
            for j,value in enumerate(values):bucket[j] += value
    binary_cost,bc,bt = distinct_plan(layers,widths,tuple(range(1,10)),4,32,2,True)
    for j,value in enumerate(binary_cost):binary_total[j] += value
    binary_levels += len(bc)
    root_only += len(cuts)==1
    max_length = max(max_length,max(j-i for i,j in zip((0,)+cuts,cuts)))
    label_count += sum(len(states) for _,states in tables)
    selector_bits += sum(6*len(step) for table,_ in tables for step in table)
    block_count += len(cuts)
    for total, values in zip(totals, (blocked,next_cost)):
        for j, value in enumerate(values):
            total[j] += value
    wins += next_cost[0] < blocked[0]
    for bits in product((0, 1), repeat=9):
        word = [bits[x-1] for x in order]
        def fails(c, assignment):
            return all(assignment[abs(x)-1] != (x > 0) for x in c)
        flags = [int(any(fails(c, word) for c in group)) for group in groups]
        assert any(flags) == any(fails(c, bits) for c in clauses)
        for mu in (0, 1):
            row = init[mu]
            start = 0
            for end, (steps,table) in zip(cuts, tables):
                symbol = 0
                for step,bit in zip(steps,word[start:end]):
                    symbol = step[symbol][bit]
                start = end
                dest = [0]*widths[end]
                for i, j in table[symbol]:
                    dest[j] += row[i]
                row = dest
            output = [0 if j is None else row[j] for j in restore]
            assert output == [mu] + flags + [0]*(len(output)-1-len(flags))
            binary_row = init[mu]
            start = 0
            for end,(steps,states) in zip(bc,bt):
                index = 0
                for step,bit in zip(steps,word[start:end]):
                    index = step[index][bit]
                dest = [0]*widths[end]
                for i,j in states[index]:dest[j] += binary_row[i]
                binary_row = dest
                start = end
            assert binary_row == row
            checks += 1
print(totals, wins, checks, block_count, root_only,max_length,label_count,baseline_labels,selector_bits)
print(multiblock, binary_total, binary_levels)

rng = Random(20261127)
clauses = [tuple(x if rng.randrange(2) else -x for x in rng.sample(range(1,17),3))
           for _ in range(28)]
_,chosen = select_order(clauses,16,4,32,pack,red['reduce_layers'],
                        fold,independent,red['resources'])
_,order,init,layers,widths,restore,groups = chosen
baseline,cuts = choose_blocks(widths,4,32,3)
cost,cuts,tables = distinct_plan(layers,widths,cuts,4,32,8)
for _ in range(1024):
    bits = [rng.randrange(2) for _ in range(16)]
    mu = rng.randrange(2)
    row = init[mu]
    start = 0
    for end,(steps,states) in zip(cuts,tables):
        index = 0
        for step,v in zip(steps,order[start:end]):
            index = step[index][bits[v-1]]
        dest = [0]*widths[end]
        for i,j in states[index]:dest[j] += row[i]
        row = dest
        start = end
    out = [0 if j is None else row[j] for j in restore]
    assert out[0]==mu and any(out[1:])==any(fails(c,bits) for c in clauses)
print(baseline,cost,cuts)
~~~~
