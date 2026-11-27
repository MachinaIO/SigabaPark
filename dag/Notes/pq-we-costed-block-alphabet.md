---
title: Fusing short witness blocks in the rectangular tensor encoder
refs: [definition:WE_CircuitSAT, note:pq-we-costed-witness-order, note:pq-we-rectangular-levels]
tags: [witness-encryption, compilation, complexity, correctness]
---

Read up to d adjacent bits as one symbol. A cut from i to j has a public transition for each of its 2^(j-i) words, equal to the product of the corresponding original binary matrices. Every source coordinate in the lookahead program is live on at least one reachable prefix, and every destination coordinate is Boolean on all reachable prefixes. Since all entries are nonnegative integers, an entry above one in any such product would give an attainable destination above one. Thus the products themselves are binary, including products at the root before multiplication by the initial message row. Materialization verifies this by counting the paths joining each pair. Grouping bits bijectively preserves full assignments and the entire terminal row. For a false instance every extension still has a unit in the terminal row, so any common divisor of a grouped prefix row and the modulus must be one.

Encode each block directly with a **fresh** tensor factor, independent error, and (away from the root) fresh preimage coins for each symbol. Keys are generated only at retained cuts; decryption selects exactly one table entry per block. The new distribution requires a security argument for this alphabet. At a hop with alphabet B in the next block, the concatenation of its targets and flooding error has B times the next key width in columns. At a prefix ending after i original bits there are still 2^i paths. The hybrid must account for these dimensions, for all exposed sibling branches including at the root, and for tensor survival and error accumulation across the new number of blocks. Reusing binary security parameters solely on the strength of terminal equality is unjustified.

**Exact selection in a restricted family.** At fixed lattice dimension n and bit length k put m_j=2 n k w_j. Let R=n at the root and R=m_i elsewhere. A block with B symbols costs B k R m_j raw payload bits, B m_j preimage columns away from the root (zero at the root), and n R m_j dense decryption multiply-adds away from the root (zero at the root, where one selects a residue block). These exclude key setup, target formation, noise, scanning and public compilation. Keep an interval only if all three accounts are at most their totals for its singleton levels. Minimize the lexicographic sum of costs over a partition by shortest path through the cut indices. Singleton intervals guarantee feasibility. The local filter can exclude globally beneficial partitions. The search prices O(Hd) intervals before materializing any table. Computing the selected tables takes polynomial time in H, width and 2^d, so a fixed d or d=O(log H) preserves polynomial honest costs with polynomial-bit parameters and polynomial-time samplers. Cuts can be specified by an H-bit public mask or recomputed at preprocessing. Gains at fixed parameters are not security-matched timings.

**Controls.** On the previous 60 ordered four-input five-NAND circuits at n=4, k=32 and d=3, all 60 payloads fell. The total number of levels fell from 540 to 274. All 61,440 witness/message combinations reproduced their expected group-output vector. These small controls are publicly solvable. A separate four-bit example encodes two blocks of four symbols using bounded Gaussian preimages at q=17. For both messages and three seeds it checked all nonroot preimage congruences and the final residual identity on all 16 symbol pairs (96 path checks). This checks modular algebra without estimating a decryption error rate.

| Same ordered programs | Full-root payload bits | Preimage columns | Dense Dec multiply-adds |
| --- | ---: | ---: | ---: |
| One bit per level | 26669940736 | 859648 | 1666187264 |
| Selected blocks of up to three bits | 18282577920 | 586752 | 657719296 |

Run the following listing from the DAG root. The Gaussian check uses NumPy.

~~~~python
def choose_blocks(widths, n, k, max_bits):
    h = len(widths) - 1
    m = [2*n*k*w for w in widths]
    def cost(i, j):
        alphabet = 1 << (j-i)
        rows = m[i] if i else n
        return (alphabet*k*rows*m[j], alphabet*m[j] if i else 0,
                n*rows*m[j] if i else 0)
    zero = (0, 0, 0)
    def add(a, b):
        return tuple(x+y for x,y in zip(a,b))
    best = [(zero, ())]
    for j in range(1, h+1):
        options = []
        separate = zero
        for i in range(j-1, max(-1, j-max_bits-1), -1):
            separate = add(separate, cost(i, i+1))
            together = cost(i,j)
            if all(a <= b for a,b in zip(together,separate)):
                prev, cuts = best[i]
                options.append((add(prev,together), cuts+(j,)))
        best.append(min(options))
    return best[-1]

def materialize(layers, widths, cuts):
    tables = []
    i = 0
    for j in cuts:
        partial = [set((x,x) for x in range(widths[i]))]
        for pair in layers[i:j]:
            extended = []
            for prefix in partial:
                for edges in pair:
                    paths = [(a,d) for a,b in prefix for c,d in edges if b==c]
                    assert len(paths) == len(set(paths))
                    extended.append(set(paths))
            partial = extended
        tables.append(partial)
        i = j
    return tables

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
for trial in range(60):
    clauses = front['nand_cnf'](4, [(rng.randrange(5+j), rng.randrange(5+j))
                                    for j in range(5)])
    base, chosen = select_order(clauses, 9, 4, 32, pack, red['reduce_layers'],
                                fold, independent, red['resources'])
    cost, order, init, layers, widths, restore, groups = chosen
    blocked,cuts = choose_blocks(widths,4,32,3)
    tables = materialize(layers,widths,cuts)
    block_count += len(cuts)
    for total, values in zip(totals, (cost, blocked)):
        for j, value in enumerate(values):
            total[j] += value
    wins += blocked[0] < cost[0]
    for bits in product((0, 1), repeat=9):
        word = [bits[x-1] for x in order]
        def fails(c, assignment):
            return all(assignment[abs(x)-1] != (x > 0) for x in c)
        flags = [int(any(fails(c, word) for c in group)) for group in groups]
        assert any(flags) == any(fails(c, bits) for c in clauses)
        for mu in (0, 1):
            row = init[mu]
            start = 0
            for end, table in zip(cuts, tables):
                symbol = 0
                for bit in word[start:end]:
                    symbol = 2*symbol + bit
                start = end
                dest = [0]*widths[end]
                for i, j in table[symbol]:
                    dest[j] += row[i]
                row = dest
            output = [0 if j is None else row[j] for j in restore]
            assert output == [mu] + flags + [0]*(len(output)-1-len(flags))
            checks += 1
print(totals, wins, checks, block_count)

from itertools import product
from pathlib import Path
from random import Random
import numpy as np
ns={}
for s in ('clocked-preimage','ordered-radix-gadget','fraction-free-preimages'):
    p=Path('dag/Notes/pq-we-'+s+'.md')
    exec(p.read_text().split('~~~python\n',1)[1].split('\n~~~',1)[0],ns)
def check(seed, mu):
    q=17;n=2;a=2
    bits=Random(seed).getrandbits
    draw=ns['filtered_sampler'](ns['sample_squared'],ns['threshold'])
    def small():return draw(0,4,5,bits)
    def mat(rows,cols,fn):return np.array([[fn() for j in range(cols)] for i in range(rows)],dtype=object)
    def key(w):
        A,cols,lift=ns['radix_setup'](n*w,q,4,a,bits)
        m=len(cols);ell=n*w*(((q-1).bit_length()+a-1)//a)
        T=8+(m-1).bit_length()+4
        sig2=ns['radix_quality'](m-ell,a)*T
        dirs=ns['gram_prepare'](cols)
        def pre(y):return ns['gram_draw'](cols,dirs,lift(y),sig2,T-3,bits,draw)
        return np.asarray(A,dtype=object),pre
    widths=(2,2)
    bit_pair = [{(0,0),(1,1)}, {(0,0)}]
    tables = materialize([bit_pair]*4,[2]*5,(2,4))
    prev=None;public=[];ct=[];factor=[];noise=[]
    for j,w in enumerate(widths):
        if j+1<len(widths):A,next_pre=key(w)
        else:A,next_pre=mat(n*w,3,lambda:bits(20)%q),None
        public.append(A);C=[];F=[];E=[]
        for edges in tables[j]:
            M=np.zeros((2,2),dtype=object)
            for i,t in edges:M[i,t]=1
            if not j:M=np.array([[mu,1]],dtype=object)@M
            S=mat(n,n,small)
            Z=np.kron(M,S)
            err=mat(len(Z),A.shape[1],small)
            y=(Z@A+err)%q
            D=np.array([prev(list(col)) for col in y.T],dtype=object).T if j else y
            if j:assert np.array_equal(public[j-1]@D%q,y)
            F.append(Z);C.append(D);E.append(err)
        factor.append(F);ct.append(C);noise.append(E);prev=next_pre
    for path in product(range(4),repeat=2):
        val=ct[0][path[0]];P=factor[0][path[0]];e=noise[0][path[0]]
        for j,b in enumerate(path[1:],1):
            val=val@ct[j][b]%q
            e=e@ct[j][b]+P@noise[j][b]
            P=P@factor[j][b]
        assert np.array_equal(val,(P@public[-1]+e)%q)
    return [c[0].shape for c in ct]
print([check(i,mu) for i in range(3) for mu in range(2)])
~~~~
