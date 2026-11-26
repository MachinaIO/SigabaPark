---
title: When shrinking the explicit WE root table gives public decision
refs: [definition:WE_CircuitSAT, note:pq-we-product-alphabet, note:pq-we-quantum-prefix-tree, note:pq-we-root-loss-budget]
tags: [witness-encryption, complexity, reduction]
---

Count the paths *after* compiling consecutive witness bits into local matrix labels. Write B_i for the number of retained labels at level i. The product-alphabet compiler supplies an independent local preimage word for every label. Thus each tuple is realizable, and every witness maps to such a tuple. For message zero the logical terminal row vanishes precisely for a valid satisfying trace. These two properties suffice for the following decision test, regardless of any hiding assumption.

**Decision boundary.** A public encryptor can count P=product B_i before running a lattice sampler. Under a public polynomial cap, enumerate the tuples when P is within budget, and test their exact terminal rows on the zero-message initialization. On these instances encrypt a bit as its AND with the decision bit; decryption returns the transmitted bit. Valid witnesses recover the message, and on false statements the ciphertext is always zero. Choose the mode from the public statement alone. Above the cap an ordinary fallback is needed unless further information about the compiler is proved. Costs are polynomial in the cap, the input and program sizes. The number of tuples is easy to count with saturation even if P is large.

There is a stronger obstruction for general CircuitSAT. Suppose a uniform deterministic polynomial-time compiler sound and complete in the above sense has a known polynomial bound P <= p(input size) on *every false circuit*. Run the capped enumeration and return YES on overflow: the hypothesized bound makes overflow impossible on NO. This would put CircuitSAT in P and hence imply P=NP. If the compiler also depends on a security parameter, this implication requires a uniform choice polynomial in input length at which the exact logical properties and bound hold. The obstruction concerns explicit listing of independently selectable, publicly evaluable label paths. A succinct proof distribution, computational hybrids which never materialize every path, and subexponential-time reductions have different requirements. Honest ciphertext size and honest Enc/Dec can be polynomial even when the explicit proof table is exponential.

**Variable-alphabet accounting.** At cut j the explicit table has product_(i<=j) B_i leaves. In the isolated-tree wrapper the factors are applied from j backwards to 1. At level i the number of parents is product_(i<l<=j) B_l. At cut j each parent has w_j m_j independent column secrets in the extension of the older tree argument, where w_j is the logical key width and m_j its lattice column count. Hence the number of single-secret hybrid terms at that cut is w_j m_j times the sum of these suffix products for i from 1 to j. Each such secret at level i uses B_i n samples with the same short design formed by the B_i transposed tensor factors; the advantage bound must be evaluated at that sample count and wrapper time. The unweighted sum across cuts below omits root-induction multipliers, Gaussian shifts, sampler distances, and the ordinary-LWE design switch. It only counts formal single-secret terms. Distinct labels must have fresh tensor factors; merely equating some logical prefixes would not justify merging the corresponding noisy proof rows. The original [VWW proof](https://ntt-research.com/wp-content/uploads/2023/01/Witness-encryption-and-null-iO-from-evasive-LWE.pdf) identifies both the explicit base table and repeated induction losses as reasons for subexponential assumptions.

**Controls.** For the previous 60 ordered four-input five-NAND circuits, n=4,k=32, m_j=2nw_jk, the original one-bit programs have 30,720 terminal tuples in aggregate, and the capped product programs have 274. The largest compressed table has 96 tuples. For the three multi-block survivors alone the totals are 1,536 versus 148. The unweighted single-secret term counts summed across cuts change from 131,749,376 to 200,448 overall, and from 15,837,440 to 134,400 on the three survivors. These counts describe program shapes; all 60 circuits are actually YES, so none is evidence of false-instance hiding. Direct evaluation agrees with independent CNF enumeration throughout the corpus; separate contradictory-unit and four-clause unsatisfiable controls exercise the NO branch. A cap of 96 suffices for all 60. In this regime the decision shortcut removes the lattice header entirely, including on the multi-block examples. The hard-instance challenge in this proof strategy is to control security loss and time when that shortcut does not apply.

Run the listing at the DAG root.

~~~~python
from math import prod

def profile(alphabets, widths, n, k):
    leaves=prod(alphabets)
    loss=0
    for j,w in enumerate(widths[1:],1):
        parents=1
        for labels in reversed(alphabets[:j]):
            loss+=parents*w*(2*n*k*w)
            parents*=labels
    return leaves,loss

def decision(init, tables, widths, budget):
    labels=[states for _,states in tables]
    if prod(map(len,labels))>budget:
        return None
    for choices in product(*labels):
        row=init[0]
        for edges,w in zip(choices,widths[1:]):
            dest=[0]*w
            for i,j in edges:
                dest[j]+=row[i]
            row=dest
        if not any(row):
            return True
    return False

from pathlib import Path
def body(slug):
    return Path('dag/Notes/pq-we-'+slug+'.md').read_text().split('~~~~python\n',1)[1].split('\n~~~~')[0]
code=body('product-alphabet')
# Load the published compiler, public generators, and no experiment loop.
exec(code.split('rng = Random(712)')[0])
rng=Random(712)
totals=[0]*4
multi=[0]*4
outcomes=[0,0,0]
for _ in range(60):
    C=front['nand_cnf'](4,[(rng.randrange(5+i),rng.randrange(5+i)) for i in range(5)])
    _,(_,order,init,layers,widths,restore,groups)=select_order(
        C,9,4,32,pack,red['reduce_layers'],fold,independent,red['resources'])
    _,cuts=choose_blocks(widths,4,32,3)
    _,cuts,tables=distinct_plan(layers,widths,cuts,4,32,8)
    compact=[widths[0]]+[widths[i] for i in cuts]
    alph=[len(states) for _,states in tables]
    values=profile([2]*9,widths,4,32)+profile(alph,compact,4,32)
    for i,val in enumerate(values):
        totals[i]+=val
        if len(cuts)>1:multi[i]+=val
    got=decision(init,tables,compact,512)
    direct=any(all(any(bits[abs(x)-1]==(x>0) for x in clause) for clause in C)
               for bits in product((0,1),repeat=9))
    assert got is not None and got==direct
    assert decision(init,tables,compact,prod(alph)-1) is None
    outcomes[int(got)]+=1
    outcomes[2]=max(outcomes[2],prod(alph))
print(totals,multi,outcomes)
for C,truth in (([(1,),(-1,)],False),
                ([(1,2),(1,-2),(-1,2),(-1,-2)],False),
                ([(1,2),(-1,2)],True)):
    _,(_,order,init,layers,widths,_,_)=select_order(
        C,2,4,32,pack,red['reduce_layers'],fold,independent,red['resources'])
    _,cuts=choose_blocks(widths,4,32,2)
    _,cuts,tables=distinct_plan(layers,widths,cuts,4,32,8)
    assert decision(init,tables,[widths[0]]+[widths[i] for i in cuts],4)==truth
~~~~
