---
title: Recompute NAND interiors and compare split encryption with the direct ABE item count
refs: [definition:WE_CircuitSAT]
tags: [witness-encryption, compilation, cost]
---

Fix any two-way partition of the NAND gates, with the output check owned by
its producing gate. Enumerate a boundary assignment for every wire touching
both sides, including shared primary inputs. A gate output counts as touching
its producer and all its consumers. Let c count boundary wires and p_L,p_R
count the used primary inputs private to each side. Ignore unused primary
inputs. On either side take only its private primary inputs as the witness.
In original topological order evaluate all owned gates, reading externally
produced wires from the boundary. For every owned boundary output compare
the computed bit with its branch value. Check the output bit on its owner.
All gates, including internal fanout, remain deterministic. The test works
even if dependencies cross the partition multiple times in either direction.

For an honest witness evaluate once to select the branch. Conversely, two
accepting local witnesses define a consistent global primary assignment:
private inputs have unique owners and shared ones use the branch bits.
Induction over the original topological order gives the computed values on
both sides, since every imported gate value was checked on its producer.
In particular, an incorrect guess with an otherwise free imported wire
cannot provide spurious acceptance. Encrypt independent XOR shares on
the two local predicates for each branch as in the mixed separator
compiler. On NO inputs at least one leaf in every branch is false.

**Cost for a concrete split template.** Use the existing two-part KP-ABE
enumeration independently on each local verifier. Under a balanced split
of k primary witness bits the item count is B(k)=2^floor(k/2)+2^ceil(k/2)
(one term for keys and one for ciphertexts). For this template the total
is precisely 2^c (B(p_L)+B(p_R)), with fresh local instances as required.
Direct enumeration on the unsplit verifier costs B(n) for n used primary
inputs. These counts exclude ABE setup, public parameters, local circuit
size, root payload encoding, branch parsing and per-item operations. Even
equal counts may have unequal running times. Smaller leaves may change
per-item costs. Constant or empty leaves can be specialized separately.

For polynomial-time partition heuristics the preceding anchored-cut
network can target a(c+p_L)+b(c+p_R)+d c. Keep the touch arcs of weights
a,b only for primary inputs, give primary split arcs weight d, and give
gate-output split arcs weight a+b+d with zero touch cost. This implements
the displayed objective exactly; scoring candidate partitions by the
actual balanced-item formula accounts for its parity effects. Always
include direct encryption as a candidate before claiming an improvement.

On the same 24 NAND circuits and the same pins as the anchored-cut note,
the four-gate prefix totals 3992 local items. Exhausting the 16 permitted
partitions per circuit lowers that total to 1390. Direct encryption totals
296 items and wins on all 24 (no strict split improvement). The earlier
15232 figure scored exhaustive local assignments including internal gate
outputs; it is not a comparable ABE item count. The test below also checks
both local evaluators against the full NAND computation for every primary
assignment and matching-primary boundary guess at the chosen partition.

There are regimes where splitting helps the item count. With two independent
64-primary subcircuits whose outputs feed a final AND, put the final gate
with the right subcircuit (implement AND by two NAND gates). There is one
crossing gate output. The template gives 8 times 2^32 local items versus
2 times 2^64 direct items, assuming all 128 inputs are used. Both grow
exponentially in subcircuit input width. No new primitive or generic
polynomial construction follows from this counting improvement.

~~~python
from itertools import combinations, product
from random import Random
def bag(z):return (1<<(z//2))+(1<<((z+1)//2))
rng=Random(109)
for _ in range(800):
    vs=rng.sample(range(1,6),rng.randint(1,3))
    for x in vs:rng.choice((-1,1))
tot=[0]*5
checks=0
for case in range(24):
    gates={z:rng.sample(range(1,z),2) for z in range(7,15)}
    allg=set(gates)
    used=set.union(*(set(ab) for ab in gates.values()))&set(range(1,7))
    def stats(L):
        R=allg-L
        def wires(S):return S|{x for z in S for x in gates[z]}
        A,B=wires(L),wires(R)
        F=A&B
        l,r=len((A-B)&used),len((B-A)&used)
        return (1<<len(F))*(bag(l)+bag(r)),F
    parts=[{7,8}|set(z) for j in range(5) for z in combinations(range(9,13),j)]
    score,L=min((stats(S)[0],i) for i,S in enumerate(parts))
    L=parts[L]
    val,F=stats(L)
    def local(S,assignment,bd):
        t=assignment|bd
        for z,ab in gates.items():
            if z not in S:continue
            bit=1-(t[ab[0]]&t[ab[1]])
            if z in bd and bit!=bd[z]:return False
            t[z]=bit
        return 14 not in S or t[14]==1
    for bits in product(range(2),repeat=len(used)):
        w=dict(zip(sorted(used),bits))
        t=dict(w)
        for z,(a,b) in gates.items():t[z]=1-(t[a]&t[b])
        accepts=False
        for bs in product(range(2),repeat=len(F)):
            bd=dict(zip(sorted(F),bs))
            if any(bd[x]!=w[x] for x in F&used):continue
            ok=all(local(S,{x:w[x] for z in S for x in gates[z] if x in used-F},bd)
                   for S in (L,allg-L))
            assert ok==(t[14]==1 and all(t[x]==bd[x] for x in F))
            accepts|=ok
            checks+=1
        assert accepts==bool(t[14])
    direct=bag(len(used))
    for i,z in enumerate([stats({7,8,9,10})[0],score,direct,min(direct,score),int(score<direct)]):tot[i]+=z
print(tot,checks)
~~~
