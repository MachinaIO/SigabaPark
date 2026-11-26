---
title: Folding binary WE intervals using reachable rows and all future continuations
refs: [definition:WE_CircuitSAT, note:pq-we-binary-interval-products, note:pq-we-live-clause-matrix-product]
tags: [witness-encryption, compilation, complexity, correctness]
---

The full matrix product of a witness interval can distinguish substrings that no execution of the verifier distinguishes. The compiler below merges substrings whose actions agree for every attainable input row and every possible continuation. It still submits two binary matrices per retained level to the existing tensor encoder. All preprocessing uses both public message programs, keeping layout and witness routing independent of the encrypted bit.

**Context test.** For each message separately, compute a basis L_i of the rational span of all attainable rows before level i. Starting with the initial row, extend the current basis under each of the two branches and retain linearly independent original rows. Also compute a matrix R_j whose columns span all columns of all continuation products after the chosen endpoint j. Start with the identity at the end and propagate backwards through the two branches. Equality of L_i P R_j for two interval products is equivalent to equality of all complete terminal rows in every original surrounding context. For a zero space the listing retains one zero row. An interval state is the pair of such signatures for the two messages. Extending equivalent representatives by a common next bit preserves equivalence because the branch maps the next suffix span into the present one. A public cap bounds the number of states. Retain one actual substring product per state for reconstruction.

**Binary implementation and composition.** If at most two joint states remain, use the representative products directly when binary. Otherwise for each message seek a binary matrix B satisfying L_i B=L_i P for its representative P. For each target column of L_i P, solve for a subset of the columns of L_i summing to that target. The bounded subset-sum search uses the nonnegative original rows retained for L_i and may miss solutions. Every returned solution is exact. It is important that this synthesis matches the representative on the entire reachable row, even though signatures only test its observable suffix action. This prevents successive synthesized matrices from taking the computation outside the certified space.

For a fixed original path, replace one interval word at a time by the actual word for its reached signature. Each replacement preserves the terminal row in the resulting *original* context and does not affect the words or routing in disjoint intervals. The final path is the concatenation of representatives. Now replace their matrices by the synthesized matrices from left to right; at every boundary the current row equals that of this representative path. Conversely every grouped choice has a realizing local word, including the duplicate of a singleton, so every grouped path evaluates as an original path for both messages. Thus the compiler preserves valid witness outputs and preserves the full-path false-instance condition needed for hiding. Intermediate prefix values and energies may change; re-evaluate security and honest parameters on the compiled program. This changes the frontend only.

**Cost.** For polynomial caps the searches, exact basis extraction and suffix dynamic program run in polynomial time in H and w. Each span has dimension at most w. Actual product entries have O(1+H log(max(2,w))) bits, and fraction sizes in elimination are polynomial by minor bounds. The reference revisits admitted intervals to reconstruct routing. Cap overflow or failed synthesis can discard potential improvements. Every single binary level is admissible. Moreover, each interval admitted by the earlier full-product compiler remains admissible here at the same state cap: projection cannot increase the number of distinct products, and all original endpoint products on such an interval are binary. Witness lookup takes one routing transition per original bit, as before. The extra compilation time should be charged on Enc if no preprocessing is shared.

**Where it helps.** In a three-state control, successive pairs of witness bits implement an OR test followed by continuation or permanent failure. A temporary state has different transitions on substrings that are indistinguishable from the attainable starting state. Append four independently chosen two-message binary levels, so the final row also depends on the suffix. At 16 OR tests the previous compiler keeps all 36 levels; the new one keeps five at the same width. At fixed backend dimensions this changes transition preimage draws from 70m to 8m and selected square products from 35 to four, plus the public routing. This is a structured representation example; the OR tests are easy to evaluate publicly. It makes no security-matched timing or universal compression claim.

**Where it did not help.** On exactly the preceding 60 five-NAND circuits, the total 492 compiled levels stayed at 492. Comparing the original, reversed and increasing-variable-frequency orders, while excluding any order wider than the original, gave 489 levels with either interval algorithm. Thus the small improvement there came entirely from public variable ordering. The implementation also compared all original witness strings on 60 random message-paired programs and six nine-level NAND encodings, checking exact terminal rows for both messages and realizability of every grouped path up to duplicate labels.

Use mm and project from the preceding binary-interval note. The input layout is unchanged; additionally supply the two public initial rows.

~~~python
from fractions import Fraction

def independent(rows):
    pivots={}
    chosen=[]
    for row in rows:
        v=list(map(Fraction,row))
        for j in sorted(pivots):
            if v[j]:
                c=v[j]
                v=[x-c*y for x,y in zip(v,pivots[j])]
        j=next((i for i,x in enumerate(v) if x),None)
        if j is not None:
            pivots[j]=[x/v[j] for x in v]
            chosen.append(row)
    return tuple(chosen) or (rows[0],)

def lift_matrix(L,T,raw,cap):
    if all(x in (0,1) for row in raw for x in row):
        return raw
    w=len(raw)
    items=tuple(zip(*L))
    zero=(0,)*len(L)
    columns=[]
    for target in zip(*T):
        sums={zero:0}
        for i,item in enumerate(items):
            if target in sums:
                break
            for v,mask in list(sums.items()):
                u=tuple(a+b for a,b in zip(v,item))
                if any(a>b for a,b in zip(u,target)) or u in sums:
                    continue
                if u==target:
                    sums[u]=mask|(1<<i)
                    break
                if len(sums)<cap:
                    sums[u]=mask|(1<<i)
        if target not in sums:
            return None
        columns.append(sums[target])
    return tuple(tuple((col>>i)&1 for col in columns) for i in range(w))

def span_fold(levels,initial,mm,cap=8,lift_cap=128):
    H=len(levels);w=len(initial[0])
    if H==0 or cap<2 or lift_cap<1:
        raise ValueError("invalid program or cap")
    I=tuple(tuple(int(i==j) for j in range(w)) for i in range(w))
    bases=[tuple((tuple(row),) for row in initial)]
    for level in levels:
        bases.append(tuple(independent(mm(L,level[mu][0])+mm(L,level[mu][1]))
                           for mu,L in enumerate(bases[-1])))
    suffix=[None]*(H+1)
    suffix[H]=(I,I)
    for j in reversed(range(H)):
        suffix[j]=tuple(independent(tuple(zip(*mm(levels[j][mu][0],tuple(zip(*R)))))+
                                    tuple(zip(*mm(levels[j][mu][1],tuple(zip(*R))))))
                        for mu,R in enumerate(suffix[j+1]))
    def intervals(i):
        L=bases[i]
        states={(I,I):(I,I)}
        routes=[]
        for j in range(i,H):
            new={};ids={};table=[]
            R=tuple(tuple(zip(*r)) for r in suffix[j+1])
            for raw in states.values():
                edges=[]
                for bit in (0,1):
                    M=tuple(levels[j][mu][bit] for mu in (0,1))
                    nxt=tuple(mm(raw[mu],M[mu]) for mu in (0,1))
                    key=tuple(mm(mm(L[mu],nxt[mu]),R[mu]) for mu in (0,1))
                    if key not in new:
                        if len(new)>=cap:
                            return
                        new[key]=nxt
                        ids[key]=len(new)-1
                    edges.append(ids[key])
                table.append(tuple(edges))
            routes.append(table)
            states=new
            if len(new)<=2:
                pairs=[tuple(lift_matrix(L[mu],mm(L[mu],raw[mu]),raw[mu],lift_cap) for mu in (0,1))
                       for key,raw in new.items()]
                if all(B is not None for pair in pairs for B in pair):
                    yield j+1,tuple((pairs+pairs[-1:])[:2]),routes
    cost=[H+1]*H+[0];cut=[None]*H
    for i in reversed(range(H)):
        for end,_,_ in intervals(i):
            if 1+cost[end]<cost[i]:
                cost[i]=1+cost[end];cut[i]=end
    groups=[];i=0
    while i<H:
        end,pair,route=next(v for v in intervals(i) if v[0]==cut[i])
        groups.append((pair,route))
        i=end
    return groups
~~~
