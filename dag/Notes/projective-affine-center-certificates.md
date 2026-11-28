---
title: Target-sensitive projective hitting sets for coherent affine NAND separators
refs: [definition:WE_CircuitSAT_Capped, definition:ProjectiveJoin, theorem:AdvancedEncryption.WE.ProjectiveJoin.compatible, theorem:AdvancedEncryption.WE.ProjectiveJoin.halfCount, theorem:AdvancedEncryption.WE.ProjectiveJoin.planeHits, theorem:AdvancedEncryption.WE.ProjectiveJoin.sharedLift]
tags: [witness-encryption, circuit-sat, finite-fields, affine-subspaces]
---

**Quantifiers.** A single fixed set S of binary 32-vectors intersects every nonempty affine fiber of codimension at most three. Thus for every system Az=b actually satisfied by a witness there is some z' in S with Az'=b. It is unnecessary for one evaluation of the row code to preserve the entire rank. For fixed nonzero b, only dual coefficients with gamma.b=1 can witness infeasibility, at most four for three independent rows. Remove dependent rows first using the known consistent RHS; a zero target always permits z=0. Absence of a solution remains absence in every restriction. For example the three rows (32,33,34) with target bits (0,1,1) at the finite point zero lose one row of rank but retain this target.

**The 580-point construction.** Identify GF(32) with five-bit polynomials modulo X^5+X^2+1. Pack a binary row of length 32 into seven coefficients, low-to-high, of a degree-at-most-six polynomial P. This injective binary linear map uses only two bits of the top coefficient. Take evaluation at 24 distinct finite elements and at infinity, meaning coefficient six. A nonzero P has at most six projective zeros: its finite root count is at most its degree, and infinity is a zero only when the degree is strictly below six. For a nonzero target b and an independent basis of rank r≤3, each of the 2^(r−1) obstructing combinations maps to a nonzero polynomial. At most 24 projective points are bad. At any remaining point, the evaluated linear map E_x from five binary coordinates to the RHS space has b in its image. Otherwise a linear functional would vanish on its range but not on b, yielding one of the forbidden dual coefficients. Row evaluations act on y by the nondegenerate coordinate dot product. Every compatible RHS of the original system, including ones with an initially dependent presentation, is covered by this argument. The theorem compatible proves the quantified projective root budget and existence of an image containing the target, parametrized by the polynomial assignment and the implication from annihilation to zero evaluation. The binary packing and inner code are explicit below.

A codimension-three affine fiber in five dimensions contains four distinct points of zero XOR. A full-rank-three fiber has dimension two, and smaller rank gives a larger flat with such a plane. The complement of the 25-point inner list consists of 13,14,21,23,25,28,29, with no distinct four of zero XOR (planeHits). Hence the list hits all compatible inner systems and includes zero. The 24 finite projection blocks each contribute at most 24 nonzero vectors; at infinity there are only four possible outputs including zero. Deduplicating the image gives exactly 580 points. Form an original-space center by the binary transpose of evaluation at x applied to y, namely z_j=dot(y, eval_x(pack(e_j))).

**571-point improvement.** Embed the 32 bits in a different 32-dimensional subspace of the same 35-dimensional coefficient space. Impose one high-bit constraint separately on evaluations at infinity, zero, and one. Set the high bits of c_6 and c_0 to zero, and the high bit of c_1 to the XOR of the high bits of c_2,...,c_5. Use the other 32 bits freely and in a fixed order. This is injective and each of the three marked images lies in a four-dimensional coordinate hyperplane. Any 15 of the 16 possible inner vectors, including zero, meet every affine subspace of codimension at most three in four dimensions: even the smallest such fiber has two elements. Other points use the 25-vector list. The three mark positions and 22 ordinary ones give at most 1+3*14+22*24=571 vectors; the replay confirms equality. For a consistent input matrix find a certificate by scanning these 571 centers for a match. This takes at most 1713 word parities for three rows. With sparse or repeated forms their signatures can instead be precomputed once per distinct public form. The 571 fixed vectors can be compiled into the public algorithm, or would take 18272 bits if serialized plainly. Their use does not add them as per-ciphertext fields.

**NAND fixtures and packet counts.** Use three private 32-bit groups holding selectable local coordinates, and one 32-bit shared center. Each leaf accepts if at least one of its active coordinates names an affine equation fulfilled at the center. A private coordinate is active when its witness bit is zero. Wire the three outputs into an AND with conventional NAND macros, padding with output-preserving pairs to 4096 gates. In the NO fixture the three duplicated local forms are z0=0, z1=0, z0 XOR z1=1. All three pairs can be solved. In the YES sibling the third condition is z0 XOR z1 XOR z2=1. The original witness selects one true coordinate per leaf; the three true equations have a common solution in the hitting set, even if its center differs from the witness center. All other witness constraints must continue to hold after such a replacement.

For each center, sample two independent common bits, give the three sides shares a,c,beta XOR a XOR c, and mask each advertised local type using its own fresh bit p. Publish masked share and p for an accessible type; repeated equal types can use one incidence. A witness reconstructs beta by XOR. On NO a side is missing at each center. Translate its ideal share by beta so all disclosed shares stay fixed; an XOR sharing of fixed parity is uniform, and the pads on inaccessible incidences can translate independently. This couples the joint public view. No computational source or quantum assumption is required on this public family. In order (raw ciphertext bits, useful coin bits), 580 centers give NO (1648,1984), YES (1744,2032); the 571 centers give NO (1644,1964), YES (1728,2006). Counts exclude statement encoding and the 2L+1 outer frame. The public algorithm can test these restricted local reaches directly. No registered end-to-end cost for this projective compiler follows from the arithmetic counts.

**Several central bags.** Let s commit to all values crossing between bag components; let P_c(s,z_c) include all constraints in component c. Give z_c pairwise disjoint physical variables; a private child witness can be included in z_c. For every fixed s and original witness one may replace each component by a certified extension at the same s. The theorem sharedLift gives simultaneous equivalence even for an arbitrary index type. A tree implementation transmits s along its running-intersection subtrees; one bag must choose one common local row for every child. For finite width w, brute-force 2^w interface branches if necessary and charge each branch, with independent pads across branches. Never paste two independently chosen auxiliary centers for the same unconditioned physical wire: z=0 and z=1 accept on separate projected edges but have no simultaneous original witness. Preserve the wire value, merge its equations into one ranked system, or prove a joint transport law. In particular two local rank-three tests may lift only as a merged rank-six system.

A mixed grammar can group arbitrary private 8-input, at-most-200-gate nonlinear NAND lists into six leaf blocks, with two 32-bit private centers (128 primary bits suffice for six 8-bit blocks, two centers and 16 remaining shared bits). A public grammar checker verifies allowed parents, ranks after conditioning on interface bits, the affine macro suffix, and the promised gate budget. For each fixed interface, tabulate 256 private inputs per nonlinear block to record reachable local row types. Use three witnesses per center, verify one common interface, and combine the two center roots by one AND. Arbitrary shared gates breaking this grammar make the interface wider or increase the number of independent center equations. Directly representing each arbitrary interbag bus by its assignment regenerates the full exponential cost. No uniformly small interface or general WE construction is established.

For public row candidate lists of at most 32 per child there are at most 32768 triples and at most 262144 possible triple/right-side obligations if every RHS must be supported. Independently uniform 32-bit centers hit a compatible obligation of rank at most three with probability at least 1/8. Repeatedly choose a point hitting at least a 1/8 fraction of the remaining list by assigning its bits one at a time. For each tentative prefix, compute the conditional expected number of newly hit obligations by Gaussian elimination of the remaining columns, counting incompatible extensions with probability zero and compatible ones with probability 2^-residualRank. The better half preserves the expectation. Thus after K steps the number of missed obligations is at most M(7/8)^K. This yields a deterministic *circuit-dependent* alternative. Enumerate structurally eligible equations and their compatible targets, without consulting global SAT reachability. Counting and generating this entire list costs time and should not be hidden in a description bound.

### Replay of the finite projective families

```python
from itertools import combinations,product
from random import Random
def dot(a,b):return (a&b).bit_count()%2
inner=[0,1,2,4,8,15,16,17,6,26,7,27,10,18,22,31,3,12,5,30,9,24,11,20,19]
def mul(a,b):
    v=0
    while b:
        if b&1:v^=a
        b>>=1;a<<=1
        if a&32:a^=37
    return v
def evaluate(row,x,variant):
    if variant==580:
        c=[(row>>(5*i))&31 for i in range(7)]
    else:
        c=[0]*7
        for i in range(7):
            w=4 if i in (0,1,6) else 5
            c[i]=row&((1<<w)-1);row>>=w
        assert not row
        c[1]|=16*(sum(a>>4 for a in c)%2)
    if x==32:return c[6]
    v=0
    for a in reversed(c):v=mul(v,x)^a
    return v
def make(variant):
    out=set()
    for x in [32,*range(24)]:
        col=[evaluate(1<<i,x,variant) for i in range(32)]
        if variant==571 and x in (0,1,32):
            assert all(v<16 for v in col)
            ys=range(15)
        else:ys=inner
        for y in ys:out.add(sum(dot(y,c)<<i for i,c in enumerate(col)))
    return sorted(out)
def sig(F,z):return sum(dot(f,z)<<i for i,f in enumerate(F))
def rank(F):
    S={0}
    for f in F:S|={s^f for s in S}
    return len(S).bit_length()-1
def first(F,b,S):
    return next((z for z in S if sig(F,z)==b),None)
def selfcheck():
    cyc=[1]
    for _ in range(31):cyc.append(mul(cyc[-1],2))
    assert cyc[-1]==1 and len(set(cyc[:-1]))==31
    assert len(set(inner))==25 and 0 in inner
    assert all(a^b^c^d for a,b,c,d in combinations(set(range(32))-set(inner),4))
    S=make(571);assert len(S)==571 and len(make(580))==580
    rng=Random(259)
    for _ in range(500):
        F=[rng.getrandbits(32) for j in range(3)]
        assert len({sig(F,z) for z in S})==2**rank(F)
    # Compare every RHS, including inconsistent dependent equations.
    F=[1,2,3]
    assert first(F,4,S) is None and all(first(F[:k]+F[k+1:],(4%(2**k))|((4>>(k+1))<<k),S) is not None for k in range(3))
    K=[32,33,34];b=6
    assert any(rank([evaluate(f,x,580) for f in K])<3 and any(sig([evaluate(f,x,580) for f in K],y)==b for y in inner) for x in [32,*range(24)])
    for fam in (580,571):
        Z=make(fam)
        for y in (0,1):
            rows=[(1,0),(2,0),(7 if y else 3,1)]
            nh=sum(dot(f,z)==v for z in Z for f,v in rows)
            print(fam,'YES' if y else 'NO','incidences/raw bits/coins',nh,2*nh,2*len(Z)+nh)
    print('recovered',first([1,2,7],4,S),'NO',first([1,2,3],4,S))
if __name__=='__main__':selfcheck()
```
