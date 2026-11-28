---
title: Directional forest labels, a single shifted suffix key, and the cost of decoding public dictionaries
refs: [definition:WE_CircuitSAT_Capped, theorem:AdvancedEncryption.WE.DirectedLabels.additive_view, theorem:AdvancedEncryption.WE.DirectedLabels.chart_record, theorem:AdvancedEncryption.WE.DirectedLabels.essential_injective, theorem:AdvancedEncryption.WE.DirectedLabels.point_gap]
tags: [witness-encryption, branching-program, learning-with-errors, correctness, finite-security]
---

A designated incoming edge can deliver each internal state label without an issued correction. A bounded suffix can instead use one shift-hiding key, with a full boundary table and no subsequent state rows. An attempted further compression has polynomial issuance length on general circuits and an unbounded decoder. A known unique-witness circuit shows that making this decoder efficient would contradict the very shift-hiding property used for security. The positive and negative results concern specific complete public interfaces.

### Label shapes and direction

Publish a start label, all edge differences f(v)−f(u), and terminal records β a(t)−f(t) for independent uniform scalar labels. The two laws agree exactly if a translation h is zero at the start, constant across each *undirected* edge, and equals a(t) at every terminal. Sufficiency translates every random tape by h bijectively. Necessity takes any common transcript and subtracts its two tapes. Thus two different terminal flags in a disconnected component already separate the laws even when the start cannot reach either. Exhaustive histograms checked all 512 two-source/three-terminal examples in the listing. Removing rejecting-terminal openings changes this criterion and must be part of the specified interface.

A positive coefficient construction applies if a public state chart x_i(s) satisfies x_next(T_b s)=U_b x_i(s) and the acceptance bit is a terminal linear form a x_L. Include a constant coordinate for affine charts. Work backwards: Q_L=a, and the rows of Q_i are a basis for the union of the rows of both Q_next U_b. Compute M_b with Q_next U_b=M_b Q_i. With uniform matrices K_i of the shape of Q_i, publish K_0 x_0(start), two matrices K_next U_b−M_b K_i per layer, and βa−K_L. At a legal step evaluate the public matrix on x_i(s) and add M_b applied to the actual label. The terminal row recovers β on accepting paths. On NO, Q_0 x_0(start)=0 since every suffix from start rejects; translating *all* K_i by Q_i preserves each public coefficient, including the terminal one. This is perfect full-view equality. It emits sum_{i,b} rows(Q_next)·dim(x_i) binary entries plus the anchor, terminal and any non-reconstructible chart data. With a table chart the rows are the right-language truth vectors in compressed coordinates; unfolding M_b maps any candidate label dimension to those rows, so their binary rank lower-bounds this interface. With a small syntactically constructible chart, forward linear-span reachability also decides existence directly. No small chart for general NAND SAT follows.

For ordinary directed PRF labels, give only the start key. Select one public incoming edge per positive-indegree vertex; roots draw independent keys. Define the child key at its designated edge to equal PRF(parent key, layer, parent, branch), use this value directly on that edge, and publish a correction child key XOR PRF(parent key, distinct edge domain) on each other incoming edge. An accepting terminal supplies one bit β masked by a separate PRF output; rejecting terminals need no payload. Domain-separate terminal and edge uses. Correctness is induction along any directed path. The number of full-key corrections is |E| minus the number of positive-indegree vertices. When the symbolic indexing of the designated edge is not implicit, charge its encoding and all record addresses.

On NO replace outgoing PRF evaluations at *unreachable* vertices by independent random strings in topological order. For a challenged unreachable vertex all incoming parents are unreachable and already processed. A designated incoming pad is a fresh hidden key; other incoming ciphertexts are uniform regardless of that key. An indegree-zero challenged vertex instead uses its fresh root key. Thus a single-key simulator need not know its challenge key. It uses distinct classical queries for both siblings; oracle replies determining a designated reachable child's key are known and can drive subsequent operations. In the final hybrid unreachable accepting-terminal rows use fresh pads, so all rows jointly hide the message. This argument presupposes an explicit affordable graph, charged reachability tests, per-key hybrid loss and a suitable quantum-secure PRF against quantum computation with classical reduction queries. It is not an efficient cryptographic replacement for scanning all exponentially many energy states. An affine, otherwise secret address-to-label map can be determined on the entire affine span of exposed input/label pairs; applying a low-degree public sibling transform after that map does not restore lost label uncertainty. A public polynomial correction for affine labels must account for its entire coefficient vector. Sharing a key across branches without domain separation or counting a correction oracle as free gives no such guarantee.

### What can be folded into one shifted key

Peikert–Shiehian Construction 3.1 has a master evaluation coordinate of the form s·v_x modulo q, with v_x computable from the public parameters and x. Lemma 3.2, Figure 1 takes the adversary's bounded shift circuit before fresh setup, then gives one public-parameter/shifted-key pair. Lemma 3.8 bounds the difference between shifted evaluation and master evaluation plus the shift. The paper's programmable PRF takes an explicit polynomial-size list of points; its input-privacy game uses random programmed outputs. These are different interfaces. The base shift-key game neither gives the master nor issues a second shifted key under the same master. It assumes LWE and CPA security of GSW. The published PPT statements do not certify registered finite parameters or a concrete quantum loss. [Original paper, §§3–5](https://web.eecs.umich.edu/~cpeikert/pubs/chc-pp-prf.pdf)

For a suffix of h choices compute its acceptance circuit C(u,z) on boundary state u and suffix z. Submit one circuit for the shift Hβ(u,z)=(q/2)β C(u,z) in one output coordinate (q even, other coordinates zero), padded equally in both worlds. Use one shared public shifted key. A direct variant delivers every boundary's table of 2^h base bits via its prefix label: encrypt the vector with domain-separated PRF pads under the boundary key. Dec selects the entry indicated by its suffix, subtracts the base bit from the rounded shifted bit and recovers the message on acceptance. This variant requires the appropriate common rounding at each exposed point; pay the total probability of borderline values. Alternatively use the flooded residues below with the unit coefficient at the selected table address to eliminate a base-rounding hypothesis. The prefix label stays fixed-length. The explicit boundary still costs width·2^h entries. The suffix shift can implement arbitrary branching and merging without issuing any suffix edge records.

For NO, after sanitizing unreachable prefix keys, rows for those boundary vertices are uniform because the boundary masking streams are independent. For reachable u every suffix rejects. Their base data can therefore be reconstructed from the *one* shifted evaluator up to the charged error, including all rows in one joint view. Prefix randomness and known reachable keys can be generated locally after the challenge. Use separate terminal/opening stream domains and account for each PRF query. An earlier unsanitized key that contains the unknown future master cannot be released by invoking the single-key game. Folding both branches into one circuit on (state,branch) fixes that issuance problem only when there is also a way to deliver consistent branch-specific base data. In the bounded-suffix construction that delivery is explicit. It supplies a partial contraction rather than free iteration of two different shifts.

### Compressing the boundary with real-point columns

For a boundary let public dictionary positions z_j give columns v_j of the actual evaluation function. Send s·v_j+u_j mod q for independent integer noise uniform on [−W,W], masked under the boundary key when there is a prefix. If v_z=Σ c_j v_j mod q with signed integer coefficients of total absolute value A, subtract the same linear combination of the delivered residues from the shifted coordinate. Its distance from (q/2)β C(u,z) is at most B+A W when the shift evaluation error is bounded by B. Nearest-half decoding is exact when 4(B+A W)<q. On reachable NO rows replacing s·v_j by the shifted center changes each distribution by at most B/(2W+1), since the two integer intervals overlap in at least 2W+1−B positions; reduction modulo q cannot increase the variation. Conditional on fixed good keys, product coupling gives a total at most D B/(2W+1) for D exposed residues. Charge the bad-key/error probability η as well. Virtual doubled gadget columns are not interchangeable with actual points at which the shifted key is available.

Every finite set of columns in (Z/q)^n admits a signed dictionary of actual columns of size at most R=floor(log₂(q^n)). Choose a maximal set with distinct subset sums. The cardinal bound follows by injectivity; adjoining any excluded point produces a subset-sum collision, necessarily using the new point on just one side. Subtracting the two existing subset sums gives coefficients in {−1,0,1}. This establishes existence only: finding the set on an implicit domain and decoding its signed sums can be expensive.

### Polynomial issuance without a dictionary-search oracle

Take the prefix to be empty and C(w) the actual circuit on the 128 witness bits; a raw NAND evaluator can compute it without a trace supplied by the witness. Choose k independent uniform 128-bit salts r_i and commit to the *single* padded shift Hβ(i,x)=(q/2)β C(x XOR r_i). For each cohort i sample m independent uniform dictionary points after independent public setup. Publish salts, positions, the one shifted-key pair, and D=km flooded residues of the genuine master at these actual queries. Each position can be sampled and evaluated directly, without a coverage test. For witness w try to express v_{i,w XOR r_i} as a signed sum of its own cohort's columns. An exhaustive implementation checks all ternary coefficient vectors and verifies the modular identity; use the first success, otherwise return an arbitrary bit.

Fix w and condition on public setup. The column map depends on setup and the input, independently of the secretly shifted circuit. Within cohort i the query and m dictionary inputs are exchangeable, because the salt is uniform and independent of the dictionary. In any ordered family call a position essential if its vector cannot be a signed sum of the other positions. The indexed essential vectors have distinct subset sums: a collision gives one essential vector as the difference of two sums of other indices. This reasoning counts positions correctly even when values repeat. At most R positions are essential. Hence the chance of no representation for this query is ≤R/(m+1). Conditional on setup the coverage events across cohorts are independent, so the all-miss probability is at most (R/(m+1))^k. This is a per-fixed-witness bound; no simultaneous guarantee for all witnesses is needed. For m=2R, k=129 and R>0 it is below 2^-129. Add η for failure of the actual error bound. Noise pays A≤m. The independent salts are chosen before submitting H; all games must use a common circuit-size bound. Honest Enc is polynomial in these parameters, while general exhaustive Dec is exponential in m.

On a false statement the fundamental simulation samples the same publicly chosen points and noise, using SEval instead of the base evaluation at each sampled point. Here Hβ vanishes on *every* query, and no signed decomposition is needed by the simulator. One shift-key hybrid per bit world then suffices. The resulting distinguishing upper bound is 2ε_shift+2η+2D B/(2W+1) for the charged reductions. This is a conditional quantitative statement, requiring the actual PS noise, LWE and GSW costs, auxiliary computation, security parameters, and registry strength. No fresh hardness premise concerning a particular statement has been introduced.

### Why faster general decoding is incompatible with this interface

Take a circuit accepting exactly the known word w*. It fits the fixed registered size using literals and an AND chain with harmless padding. Compare the two shifts for this same public circuit. With probability at least 1−D/2^128 the dictionary never samples a transformed copy of w*. On that event the *same* postprocessing of a single shifted-key challenge simulates all issued residues in both worlds within the flooding error; the zero shift needs no exceptional event. Let γ bound per-message error of a candidate decoder on w*, δ=η+D B/(2W+1), and let ε_shift be the single-challenge advantage at the cost of setup postprocessing plus this decoder. Calling it on the known witness in the two simulated worlds gives a difference bounded below by

    1 − 2γ − 2δ − D/2^128,

whereas shift hiding bounds it above by 2ε_shift. Thus a general procedure for fast short-coefficient decoding with those guarantees is itself inconsistent with strong shift hiding at that cost. This is stronger than the observation that a particular ternary search is slow, and specific to this released transcript. The exponential decoder incurs a reduction cost outside the assumed efficient class. No claim here rules out other constructions.

For a C-dependent public dictionary in this flat full-domain scheme, replace D/2^128 by its probability of including *some satisfying assignment*. If the postprocessing still simulates when all sampled shifts vanish, an efficient correct decoder on every satisfiable C would force the public sampler to find a witness with high probability on each such C. A fixed valid w for the two-world comparison can be hardwired as nonuniform advice, charging its bits and use. Public evaluation of the sampled candidates then recognizes a hit without the advice. This is a fixed-parameter tradeoff; it does not imply an unconditional complexity-class collapse. In particular, the full bounded-suffix table may include the accepting position with certainty. The above sparse-sampling incompatibility does not apply to it.

The flat construction transmits D residues and D witness-size addresses, plus k salts, public parameters and shifted key. For illustration only, n=1024 and log₂ q=132 give 4,603,281,408 residue bits already at m=2R and k=129, before 4,463,788,032 address bits. Those parameters have not been justified for the shift theorem. In addition the parameters include the large public matrices, encrypted shift-program bits and noisy vectors of Construction 3.1. Parameter feedback between q, B and the circuit-size bound must be solved; the asymptotic choice in §3.4 supplies no certified registered clock here. The canonical metric sums both worst-case times and both description lengths. Neither the GGH chain nor a generic witness PRF or bounded garbling supplies a free public short-coefficient decoder. The remaining general WE construction must change the exposed interface or find another secure mechanism within that budget.

### Executable checks

Finite experiments below test the algebra, full scalar transcript histograms, and every directed path on 100 tiny forest instances. They do not instantiate the lattice cryptography.

```python
from collections import Counter
from itertools import combinations,product
from random import Random

def signed(cols,q):
    sums={0:()}
    for a in cols:
        sums={ (x+k*a)%q:coeff+(k,) for x,coeff in sums.items() for k in (-1,0,1) }
    return sums

def checks():
    # All ordered samples, with repetitions. Counts positions, not distinct values.
    for q,m in [(5,3),(8,3),(9,3)]:
        bad=total=0;R=(q.bit_length()-1)
        for seq in product(range(q),repeat=m+1):
            essential=[j for j in range(m+1)
                       if seq[j] not in signed(seq[:j]+seq[j+1:],q)]
            ss={
                sum(seq[j] for i,j in enumerate(essential) if mask>>i&1)%q
                for mask in range(1<<len(essential))}
            assert len(ss)==1<<len(essential) and len(essential)<=R
            bad+=len(essential);total+=m+1
        assert bad*(m+1)<=total*R
        print('cyclic q, m, essential positions/all positions',q,m,bad,total)
    for W in range(5):
        for e in range(-2*W-1,2*W+2):
            a=set(range(-W,W+1));b={x+e for x in a}
            assert len(a&b)==2*W+1-abs(e)
    # Tiny *arithmetic fixtures*, not cryptographic parameters.
    q=128;B=1;W=3;r=3;mkey=29;cols=(2,9,17)
    for c in product((-1,0,1),repeat=r):
        col=sum(u*v for u,v in zip(c,cols))%q
        for e in product((-W,W),repeat=r):
            d=[(mkey*v+x)%q for v,x in zip(cols,e)]
            for message,accept,err in product((0,1),(0,1),(-B,B)):
                shifted=(mkey*col+message*accept*(q//2)+err)%q
                diff=(shifted-sum(x*y for x,y in zip(c,d)))%q
                assert (q//4<diff<3*q//4)==bool(message*accept)
    print('rounding and flooding endpoint checks passed')

def component_test():
    def law(edges,labels,msg):
        out=Counter()
        for f in product(range(2),repeat=5):
            out[(f[0],tuple(f[a]^f[b] for a,b in edges),
                 tuple(f[i]^(msg*v) for i,v in labels))]+=1
        return out
    candidates=list(product(range(2),range(2,5)))
    for mask in range(1<<len(candidates)):
        edges=[v for j,v in enumerate(candidates) if mask>>j&1]
        for flags in product(range(2),repeat=3):
            labels=list(zip(range(2,5),flags))
            shift=any(not h[0] and all(h[u]==h[v] for u,v in edges)
                    and all(h[i]==j for i,j in labels) for h in product(range(2),repeat=5))
            assert (law(edges,labels,0)==law(edges,labels,1))==shift
    print('512 complete additive histogram comparisons passed')

def forest_test():
    rng=Random(166)
    for _ in range(100):
        edges=[[(j,b,rng.randrange(5)) for j in range(5) for b in range(2)]
               for _ in range(4)]
        # A finite deterministic keyed function for *correctness* checks only.
        pad={(i,j,b,k):rng.randrange(16) for i in range(4) for j in range(5)
             for b in range(2) for k in range(16)}
        K=[[rng.randrange(16) for j in range(5)]]
        hints=[]
        for i,es in enumerate(edges):
            child=[None]*5;table={}
            for parent,b,v in es:
                z=pad[i,parent,b,K[-1][parent]]
                if child[v] is None:child[v]=z
                else:table[parent,b]=z^child[v]
            indegree_positive=len({v for _,_,v in es})
            assert len(table)==len(es)-indegree_positive
            K.append([rng.randrange(16) if k is None else k for k in child]);hints.append(table)
        for bits in product(range(2),repeat=4):
            s=0;k=K[0][s]
            for i,b in enumerate(bits):
                k=pad[i,s,b,k]^hints[i].get((s,b),0)
                s=edges[i][2*s+b][2]
                assert k==K[i+1][s]
    print('100 designated-parent graphs, all 16 paths and exact issued row counts passed')
if __name__=='__main__':checks();component_test();forest_test()

```
