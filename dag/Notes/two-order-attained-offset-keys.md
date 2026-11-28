---
title: Offset function keys for two trace orders with separable joint reachability
refs: [definition:WE_CircuitSAT_Capped, definition:ReorderedTraceScan, definition:PermutationSignatureTree, definition:OffsetCellKeys, definition:OffsetRectangleGauge, definition:ProjectiveOrderPhase, definition:OffsetRingCellTree]
tags: [witness-encryption, ring-lwe, branching-programs]
---

## Two permutations of one trace

Use 129 source bits (constant and 128 inputs) and three raw bits per gate (two reads and its output). Total 12417. In A order take the sources and then 4096 consecutive triples. Its absorbing reject state and two live states suffice: a first read replaces a live state by that bit, the second replaces it by their NAND, and the output must equal the stored bit. Source bits are ignored by A. In B order take each of the 4225 wires' defining bits followed by every attached read pin. Remember the defining bit, reject unequal pins, and require the constant and terminal definitions to be one. For a forward/self reference attach the read pin to wire zero: the registered evaluator reads true for unavailable wires. Attach both occurrences of a duplicated read. A raw output is both a gate's third bit and the defining bit of its wire, with no extra copy. Both readers inspect each raw bit exactly once. Two dense layered tables of width three have 74502 transition entries each; the variable permutation takes 173838 bits when stored as 12417 fixed 14-bit indices. Computing pin buckets takes O(n+g) RAM operations with arrays and fixed-width indices. Parsing the official unary format costs extra. ReorderedTraceScan proves the local transitions, uniqueness of a valid trace given its primaries and agreement of the final value with evalGates. The executable compiler below supplies both permutations and independently tests forward and duplicate wiring.

The first reader alone has 4^4096 admissible gate tuples. With the 129 source bits last, a prefix cover needs at least that many roots: the last gate's output must be checked. With sources first and without skipping them it needs another factor 2^129. The second domain has 2^4223 raw words from its free wire definitions. Replacing complete GGM boundary seeds by one seed per accepting automaton state is unjustified: different prefixes can hit the same state while carrying different future mask functions. Existing single-prefix transport costs 2^(h−k) common-order roots for k fixed coordinates ending at depth h. Randomizing GGM expansions only hides an antichain of distinct exposed subtrees after every exposed pair has been made incomparable on NO; it does not identify different variable orders. The construction below first computes attainable joint verdicts.

## Exact substitution of ordered intervals

For two large blocks read as UV by A and VU by B, classify u by the state reached in A and the complete subset of B states from which its suffix accepts. Classify v by the analogous suffix acceptance profile for A and the state reached in B. The two verdicts are membership tests in these profiles. There are at most w_A·2^w_B and w_B·2^w_A signatures. Crucially use only attained signatures. Witnesses for an attained u and an attained v combine because the blocks have disjoint coordinates. Computing the individual block signatures still has a cost when the readers differ inside a block.

More generally, take a tree of common intervals of the two leaf orders. Its two children are ordered left-to-right by A and either directly or oppositely by B independently at each node. Store the set of transformation pairs actually achieved by the substring under all settings of its bits, including effects from every possible entry state. At a leaf use the two *paired* bit transitions. Combine each left/right pair by composition in the relevant orders. Every table element is realized by joining two independent child assignments, and every assignment restricts to two such elements. PermutationSignatureTree.mem_iff and both prove these facts. Nesting depth and the number of inversions need not be small. On a supplied tree for a separable permutation this decides all four joint endpoint verdicts at the root. The replay constructs a certificate by merging adjacent intervals in the other order, retaining their orientation. Every successful full merge is independently checkable.

For widths 3 and an absorbing failure state, only 3²=9 unary maps per reader are possible. A node therefore holds at most 81 transformation pairs, independent of height. At 12417 leaves a complete binary certificate uses 12416 joins and tries at most 81,461,376 child-pair combinations. Two nine-by-nine composition tables and a bitset or small list per node suffice. Storing every 81-bit presence bitmap would take 2,011,473 bits excluding indexing and the certificate. At an arity-k common interval one may enumerate the Cartesian product of child tables and compose in the two specified permutations, costing up to 81^k candidates with O(k) composition work each. Applying such a node to the entire permutation is always possible, with exponentially high cost. A cheap binary certificate for every wiring is unproved. For the explicit 4096-gate controls the measured candidate counts are 160492 (YES) and 160264 (NO), with largest tables of 7 and 11 pairs. These counts cover the joins only.

## The two keys and the one-challenge reduction

The dealer must decide whether cell 11 is attainable. For the trace compilers that question is exactly SAT. This is an explicit issuer preprocessing step with the restricted complexity above, not a cheap general-NAND compiler. Define the cell of each raw address x to be its pair of local verdicts (A(x),B(x)). Do not issue any token for 00 or for an unattained cell. A gets the 10 and 11 tokens that exist; B gets the 01 and 11 tokens that exist. Each cell has a canonical seed t and offset d. A token is (t,d); B's corresponding token is (t,d XOR m). Within each cell the common function is H_t(x) XOR d, where H may be any public deterministic keyed evaluator. An accepted address with both roles reads the same seed and obtains exactly m by XOR. OffsetCellKeys.no_view proves full joint equality for independently uniform cell seeds and offsets on disjoint authorized cells. Including the same independent public parameters changes neither proof. A phantom 11 token on NO publishes both corresponding offsets and discloses m immediately.

There is a fixed RingLWE.decision issuer with one expansion. Use the registered N=2048, q=512, m_rows=1, CBD(1) secret and errors. Sample one public ring header a and one private 8192-bit seed s, four independent fair bits per coefficient giving secret and error by the difference-of-bits rule. Compute Y=a·secret(s)+error(s), serialized as 18432 coefficient bits. From Y take two disjoint 8193-bit segments, each a new 8192-bit seed and one offset. Use these tokens for the 10 and 01 cells respectively. Use the *parent seed* and offset zero for 11. Its presence on YES is permitted, and it is absent on every NO. OffsetRingCellTree implements the ring map, bit extraction, child and root issuance, and offset-correct evaluation. Its no_parent lemma states precisely that on NO the published keys require only the challenge body and flags. The 11 test stays indispensable in the honest issuer.

A reduction given an ordinary fixed (a,Y) challenge computes the two segments and the exclusive-cell flags, and can generate every public value on NO without s. Uniform Y gives independent uniform bits conditional on a since coefficient serialization at the power-of-two modulus is bijective. In the ideal law flipping the B-only offset preserves the whole pair of keys; indices, flags and a are the same. Real challenge rows have exactly the prescribed seed law. Consequently message distinguishing gap is at most twice the costed one-challenge distinguishing bound, by two hybrids through the identical ideal view. Alternatively select a fair challenge message and test the attacker's answer against it to get half the message gap. This proof is for the encoded sample laws via the core RingLWE word/ring correspondence; no native testing machine or quantum clock is certified. No new assumption is introduced.

One nonconstant evaluator expands each disclosed cell seed t once with the same public a and computes the binary inner product of its first 12417 coefficient bits with the raw address. B can read the address in its own permutation by indexing coefficients by raw position. This construction uses the public verdict-pair classifier as well as the original local accept test. Evaluating both verdicts can buffer the word and run the second program, or maintain the interval-stack transformations while traversing the certificate. Width three describes the two local checks, not the entire restricted-key evaluator. Selecting the cell before expansion can require a second input pass; alternatively accumulate each candidate inner product in a single pass after expanding its token. A linear evaluator within each cell suffices because the cells themselves constrain which shift is present. Security concerns the entire key description, including every seed.

At most four transmitted tokens and the ring header take 51204 raw bits and three optional-cell flags give 51207. NO has at most two tokens and 34821 bits including flags. These figures assume programs, public statement and the chosen parsing/order convention are shared; otherwise charge their encodings as well. A naive ring product visits 2048² coefficient pairs, with ternary multiply-adds. Issuance uses one product in addition to reachability preprocessing; one selected token uses one more product for its inner-product mask. The plain random-token construction already gives exact hiding at the same structural boundary. The lattice construction replaces independent random cell tokens by a single parent with a challenge simulation, without improving the arbitrary-circuit SAT decision cost. None of these RAM/size estimates prove the combined registered cost.

## Failure of separable masks and a checked repair

On two-block signature cells form a bipartite graph. A row mask l_u and column mask r_v give the canonical table l_u+r_v+role·m on each authorized edge. Extending by a fresh pair pad z_uv on marked pairs gives a linear image. OffsetRectangleGauge.coset proves that the entire table distributions agree exactly when the role vector is in that image. With only vertex pads this requires even signed role sum on every cycle. A 2-by-2 rectangle with three A edges and one B edge violates this condition even though the languages are disjoint: four authorized evaluations recover m with certainty. Both languages admit opposite order scans of width at most three. Choose a spanning forest of the attained-pair graph, set vertex potentials to fit role values along forest edges and mark the remaining edges, or only those chords whose values disagree. The feedback lemma constructs the correcting pair pads. There are at most |E|−|V|+#components chords. On NO, a pair has only one role so the color function is well-defined. On YES a pair-specific pad is shared between the two roles, preserving offset correctness. The replay enumerates the two complete laws and the one-pad repair. Clear seeds or auxiliary fields correlated with these pads would require their own joint analysis.

For a proposed projectively commuting family, ProjectiveOrderPhase proves explicitly that moving Heisenberg factors (x_i,y_i,z_i) changes only the central coordinate by the difference of the two pair sums, with pair sum Σ_{i<j} x_i y_j. One adjacent swap contributes x_i y_j−x_j y_i. Reading a public commutator table can correct the phase at witness-dependent cost up to one lookup and field addition per inversion; a binary-input table can require four values per inversion. If every factor is selected only by its own raw bit, the final center is a degree-at-most-two function over F₂. A correction of the same form stays in that family. The existing five-gate quadratic moment parity test therefore survives either order on that family; a mere ability to compute a phase difference does not prove a full-key simulation. State-dependent factors or nonlinear readout lie outside that degree conclusion. The attained-cell construction supplies a separate tested escape.

## Executable replay

The first registered fixture is a chain of double-parent gates, with reversed pin order in each wire group. The last gate in its NO sibling addresses its own unavailable wire twice. This moves the final pair to the constant group near the front, inducing a large interval swap. Both orders consume identical raw bits.

```python
from itertools import product
from collections import Counter
# 2 is absorbing reject. Each live-state map has one of nine encodings.
def tmap(f):
    return 3*f(0)+f(1)
def at(t,i):
    return (t//3,t%3,2)[i]
ident=tmap(lambda i:i)
def tab(f):
    return tuple(tmap(lambda s:f(s,b)) for b in (0,1))
reset=tab(lambda s,b:b)
nand=tab(lambda s,b:1-(s&b))
check=tab(lambda s,b:s if s==b else 2)
pin=tab(lambda s,b:1 if b else 2)
keep=(ident,ident)
compose=[[tmap(lambda s:at(v,at(u,s))) for v in range(9)] for u in range(9)]

def compile_trace(n,gates):
    assert n>=1 and gates
    G=len(gates)
    order=[0]+list(range(2,n+1))+[1]+list(range(n+1,n+1+G))
    primary=list(range(n+1))+[n+3+3*i for i in range(G)]
    pins=[[] for _ in primary]
    A=[(primary[w],keep) for w in order if w<=n]
    for i,(l,r) in enumerate(gates):
        left=n+1+3*i
        for j,w in enumerate((l,r)):
            assert w>=0
            pins[w if w<n+1+i else 0].append(left+j)
        A.extend(zip(range(left,left+3),(reset,nand,check)))
    B=[]
    for w in order:
        B.append((primary[w],pin if w in (0,len(primary)-1) else reset))
        B.extend((i,check) for i in reversed(pins[w]))
    assert sorted(i for i,_ in A)==sorted(i for i,_ in B)==list(range(n+1+3*G))
    return A,B

def scan(program,word):
    s=1
    for i,t in program:
        s=at(t[word[i]],s)
    return s!=2

def expected(n,gates,x):
    ws=[1]+list(x); word=ws.copy()
    for l,r in gates:
        a,b=(ws[w] if w<len(ws) else 1 for w in (l,r))
        z=1-(a&b); word.extend((a,b,z)); ws.append(z)
    return tuple(word),bool(ws[-1])

def attainable(A,B):
    # A certificate is each successful merge of two adjacent intervals in B.
    where={i:(j,t) for j,(i,t) in enumerate(B)}
    stack=[]; candidates=0; largest=0; merges=0
    for i,ta in A:
        j,tb=where[i]
        stack.append((j,j+1,{(ta[b],tb[b]) for b in (0,1)}))
        while len(stack)>=2:
            l,h,x=stack[-2]; L,H,y=stack[-1]
            if h!=L and H!=l: break
            swap=H==l
            candidates+=len(x)*len(y); merges+=1
            z={(compose[a][c],compose[d][b] if swap else compose[b][d])
               for a,b in x for c,d in y}
            largest=max(largest,len(z))
            stack[-2:]=[(min(l,L),max(h,H),z)]
    if len(stack)!=1: return None
    cells={(at(a,1)!=2,at(b,1)!=2) for a,b in stack[0][2]}
    return cells,(candidates,largest,merges)

def check_tiny():
    for gates in ([(0,0)],[(1,1),(2,2)],[(2,2),(3,3)],[(1,0),(1,2)]):
        A,B=compile_trace(1,gates)
        legal={expected(1,gates,(x,))[0] for x in (0,1) if expected(1,gates,(x,))[1]}
        words=list(product((0,1),repeat=len(A)))
        assert {x for x in words if scan(A,x) and scan(B,x)}==legal
        dp=attainable(A,B)
        if dp: assert dp[0]=={(scan(A,x),scan(B,x)) for x in words}

def check_full():
    n=128
    g=[(1,1)]+[(n+i,n+i) for i in range(1,4096)]
    for yes in (True,False):
        if not yes: g[-1]=(4224,4224)   # both forward reads become the constant
        A,B=compile_trace(n,g)
        cells,stats=attainable(A,B)
        assert ((True,True) in cells)==yes
        for val in (0,1):
            word,answer=expected(n,g,[val]*n)
            assert scan(A,word) and scan(B,word)==answer
        print(yes,cells,stats)

def rectangle():
    def law(h,patch):
        out=Counter()
        for l0,l1,r0,r1,z in product((0,1),repeat=5):
            out[(l0^r0,l0^r1,l1^r0,l1^r1^(z if patch else 0)^h)]+=1
        return out
    assert set(law(0,False)).isdisjoint(law(1,False))
    assert law(0,True)==law(1,True)

check_tiny(); check_full(); rectangle()
```
