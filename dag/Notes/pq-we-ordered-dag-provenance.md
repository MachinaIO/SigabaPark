---
title: Ordered two-key garbling of the registered NAND DAG and provenance of ideal target hits
refs: [definition:WE_CircuitSAT_Capped, definition:OrderedNand, theorem:AdvancedEncryption.WE.OrderedIdeal.target_witness, theorem:AdvancedEncryption.WE.OrderedIdeal.issued_valid, theorem:AdvancedEncryption.WE.OrderedIdeal.full_fold, theorem:AdvancedEncryption.WE.OrderedIdeal.row_exact, theorem:AdvancedEncryption.WE.OrderedIdeal.log_sound, theorem:AdvancedEncryption.WE.OrderedIdeal.clean_extends]
tags: [witness-encryption, ideal-cipher, garbling, finite-security]
---

For the registered circuit language, garble each declared gate once. The terminal accepting-label hit in the **classical typed ideal experiment specified here**, outside an explicit guessing/collision event, implies that a total witness exists. This result permits unbounded fanout and pooling handles across different attempted evaluations within the same packet. It does not rely on an observer choosing one fixed witness before seeing the packet.

### Row compiler

Key index 0 is a fresh dummy, 1 is the separate true-constant key. Wire w≥1 has two fresh independent key values named by indices 2w and 2w+1. Numerical ordering is on public indices, never on the actual random secret strings. For n inputs, gate h=0,…,s−1 writes d=n+1+h. Replace every operand index ≥d by zero, including a self-reference. This agrees with the registered getD default true. Sort the resulting two indices. Distinct l<r issue a row for each available color a,b with ordered input indices (label(l,a),label(r,b)) and target label(d,NAND(a,b)); zero has only true available. Equal l=r issues (dummy,label(l,a)) to label(d,NOT a), including (dummy,true-constant) when l=0. Every physical tuple is strictly increasing and contains two distinct names. Swapping the raw input order also swaps its color coordinates; NAND is symmetric. Neither gate cloning nor reassignment of a shared gate's labels is involved. Input keys for both values of the same Boolean variable have conflicting singleton tags. Neutral dummy and constant may have separate singleton tags, in conflict with nothing. Internal keys have no initial handles. Only primary opposite symbols conflict.

The full_fold theorem proves equality of the complete List.foldl estep state with the actual Sigaba evaluator for every gate list, every input and initial result bit, including empty lists. It covers normalization and sorting across all shared gates, not just the final bit. For any wire valuation with the proper constant, the eligible physical rows at a sorted gate yield exactly its semantic NAND output; this is row_exact. For a fixed witness, issue its selected input handles, with both alternatives available in the challenge. Select rows using the public clear Boolean gate evaluation; cached values of already-computed gate handles can be reused. Inductively the union contains only variables agreeing with this witness. Each of the s ideal calls returns the actual successor key internally, with the corresponding handle available to the evaluator. The final color is the last gate's registered output. These are model-level row correctness and provenance statements, before cycle-test correctness or noise considerations.

### Precisely specified ideal experiment

Let the key and block domain be D=2^ℓ distinct strings, and use one independent ideal permutation of this domain for each ordered pair of key strings. Both direct forward and inverse calls are classical. The public compiler determines R triples of key indices. Generate ρ independent uniform protected key strings and an independent raw AFHE decryption credential. Precompute each row cipher under its ordered pair on its output key with the one shared permutation family, reusing existing records exactly. The random accepting output key is the unlock in the zero-message starting hybrid. Publish the row ciphertexts, index specification, known tags on initial handles and otherwise independent public information. The revised ideal model has no unmodeled evaluation-key leak. Raw protected strings and the credential are secret.

A handle is a typed public pair (tag union, fresh η-bit identifier) indexed in a table containing the hidden plaintext. Sample handle identifiers with replacement and abort if one repeats. Reject unknown identifiers and tag mismatches before access. Initial handles contain the dummy/constant and both colors of every primary input. An arbitrary public encryption request creates a handle to the caller's chosen plaintext under any supplied subset of the 2n+2 public tags. A decryption request under an incorrect raw credential returns failure. An Eval request resolves exactly two ordered handles and a block. On an exact cache hit return its recorded typed handle without a new SKE call. On a miss, if their tag union contains a forbidden pair, use two freshly uniform independent ℓ-bit keys for this inverse call. Otherwise use the resolved plaintext keys in port order. Call the same permutation inverse on the supplied block and store its result behind a fresh handle carrying the entire union. Log both direct and actual internal cipher calls. Any fixed extra public evaluation data in this specification must be simulable independently of the protected key values. A public CycleTest or a real evaluation key correlated with them is not inserted by fiat.

### Good-event invariant

Call a plaintext protected if it equals one of the generated wire, dummy or constant keys. On the good transcript below, a raw direct call and a public Enc cannot introduce a protected plaintext even when the caller adaptively chooses its tag set. An inverse at an unprogrammed (key tuple,block) yields a fresh unprotected plaintext unless it repeats a nonchallenge table entry. A repeated such record still has unprotected output: a direct forward call programmed it with a known unprotected plaintext, or a prior nonchallenge inverse created it. A conflicting fresh tuple does not contain a protected key. A public call can name a previous row ciphertext under a different tuple; classify by the **actual inverse record**, not by its advertised row position. If it is a precomputed record, outside collisions, both resolved plaintexts are precisely its ordered parent labels. The input handles already precede this query. Different physical inverses producing the same child key give different valid derivations. Enc and unregistered rows can leave unprotected records useful in later queries, but neither can create a new protected leaf on this event.

Thus every protected returned handle projects to a derivation using initial tagged labels and the compiler's rows. This is induction on the adaptive chronological log, without a tree-unrolling cost. A cached byte tuple restores the same derivation. Occurrences with distinct byte tuples can attach different supports to the same wire label. In each individual derivation every total assignment extending the support gives the claimed wire value: base variables fix their color, dummy/constant impose no variable, and a union extension restricts to each parent, so row_exact gives the child. Extra tags can only shrink the extension set. The generic induction is log_sound. Any clean support extends to a Boolean assignment (clean_extends): set i true iff its positive tag occurs, and false elsewhere. Therefore any precomputed inverse hit whose target is the true final output gives an actual satisfying witness, by applying the invariant to the union of its actual clean input tags. For a NO statement, **all** such inverse hits are excluded together on the good event. The instrumented challenger identifies the hit by its actual secret-key record. Once identified, its two input tag bitsets already give the witness: scan their union once, output 1 exactly where the positive tag occurs, and set unspecified positions to 0. No recursive expansion of the logged proof DAG is necessary. Identifying an arbitrary target hit from an unaided public view is not claimed. A direct forward query mentioning unlock is separately a raw protected-string guess. No per-target independence is needed.

The issued_valid proof connects the chronological invariant to the final *registered* list of wire values: every fold extension appends its new gate value and preserves all earlier reads, including wire zero. The target_witness theorem combines these results. From any clean derivation of the accepting last label in a nonempty gate list it produces a function Fin n → Bool on which the actual SigabaNeo.evalGates returns true. The registered 4,096-gate lists are nonempty, and their final gate decomposes them as a prefix followed by that gate. These proofs are Lean results about the derivation relation; the mapping from the probabilistic log into that relation is the good-event argument above.

The good-event supports can also be characterized exactly. Ignore the two neutral tags temporarily. Let C(w) contain all primary variables in the backward cone of the normalized wire w. A literal depends only on itself, zero and dummy depend on none, and each gate takes the union of both input cones. Because every issued row opens *both* its operands, an actual clean derivation for label (w,b) has precisely one sign for every variable in C(w), no sign outside it, and evaluates w to b. This stronger equality concerns actual successful projected records, not the optional widening constructor of the conservative lemma. Conversely assign any values on C(w), extend them arbitrarily and follow the honest gates to produce exactly that restriction with the correct color. The neutral constant tag occurs precisely when the structural cone reads zero; the dummy tag occurs precisely when a normalized gate in the cone has identical inputs. This also accounts for duplicate zero. Thus the number of attainable clean supports of a given color equals the number of such assignments on its cone, potentially 2^128. These are mathematical witnesses; the issuer and decoder do not enumerate them. An additional check compared the entire set of signed/neutral supports in all 875 circuits, not just existential acceptance.

### A finite bad-event ledger

Let q bound the total number of the observer's classical calls, counting one internal inverse at each Eval cache miss in addition to the outer call when budgeting q. Use B=4ρ+4R+12q+16 as a deliberately loose count of exposed/reserved ℓ-bit words, and H=2n+2+q as a bound on fresh handle identifiers. If B≥D use the trivial bound 1. Otherwise an upper bound on the total probability of the exceptional event is

    min(1, 2 B²/(D−B) + H(H−1)/2^(η+1)).

One proof uses a symbolic lazy table up to the first exception. Reserve distinct hidden names for all protected keys and the raw credential; collisions in their independent original draws are charged. Program each challenge forward answer as a fresh uniform unused image for its tuple, retaining identical forward records. Public row words are sampled independently of the numeric hidden names conditional on the equalities already fixed. It is harmless to declare a further exception if a fresh permutation image or a fresh junk inverse preimage hits one of the reserved hidden values. For each fresh random field word there are at most B prior forbidden choices and at least D−B allowable values after that permutation's used side has been excluded. For each new adversary-chosen raw key coordinate, Enc plaintext, direct cipher message, or credential guess, the still-unused hidden names are exchangeable conditional on the good symbolic history; at most B hidden values occupy at least D−B unused positions. Known repeated attacker literals are not required to be fresh. Reveal only the actual public outputs, using symbolic table indices for unexposed plaintexts. Conflict keys count as fresh word draws. Each query consumes at most two key-coordinate guesses, a data guess, two replacement draws and the lazy cipher value; precomputation uses at most ρ+1 hidden words and R fresh answers. B covers these operations and the resulting exclusions. A union bound charging both categories gives the stated 2B²/(D−B). Independent handle draws contribute the last birthday term, even when tags are public. This is an elementary classical hidden-name bound for this stated lazy-permutation game. It does not establish quantum random-oracle or coherent-query security. In particular conditioning on no exceptions in the future would not justify fresh-key probabilities.

### A limited ideal terminal tester

The construction can close its terminal step in a larger *explicitly ideal* model. Sample another independent uniform secret token L and expose a tester that accepts a resolved handle precisely when its hidden plaintext equals L; malformed handles return zero. It reveals no other information and the raw decryption credential is sampled separately. In the message-one world use L as the final accepting wire label. In the message-zero world keep that label independent of L. Nature samples the same uniform wire-label table in both coupled worlds; let the testers' secrets be its accepting label or a fresh independent token, respectively. Increase B by four for this token and its reserved positions, and include all tester calls in q. Until a collision, guess, or accepting-label handle exists, both testers return false on every request. In a NO instance the provenance theorem excludes the last alternative on the good event. Both transcripts can therefore be coupled identically up to the bad probability; the sum of the two displayed bad-event bounds suffices. On a valid accepting witness the message-one tester returns true (barring handle corruption); the independent message-zero token matches the obtained label with probability 2^(-ℓ) before handle errors. This is a full YES/NO decoding interface for the stated ideal functionalities. It supplies neither a real public tester for F(sk) nor a falsifiable implementation of the handle engine.

For illustration, q≤2^64 total classical calls, R≤16,384, ρ=8,450 and η=ℓ=272 give a per-world bound below 2^(-134), including the extra token. The two-world ideal gap is below 2^(-133). This measures only the specified classical ideal transcript; there is no physical implementation of a uniform random permutation oracle here.

### Scope and cost

For n=128,s=4096 the issuer has 8,450 private label indices and 258 initial handles. There are at most 16,384 rows and at most three target rows into the accepting final key. Honest decoding makes 4,096 nominal two-parent evaluations and needs at most 4,354 handles including initial alternatives. Enc calls the ideal permutation at most 16,384 times. If written explicitly the raw blocks cost at most 16,384ℓ bits, and a fixed-width triple specification another 16,384·3·14=688,128 bits; it can instead be regenerated from the public statement with a charged parser. Using a 258-bit tag bitset and η-bit identifier costs 258(η+258) bits for the initial typed records, plus framing. A full evaluator's bounded internal table, return handles and four gate-row trials if a decoder does not first compute the colors must be counted for that interface. At ℓ=η=272 the raw rows plus initial records cost at most 4,593,188 bits; explicitly carrying the triple indices brings this to 5,281,316 bits. The 8,450 random key strings are 2,298,400 bits of internal sampling before the tester or credential. These field counts omit the real AFHE ciphertext expansion, key material, evaluation and cycle-test costs, and both machine descriptions.

[Kluczniak, Definition 12 and Theorem 3](https://eprint.iacr.org/2020/1502) describe per-target exact SKE query events, ideal table calls and a formula-based construction; Theorem 3 explicitly counts internal Eval calls. Our strictly ordered distinct-index compiler removes the repeated-key and ordering coverage issue at the syntax level. The accepting label as a shared DAG vertex, typed public metadata, resolution/rejection conventions, transfer to the real target-hit probabilities, and honest secret-dependent terminal cycle test need their own justification. In particular the printed one-sided expression has ideal minus real; a real upper bound needs the opposite direction or a two-sided guarantee. A bound for individual inverse targets alone does not automatically control arbitrary forward unlock mentions. One would also have to justify replacing the independent unlock by F(sk), as required by the message-one world, in the entire real transcript including the cycle tester. No fixed real distribution in the existing WE registry has been shown to implement this interface. We introduce no new hardness premise and claim no QPT or registered real-WE cost bound.

The accompanying deterministic replay tests every one of the 625 two-input two-gate registered circuits, 250 four-input DAGs including invalid-forward references, and the full-cap row ledger. For every wire and every test witness it compares the set of extendible clean symbolic supports with the registered evaluator. These exhaustive small instances check the compiler implementation; the general chronological argument is separate.

```python
"""Symbolic successful target-hit closure for registered NAND circuits on the no-collision event."""
from itertools import product
from random import Random
def compile_rows(n,gates):
    # symbol for dummy, constant true, then contiguous wire/value label pairs.
    dummy=0; const=1
    def options(w):
        if w==0:return [(const,1)]
        return [(2*w+b,b) for b in range(2)]
    rows=[]
    for j,(i,k) in enumerate(gates):
        dest=n+1+j
        i,k=sorted(w if w<dest else 0 for w in (i,k))
        if i==k: inputs=[(dummy,label,1^b) for label,b in options(i)]
        else: inputs=[(a,c,1^(b&d)) for a,b in options(i) for c,d in options(k)]
        for a,c,b in inputs:
            assert a<c
            rows.append((a,c,2*dest+b))
    return rows
def check(n,gates):
    rows=compile_rows(n,gates)
    prov={0:{(0,0)},1:{(0,0)}}
    for i in range(n):
        for b in (0,1):
            m=1<<i
            prov[2*(i+1)+b]={(m,b*m)}
    for a,b,c in rows:
        for m,x in prov.get(a,()):
            for v,y in prov.get(b,()):
                if (x^y)&m&v==0:prov.setdefault(c,set()).add((m|v,x|y))
    for wit in range(1<<n):
        val=[1]+[(wit>>i)&1 for i in range(n)]
        for i,k in gates:
            val.append(1^((val[i] if i<len(val) else 1)&(val[k] if k<len(val) else 1)))
        for j in range(n+1,len(val)):
            for b in (0,1):
                assert any(wit&m==x for m,x in prov.get(2*j+b,()))==(val[j]==b)
if __name__=='__main__':
    n=2;s=2
    pairs=list(product(range(n+1+s),repeat=2))
    for gs in product(pairs,repeat=s):check(n,gs)
    rng=Random(175)
    for _ in range(250):
        gs=[(rng.randrange(12),rng.randrange(12)) for _ in range(7)]
        check(4,gs)
    full=[(1+j%128,1+(j+1)%128) for j in range(4096)]
    print(len(pairs)**s,'exhaustive registered two-gate circuits;',250,'four-input circuits; full dictionary rows',len(compile_rows(128,full)))
```

Extend the preceding listing with this exact-support check and call it on the same circuits.

```python
def exact_cones(n,gates):
    rows=compile_rows(n,gates)
    P={0:{(0,0,1)},1:{(0,0,2)}}
    cones=[0]+[1<<i for i in range(n)]
    neutral=[2]+[0]*n
    for i in range(n):
        for b in (0,1):P[2*(i+1)+b]={(1<<i,b<<i,0)}
    for i,k in gates:
        i,k=(u if u<len(cones) else 0 for u in (i,k))
        cones.append(cones[i]|cones[k]);neutral.append(neutral[i]|neutral[k]|int(i==k))
    for p,q,y in rows:
        for m,x,u in P.get(p,()):
            for r,z,v in P.get(q,()):
                if not ((x^z)&m&r):P.setdefault(y,set()).add((m|r,x|z,u|v))
    expected={}
    for a in range(1<<n):
        bits=[1]+[(a>>i)&1 for i in range(n)]
        for i,k in gates:
            v=1^((bits[i] if i<len(bits) else 1)&(bits[k] if k<len(bits) else 1))
            t=len(bits);bits.append(v)
            expected.setdefault(2*t+v,set()).add((cones[t],a&cones[t],neutral[t]))
    for t in range(n+1,len(cones)):
        for b in (0,1):assert P.get(2*t+b,set())==expected.get(2*t+b,set())
```

A separate adaptive replay below uses actual lazy forward/inverse permutation tables and 64-bit toy identifiers. It projects out the two harmless neutral bits, already checked by exact_cones. On 120 generated circuits it checked 1,472 recognized inverses, 22,064 unrecognized inverses and 11,880 cached calls. The calls included 18,528 conflict substitutions, 4,800 fresh chosen-tag records and 1,920 malformed tag rejections. Seed the circuit generator with Random(177), use n=2+i%3 and s=3+i%7, choose both raw indices uniformly in range(n+s+1), and pass seed=1200+i for i=0,…,119. The assertions run on the sampled good histories, not a proof about all random permutations.

```python
def adaptive(n,gates,seed):
    from collections import defaultdict,Counter
    rng=Random(seed)
    rnd=lambda:rng.getrandbits(64)
    N=2*(1+n+len(gates));keys=[rnd() for _ in range(N)]
    assert len(set(keys))==N
    protected={k:i for i,k in enumerate(keys)}
    fw,bw=defaultdict(dict),defaultdict(dict)
    header,cache,entries,objects={}, {}, {},[]
    counted=Counter()
    def perm(pair,word,invert=False):
        x,y=(bw[pair],fw[pair]) if invert else (fw[pair],bw[pair])
        if word not in x:
            ans=rnd()
            while ans in y:ans=rnd()
            x[word]=ans;y[ans]=word
        return x[word]
    def create(t,k):
        h=rnd();assert h not in entries
        entries[h]=(t,k);obj=(t,h);objects.append(obj);return obj
    constants={0:create(0,keys[0]),1:create(0,keys[1])}
    starts={2*(i+1)+b:create(1<<(2*i+b),keys[2*(i+1)+b]) for i in range(n) for b in (0,1)}
    for a,b,y in compile_rows(n,gates):
        pair=(keys[a],keys[b]);c=perm(pair,keys[y])
        header[a,b,y]=c
    allowed={(keys[a],keys[b],c):y for (a,b,y),c in header.items()}
    def value(x):
        v=[1]+[(x>>i)&1 for i in range(n)]
        for i,j in gates:v.append(1^((v[i] if i<len(v) else 1)&(v[j] if j<len(v) else 1)))
        return v
    vals=[value(x) for x in range(1<<n)]
    cones=[0]+[1<<i for i in range(n)]
    for i,j in gates:cones.append((cones[i] if i<len(cones) else 0)|(cones[j] if j<len(cones) else 0))
    def evaluate(p,q,c):
        for t,h in (p,q):
            if h not in entries or entries[h][0]!=t:counted['rejected']+=1;return None
        req=p,q,c
        if req in cache:counted['cached']+=1;return cache[req]
        tags=p[0]|q[0]
        tainted=any((tags>>(2*i))&3==3 for i in range(n))
        pair=(rnd(),rnd()) if tainted else (entries[p[1]][1],entries[q[1]][1])
        k=perm(pair,c,True);record=(*pair,c)
        counted['conflict' if tainted else 'clean']+=1
        if k in protected:
            id=protected[k];assert not tainted and allowed[record]==id
            cone=sum(1<<i for i in range(n) if (tags>>(2*i))&3)
            bits=sum(1<<i for i in range(n) if (tags>>(2*i+1))&1)
            assert cone==cones[id//2]
            assert all(v[id//2]==id%2 for x,v in enumerate(vals) if x&cone==bits)
            counted['recognized']+=1
        else:counted['unrecognized']+=1
        cache[req]=create(tags,k);return cache[req]
    for x,vs in enumerate(vals):
        handles={**constants,**{i:h for i,h in starts.items() if vs[i//2]==i%2}}
        for j,(i,k) in enumerate(gates):
            d=n+j+1;i,k=sorted(u if u<d else 0 for u in (i,k))
            label=lambda u:1 if not u else 2*u+vs[u]
            a,b=(0,label(i)) if i==k else (label(i),label(k));y=2*d+vs[d]
            req=handles[a],handles[b],header[a,b,y];h=evaluate(*req)
            assert entries[h[1]][1]==keys[y] and evaluate(*req)==h
            handles[y]=h
    cts=list(header.values())
    for j in range(200):
        a=rng.choice(objects);b=rng.choice(objects);c=rng.choice(cts)
        if j%5==0:
            v=rnd();assert v not in protected
            b=create(rng.randrange(1<<(2*n)),v);counted['fresh']+=1
        if j%13==0:a=(a[0]^1,a[1])
        evaluate(a,b,c)
    return counted
```
