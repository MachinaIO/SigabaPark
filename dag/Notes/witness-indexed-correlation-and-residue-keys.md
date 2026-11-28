---
title: Witness-indexed OLE views and collusion-safe polynomial remainder keys
refs: [definition:WE_CircuitSAT_Capped, definition:LocalOLEProjection, theorem:LocalOLEProjection.fullKeyFiber]
tags: [design, witness-encryption, correlation, finite-field]
---

## Required view

Let A and B be the two public readers on the same raw address set D. Sample a uniform field function c on D. Give the entire first table c and the second table i ↦ c(i)+β·A(i) on B. For a NO statement, couple the two messages by the very same c: the complete tables coincide coordinate by coordinate. At a common address the difference equals β. The Lean definitions idealView, disjointView and witnessView prove these facts even for fixed c. The equality survives every further operation on those tables, including coherent evaluation. A ciphertext that contains algorithms for the tables also exposes their implementations. Its two code strings require a separate distribution argument.

For the two width-three trace readers on 129 source positions and three positions per NAND gate, |D|=2^12417. The honest witness contains 128 bits. Replacing D by the 128-bit input space still leaves a lookup table with at least 2^128 bits. The compiler based on attained joint signatures evaluates the root accepting cell during issuance. The constructions below use public coordinate maps without testing the joint accepting cell.

## What the two PCF papers expose

Hasler and Reisert, Definition 2 and Figure 1 (p. 10), distinguish two games. One supplies a paired-output oracle with no keys. The other supplies one private key and an oracle for the opposite output, compared to cached reverse sampling. Definition 4 (p. 11) *does* compare both keys under ordinary generation and generation from fresh independent uniform programming seeds. Its seed-security clause gives one key. Theorem 3 reuses a seed to synchronize a party's input across instances. Definition 6 uses regular sparse matrices and noise. Definitions 7 and 8 concern a single FSS key with permitted leakage and a single party's output vector, respectively. Section 4.1, Theorem 2 and Figures 4–5 use levelwise sparse LPN, FSS and final-product DMPF pseudorandom outputs, with random-oracle rows. The keys contain initial vectors, tensor shares, sparse errors and FSS keys. Evaluation expands those rows and outputs a random input and product share. Table 2, at λ=112, L=3, conservative sparsity and ρ=40, reports 1.62 GiB per party optimized and an estimated 10.72 ms/OLE without precomputation; this level has roughly 2^29.5 input positions. [Authors' manuscript, ePrint 2025/2002, Definitions 2–8, §4.1 and Table 2](https://opencryptology.org/2025/2002.pdf).

Braun et al., Definitions 9–10 and Figures 1–2 (pp. 13–15), use a subfield input u, masks v,w and an extension-field multiplier Δ with w−v=uΔ. Key 1 contains Δ in its initial VOLE share. Key 0 contains the initial sender share, sparse errors and DMPF keys. Theorem 1 bounds classical oracle queries and assumes random oracles, levelwise sparse LPN (including its last-level noise law), and DMPF security with pseudorandom outputs. [Authors' revised manuscript, ePrint 2025/1644, January 2026](https://opencryptology.org/2025/1644.pdf).

Setting Δ=β and releasing key 1 exposes β immediately, even if B is empty. A public wrapper that tests B while retaining the original unrestricted key permits a reader to bypass the test. Over a field, suppose a correction d(i)=A(i)−u(i) changes w to w+Δd(i). Both unrestricted corrected outputs now differ by ΔA(i). At a known address in A outside B that difference discloses Δ on a NO instance. Sending all corrections for one bit per raw address takes 2^12417 bits. A succinct code for d still needs a proof for its bytes together with all other bytes. The two-key clause for uniformly programmed seeds compares two ways to generate the *same random-input ensemble*. It does not authorize fixing a seed for a designated circuit function, setting an OLE input to an arbitrary truth table or publishing two derived restricted descriptions conditioned on a hidden bit.

An auditor given classically sampled public strings can implement reversible local evaluation, inspect arbitrary substrings and compute off-domain. A classical query bound on the two paper games does not establish that experiment even against classical auditors; there is also no automatic superposition-query or QROM conclusion. No sparse-LPN premise is used in the construction below. The registered CircuitSAT array comprises LWE, Ring-LWE, Module-LWE and circular Ring-LWE. Neither report is assigned a registered strength here.

## Separate local normalization and simultaneous clear keys

Work over K=GF(2^e), q=2^e, in a fixed field basis; payloads use the distinct elements 0 and 1. Initially assume a public surjection t:D→K and two tests f(t(x))=0 and g(t(x))=0. Let F and G be the respective monic gcds with T=X^q−X. Each side is normalized separately, using repeated modular squaring and a local Euclidean algorithm. No joint gcd, cross-domain comparison or root search occurs during issuance. Nonzero constants give modulus 1, repeated factors give simple roots and a zero polynomial gives T itself. T has exactly one linear factor per field element, so disjoint address languages imply coprime F and G. For an exact nonempty smaller attainable image S one can use the common squarefree split polynomial ∏_{z∈S}(X−z) in place of T, provided its public construction and size are paid for.

Write d_A=deg F, d_B=deg G, D'=d_A+d_B. Sample D' independent uniform field coefficients of P in degrees 0 through D'−1. Emit the fixed-length canonical coefficients

    U = P mod F                 V = (P + β) mod G.

There are D'e random bits and D'e key bits beyond public metadata. A degree-zero residue occupies zero slots. At a common root z, V(z)−U(z)=β. On NO, K[X]/(FG) maps bijectively to K[X]/F × K[X]/G. Adding β to the second component remains a bijection. Therefore each complete pair of byte strings in the canonical encoding has exactly one generating P, for each message. This includes readers evaluating outside either root set. LocalOLEProjection.fullKeyFiber counts the entire nonce fiber for comaximal ideals of any commutative ring. The polynomial sampler uses monicity to identify the product quotient with exactly D' coefficients. No computational hybrid or quantum hardness premise is needed.

To give the required offset *functionality* on arbitrary addresses, define the first program to return U(t(x)) on A, V(t(x)) on B outside A, and zero elsewhere. The restricted second program returns V(t(x)) on B. The branch predicates and both keys are public. Their difference on B is exactly βA. The baseline is indexed by a label and can repeat at different addresses. Its full table can be distinguished from a uniformly random function. Perfect NO equality concerns the actual public key bytes, which suffices for the stated privacy property. This example implements the offset relation while the large-domain PCF idealization remains separate.

The issuer can stream P from highest to lowest degree, multiplying each remainder by X, adding the next coefficient and reducing once by the corresponding monic modulus. The second accumulator receives β after the last digit. This costs O(D'²) field operations, O(D') working field elements, and a single pass over the random coefficients. Horner evaluation costs at most D' field multiplications and additions in one sequential pass across both key fields once z is known. A two-pass witness implementation can first stream the checksum and then read the key. For a nonzero input polynomial of degree h, computing T mod it takes e squarings and a subtraction, then one gcd. Schoolbook polynomial arithmetic gives O((e+1)h²) field operations using ordinary Euclidean division with decreasing degrees. The zero-input branch has degree q when T is used. These figures count field operations and raw bits; there is no registered time/description-length certificate.

For an explicit pair of two-order readers on n=12417 bits, sum bits times public GF(4) weights whose first two weights are independent over GF(2). Addition is commutative. One reader can traverse the address forward, the other backward, with width four and externally specified layer weights. Choose nonzero weights throughout and repeat a fixed pattern to generate them without storing a permutation. For the NO fixture A={0,1}, B={2,3}, each language contains half of all addresses. With XOR addition, two bits per coefficient and field polynomial a²+a+1, the replay encodes F=0x14, G=0x15. With P=0x72 the serialized byte U|(V<<4) is 0xca for β=0 and 0xda for β=1. Over all 256 masks each byte has both message laws exactly once. Changing B to {1,3} yields 0x5a and 0x4a for the same P, and any address with label 1 decodes. Both checkers cost n field additions or fewer per witness and four field coefficients per header pair. Address translation does not require one GGM prefix tree consistent with both reads.

## Distinct local summaries and exact gluing

The readers can use genuinely different linear maps rather than merely permuting the same weighted scan. Let M_A,M_B be full-row-rank binary maps on the common witness. Their predicates can be arbitrary explicit functions of the respective local syndromes. Choose a basis H for row(M_A)∩row(M_B), of dimension h, and full-rank maps J_A,J_B with H=J_A M_A=J_B M_B. For each side, project only its own accepted syndromes through its J and form a squarefree product over the resulting labels. Embed the h-bit labels injectively in a fixed field; h=0 needs just one label. Empty sets yield modulus 1. Every pair of syndromes with matching projected label occurs on a single witness: the image of the stacked matrix lies in this matching space and both dimensions equal rank(M_A)+rank(M_B)−h. This proves sufficiency for NO coprimality. To decode on a genuine witness the proof uses its own common label, without recovering any compatible representatives.

The local predicates may read variables in arbitrary orders, since XOR columns commute, and they may depend on private syndrome bits. With k_A,k_B rows, one direct preprocessing bound is O(n(k_A+k_B)²) binary operations for the linear algebra plus enumeration of 2^k_A and 2^k_B local syndromes, with the actual predicate and projection costs for each. Product formation by successive linear factors costs O(d_A²+d_B²) field operations. No pair of local predicate outcomes is tested during issuance. If k_A or k_B is large and the root product has no concise source, this bound is exponential. A smaller syntax is needed to cover the general NAND and wire-equality readers. The executable fixture tests all 256 pairs of nonlinear truth masks on two different rank-two syndromes with one shared parity, including all attainable and unattainable pairs.

## One quotient header and guarded NAND circuits

There is a direct issuer for public local constraints f₁,…,f_m over the second root set. In S=K[X]/G sample independent uniform U_j, then publish the canonical coefficient vector of H=β+Σ_j f_j U_j. Common roots evaluate to β. If no common rational root exists on the split, squarefree support of G, then at every root of G at least one f_j is nonzero. Interpolation gives t_j∈S with Σ f_j t_j=1: at each root pick a nonzero f_j, set that coordinate of t_j to its inverse and the others to zero. This selection occurs solely in the proof. Shifting every U_j by βt_j is a bijective translation giving equal full NO laws. The proofs coinShift and headerWitness cover the shift and evaluation algebra. For m=1 multiplication by f₁ is a permutation of S. This saves one key and the normalization of f₁. The general m-constraint version uses m·deg(G) field coins and transmits deg(G) elements. Uniform sampling of the entire quotient can be necessary for this argument with arbitrary f_j.

For a 128-input NAND circuit, pack the witness bijectively as z∈GF(2^128) using a public binary basis. Given a public monic squarefree split G of degree d whose roots **contain every accepting packed input**, evaluate the original NAND circuit in S on the coordinate polynomials x_i(z)=Tr(a_i z) for the dual basis (a_i). Write these as Σ_{k=0}^{127} a_i^{2^k} z^{2^k} modulo G. The constant wire is one, each NAND is 1+xy, and an unavailable wire reads one as in the registered evaluator. Let C be the final residue. For all roots z of G, C(z) is the actual output bit. On a NO instance C is identically zero modulo G. One uniform random bit u now suffices. Emit

    H = (β xor u) + u C        in canonical degree-<d coefficient form.

At a satisfying witness H(z)=β. On NO the same coefficient vector is produced by swapping u between bits. The raw program syntax containing β and u is not an eligible serialization. The proof uses once again that G is squarefree and split. The formal bitMaskedNo and bitMaskedYes verify the binary coin pairing and the evaluation identity. This works for arbitrary NAND syntax under the given guard. It requires an efficiently obtained guard with a proof of coverage. For the universal guard X^(2^128)−X the output occupies 128·2^128 bits and already violates the cap. In particular a guard containing every satisfying input of a tautology has degree at least 2^128. On a scalable family this is a limitation of witness-by-witness root coverage; compressed residues or a different quotient may change it. A shape-dependent guard and its width must be computed from the public statement, independently of β.

With schoolbook arithmetic, 127 squarings in S generate z^{2^k}, and 128×128 scalings of length-d vectors form all coordinate functions. Subsequent 4096 NANDs take at most 4096 schoolbook products and reductions. Raw bounds are O((4096+128)d² + 128²d) operations in GF(2^128), O((4096+128)d) field elements if all gate residues are retained, 128d output bits and one random bit. Root evaluation by Horner takes O(d) additional field operations. A known syntactic conjunction guarding k fixed input bits has 2^(128−k) possible addresses and its affine-subspace vanishing polynomial is public. A two-bit encoding further reduces transmission when d>0. Write D=1+C and H=β+uD. Fix an F₂-linear coordinate ℓ on S with ℓ(1)=1. Send (ℓ(H),a), where a=1 iff the canonical H is outside the binary span {0,1}. On YES, D cannot be 1 since D vanishes at a satisfying root. If a=1, u=1 and the receiver obtains β=ℓ(H)+ℓ(D). If a=0, either u=0 or D=0, hence β=ℓ(H). For NO, D=1, and the packet is (β xor u,0). A degree-zero guard has only NO statements under the coverage promise; always emit (0,0). This compression needs a complete scalar-membership test on H and a way for the receiver to obtain ℓ(D). Given scalar membership for D and its ℓ(D), deciding whether D=1 decides nonexistence of an accepting root. Thus the shorter packet alone gives no inexpensive general compiler. On this structured family, a receiver with enough time can decode YES even without providing a witness, which is consistent with false-statement privacy. The raw 128d-bit bound above refers to uncompressed coefficients.

These counts do not certify the input parser, field software, gate-memory access or the registered clock.

## Boundaries and replay

Using f=g equal to a rootless irreducible quadratic without normalization releases β from V−U even on NO. Using a common label outside the attainable set does the same after normalization. The matrix gluing proof rules out this latter case. Publicly selecting common tree prefixes for GGM works only when the constrained descriptions share a suitable tree; for an endpoint predicate depending on the last bit, its explicit positive prefix cover in that order can need 2^(n−1) leaves. The residue construction can have a tiny number of labels despite such a cover. Neither it nor a one-corruption PCF supplies a compact constrained-key primitive for arbitrary trace readers. If a proposed proof punctures M locations, an ordinary telescoping bound is Mε with cost at least that of a specific adapter and its key synthesis. A per-coordinate proof over all raw addresses has M=2^12417; no such hybrid, registered sparse-LPN game, or all-circuit cost/security bound is claimed here.

The following reference program needs only Python 3. It counts full coefficient pairs, checks stream issuance for each tested nonce, checks every common root, exercises repeated, zero and rootless inputs, and validates exact gluing in the separate-syndrome fixture. Its output gives the number of subset pairs, disjoint pairs, distinct nonce trials summed over instances, payload/nonce trials, and pairs of syndrome predicates.

```python
from collections import Counter
from itertools import combinations, product, chain

# F4 = F2[a]/(a^2+a+1). Each base-4 digit is a field coefficient.
def times(x, y):
    return ((x if y & 1 else 0) ^
            (((x << 1) ^ (7 if x & 2 else 0)) if y & 2 else 0))

def scale(p, a):
    out = 0
    for j in range((p.bit_length() + 1) // 2):
        out ^= times((p >> (2*j)) & 3, a) << (2*j)
    return out

def degree(p):
    return (p.bit_length() - 1) // 2

def mul(p, q):
    out = 0
    while q:
        out ^= scale(p, q & 3)
        p <<= 2
        q >>= 2
    return out

def rem(p, g):
    assert g and g >> (2 * degree(g)) == 1
    while p and degree(p) >= degree(g):
        out = scale(g, p >> (2 * degree(p)))
        p ^= out << (2 * (degree(p) - degree(g)))
    return p

def monic(p):
    if not p:
        return 0
    top = p >> (2 * degree(p))
    return scale(p, next(a for a in range(1, 4) if times(top, a) == 1))

def gcd(p, q):
    while q:
        q = monic(q)
        p, q = q, rem(p, q)
    return monic(p)

def roots_poly(roots):
    out = 1
    for z in roots:
        out = mul(out, 4 ^ z)
    return out

def value(p, z):
    return rem(p, 4 ^ z)

def keys(f, g, p, b):
    return rem(p, f), rem(p ^ b, g)

def stream(f, g, coeffs, b):
    u = v = 0
    for a in coeffs:
        u, v = rem((u << 2) ^ a, f), rem((v << 2) ^ a, g)
    return u, rem(v ^ b, g)

subsets = list(chain.from_iterable(combinations(range(4), k) for k in range(3)))
pairs = disjoint = seeds = 0
for a, c in product(subsets, repeat=2):
    f, g = roots_poly(a), roots_poly(c)
    common = set(a) & set(c)
    d = degree(f) + degree(g)
    laws = [Counter(), Counter()]
    for p in range(4**d):
        digits = [(p >> (2*j)) & 3 for j in reversed(range(d))]
        for b in (0, 1):
            u, v = keys(f, g, p, b)
            assert stream(f, g, digits, b) == (u, v)
            laws[b][u, v] += 1
            for z in common:
                assert value(u, z) ^ value(v, z) == b
    assert (laws[0] == laws[1]) == (not common)
    if not common:
        assert len(laws[0]) == 4**d and set(laws[0].values()) == {1}
        disjoint += 1
    pairs += 1
    seeds += 4**d
t = (1 << 8) ^ 4             # X^4 - X
irr = (1 << 4) ^ 4 ^ 2      # X^2 + X + a, with no rational root
assert all(value(irr, x) for x in range(4))
assert gcd(irr, t) == 1 and gcd(0, t) == t
assert gcd(mul(4 ^ 2, 4 ^ 2), t) == 4 ^ 2
assert all((u ^ v) == b for p in range(256) for b in (0, 1)
           for u, v in [keys(irr, irr, p, b)])
# A constant label reaches only 0. The common root 1 leaks even on this NO.
assert value(4 ^ 1, 0) != 0
for b in (0, 1):
    u, v = keys(4 ^ 1, 4 ^ 1, 3, b)
    assert value(u, 1) ^ value(v, 1) == b

# Distinct summaries of x in F2^3, enumerated separately by opposite reads.
# Local state (x0 xor x1, x1) and (x2, x0 xor x1) glue on parity bit only.
for a, c in product(range(16), repeat=2):
    def pa(x): return ((x & 1) ^ ((x >> 1) & 1)) * 2 + ((x >> 1) & 1)
    def pb(x): return ((x >> 2) & 1) * 2 + ((x & 1) ^ ((x >> 1) & 1))
    roots_a = {s >> 1 for s in range(4) if a >> s & 1}
    roots_b = {s & 1 for s in range(4) if c >> s & 1}
    sat = any((a >> pa(x)) & (c >> pb(x)) & 1 for x in range(8))
    assert sat == bool(roots_a & roots_b)
print(pairs, disjoint, seeds, 2*seeds, 256)
# Degree-<d quotient NAND evaluation on packed F4 addresses and a two-bit codec.
def tracepoly(a, G):
    ax = scale(4, a)
    return rem(ax ^ mul(ax, ax), G)

def truth_gates(mask):
    gates = []
    def nand(i, j):
        gates.append((i, j))
        return 2 + len(gates)
    def neg(i):
        return nand(i, i)
    def conj(i, j):
        return neg(nand(i, j))
    out = nand(0, 0)
    for z in range(4):
        if mask >> z & 1:
            lo = 1 if z & 1 else neg(1)
            hi = 2 if z & 2 else neg(2)
            term = conj(lo, hi)
            out = nand(neg(out), neg(term))
    return gates

def run_poly(gates, G):
    one = rem(1, G)
    wires = [one, tracepoly(3, G), tracepoly(1, G)]
    for i, j in gates:
        x = wires[i] if i < len(wires) else one
        y = wires[j] if j < len(wires) else one
        wires.append(one ^ rem(mul(x, y), G))
    return wires[-1]

guard_cases = 0
for mask, guard in product(range(16), repeat=2):
    if mask & ~guard:
        continue
    G = roots_poly([z for z in range(4) if guard >> z & 1])
    C = run_poly(truth_gates(mask), G)
    assert all(value(C,z) == ((mask >> z) & 1) for z in range(4) if guard >> z & 1)
    D = rem(1 ^ C, G)
    transcripts = [[], []]
    for b, r in product(range(2), repeat=2):
        H = rem(b ^ (D if r else 0), G)
        packet = (H & 1, int(H not in (0, 1))) if guard else (0, 0)
        transcripts[b].append(packet)
        for z in range(4):
            if mask >> z & 1:
                assert value(H,z) == b
                assert packet[0] ^ (packet[1] * (D & 1)) == b
    if not mask:
        assert sorted(transcripts[0]) == sorted(transcripts[1])
    guard_cases += 1
assert guard_cases == 81
print("guarded NAND cases", guard_cases)
```

Expected output: `121 63 12769 25538 256` then `guarded NAND cases 81`. The second test exhausts all 16 two-input truth functions, compiling each to NAND gates, and all squarefree guards covering its accepting inputs. It checks trace-coordinate extraction, canonical quotient evaluation, recovery, and the two-bit code.
