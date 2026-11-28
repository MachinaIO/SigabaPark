---
title: Short NAND preimages, rounding inside a hidden frame and a rank-certified center packet
refs: [definition:WE_CircuitSAT_Capped, definition:ShortNand, theorem:AdvancedEncryption.WE.ShortFrame.gap, theorem:AdvancedEncryption.WE.ShortFrame.portRep, theorem:AdvancedEncryption.WE.ShortFrame.complementary, theorem:AdvancedEncryption.WE.ShortFrame.rankMask]
tags: [witness-encryption, lattices, correctness, counterexamples]
---

### A short-preimage relation for every registered NAND circuit

Each NAND has one integer coordinate per valid triple 001,011,101,110. Require their sum to equal one mod q, the two represented inputs to match the source ports, and the final output to equal one. Wire zero, a forward reference and an out-of-range port denote true as in the core fold. The empty circuit starts with last output true. The four coordinates are the only charged variables per gate. The Lean relation existentially names primary-port values and threads computed outputs. To form a literal matrix, equate all occurrences of each primary to its first representative, remove unused primaries and substitute the three fixed linear port forms at every remaining occurrence. The portRep equivalence proves this projection for arbitrary occurrence sets including empty ones. Alternatively impose all equalities to the chosen port instead of all pairs. This uses 4G columns, at most 3G+1 rows and a constant number of nonzeros per equation. Unused primaries can be filled arbitrarily, so accepting traces need not identify the primary witness uniquely.

For every integer q≥5, a normalized block of squared norm below three is a positive unit. Indeed its mass lies between −2 and 2 and equals one mod q. The remaining possibilities with one or two unit magnitudes can be checked directly. Hence any feasible integer vector has squared norm G or at least G+2, and the first alternative occurs exactly for an accepting registered input. Witness generation runs the actual evaluator then chooses its unique local unit. This concerns all integer lifts of the modular system, with no distributional hypothesis. The gap is sharp on a full-size NO: let y be the end of 4093 consecutive NOTs on one primary x, a=NAND(x,y), b=NAND(y,x), o=NAND(a,b). Both x values give a=b=1,o=0. Replace just the last unit in an honest evaluation by (−1,1,1,0), which keeps the incoming 1,1 but sets o=1. Its block squared norm is three.

### The hidden isometry does not make short-point delivery exclusive

Consider the actual public packet H=ML+U and h=Md+E over a large prime residue field. Only H,h and the lock are released. M is an independent random linear map. U is any hidden integer m-by-4G matrix with UᵀU=αI, α a positive integer. For every modular solution Lw=d the full header gives y=h−Hw=E−Uw modulo q. An honest w gives radius t=√(αG) while the next feasible integer lifts have radius at least √(α(G+2)) before reduction. This inequality alone does not exclude using several evaluations.

A signed local interpolation of arbitrary inputs/output x,y,z is (2−x−y−z,y+z−1,x+z−1,1−z). Its four sums reproduce the mass and all three ports over the integers. On the NO fixture above set the primary and all nonfinal outputs to zero or all to one, forcing the final output to one in both cases. Call the interpolated vectors w0,w1. Every nonfinal pair adds to (1,0,0,1), the final pair to (0,1,1,0). Therefore ||w0+w1||²=2G. The squared difference is 18(G−1)+6. They are public, exactly feasible, and available independently of the issuer's basis or coins.

Compute both public evaluations, take the centered lift of y1−y0 and form y0 plus the coordinatewise floors or ceilings of its half. Reduction modulo q after rounding is harmless. For q>2√(α[18(G−1)+6]), the lifted difference is exactly U(w0−w1). The two errors relative to E, as integer lifts, are the two coordinatewise halves of v=U(w0+w1) rounded complementarily, up to a global sign/interchange. Their squared distances sum to (||v||² + number of odd coordinates of v)/2, which is at most ||v||²=2αG. At least one candidate lies in the honest ball; both lie within √2 t. The Lean complementary lemma proves the dimension-independent rounding inequality. The attached executable checks the wire interpolation, norms, modular lifting and rounding with two different isometries at G=4096. This refutes exclusivity for the proposed affine packet even when U is neither recoverable nor public. Decoding by walking a single affine evaluation misses this possibility.

### What the published trapdoor gives

Aggarwal, Jain, Lin and Wu, [On the Hardness of LWE with Trapdoor Hints and Applications to Fuzzy Cryptography](https://eprint.iacr.org/2026/2927), Lemma 3.10, Theorems 4.2 and 5.1, and Figure 2. Their obfuscation publishes (A,T,b=Aᵀs+E), where T is a homogeneous trapdoor. Here E is a discrete Gaussian center (effectively restricted to X by a negligible tail). Their evaluator calls TdInvert on b−x'. With overwhelmingly good setup it recovers (s,E−x') if the integer error has Euclidean norm ≤t and rejects errors in (t,λ₁−t), with λ₁=q. Its exact ball functionality is promised for x,x'∈X, the norm-B domain with 2B<q−t. For a permissive direct call to the published inversion code it suffices that the residual admit the promised lift. A near candidate thus recovers the centered secret residue vector E; to remain literally inside the functional domain use ||E||≤B−t. On the NO fixture both candidate errors are below q−t in the described regime, so every successful output is genuine. The paper's figure encodes a point predicate, without a message bit.

For an explicit bit lock release bβ=b+βp, where p has length >2t and ||p||+2t<q. A genuine near witness y decrypts by applying TdInvert to bβ−y−jp for j=0,1 and selecting the unique success. Apply the two-candidate calculation with ||p||> (1+√2)t and q>||p||+(1+√2)t. Then the same four trials on the NO fixture recover β for every good setup. These stronger inequalities can be met with p=(ceil(3t)+1)e₁ and large q. Correct use of the short-error guarantee and the rejection annulus both matter. This is an obstruction to this concrete construction, not a claim about general ball obfuscation or nonlinear issuers.

### Positive rank-certified specialization

Over a finite prime field, suppose d is outside the image of the public L on a NO input. A linear functional ell with ell L=0, ell d=1 exists by extending a basis. For every fixed pair of centers E,E', translation M↦M+ell(·)(E−E') is a bijection preserving H and carrying Md+E to M'd+E'. The rankMask theorem proves this bijection. Thus conditioned on ML,U and the center-dependent lock, h is fresh uniform as long as M was sampled independently and uniformly. A simulator without E or s uses independent M,U for H and a fresh uniform h. It also works with the entire serialized H, including the correlations among its columns. This applies to strengthened linear constraints; on the raw four-row system every nonempty circuit permits signed interpolation with arbitrary final value, so its NO instances never have this rank certificate.

For an example, add local linear zero constraints eliminating impossible selectors for identical input references (01 and 10), and when one input is publicly constant, eliminate rows with the wrong value at that port. Consider circuits built only of repeated-input NOT gates and NANDs with a fixed-true parent: propagate syntactically known constants and identify default-true ports. Over the prime field every gate output is then exactly 1−v for its other port. Any feasible assignment makes the final output a constant or an affine literal on one primary. Such a literal can reach one on Boolean input whenever it reaches one on field input. Consequently on this whole class every NO circuit has inconsistent strengthened linear system, while every accepting Boolean witness still gives a genuinely short w and the near point h−Hw. This specialization covers arbitrary chain length and fanout, with simple satisfiability. The full 4093-NOT fixture also contains two unrestricted two-input NAND gates, so the specialization does not claim it.

For the specialization, take the fixed challenge of the paper's Theorem 4.2 with empty leakage and no extra columns (or discard sampled extra columns). Form H and h by the independent simulation just proved and shift the received syndrome by βp. In the real branch this samples exactly the NO transcript with the Gaussian error law; in the uniform branch shifting the syndrome preserves its law. A two-leg reduction bounds the distinguishing gap by two fixed-challenge advantages plus any explicit Gaussian truncation/setup error. In the real issuer sample the independent Gaussian E, M and U, and the standard lock using the same E. Honest decryptors generate the short row directly from the primary witness and never need the mask or secret frame. The reduction needs the paper's actual parameters: polynomially bounded prime q, m≥4n log q+1, τ>2, c=ceil(log_τ q), trapdoor width r≥mτ·ω(√log m), t≪q/(4rm), and Gaussian/domain slack as in Theorem 5.1. It needs its dimension- and noise-adjusted decisional LWE premise. No quantum theorem or exact registry game identification is supplied here. A uniform random challenge syndrome does not simulate correlated columns by itself when d lies in the image of L.

At 4096 gates the hidden isometry requires m≥16384 and literal output of H,h has at least (16384+1)m·ceil(log₂ q) bits before the lock or the machines. At 16 bits per coefficient this alone is 4,295,229,440 bits. The bound applies to explicit fixed-width serialization. Streaming a uniform matrix is not free, and a seeded mask changes the above exact simulator. The additive norm gap is two in squared distance, about 0.0156 in unsquared distance for α=1. Neither the registered honest-machine cost, full-circuit hardness reduction, nor finite post-quantum security follows.

### Reproduce the full-size hidden-frame examples

Run with Python 3. The wire numbering in this listing drops the unused constant wire, and the circuit uses one primary. Appending 127 unused primaries and shifting gate references gives the same fixture in the registered 128-primary layout.

```python
"""Run this file with Python 3. The 4096-gate fixture uses one primary port."""
from itertools import product
from random import Random

def row(x, y, z):
    return (2-x-y-z,y+z-1,x+z-1,1-z)

def sq(v):
    return sum(x*x for x in v)

def mx(m, v):
    return [sum(a*b for a,b in zip(r,v)) for r in m]

def experiment():
    g = 4096
    gates = [(j,j) for j in range(4093)]+[(0,4093),(4093,0),(4094,4095)]
    def rows_for(inputs, forced):
        wires = [inputs]
        rows = []
        for j,(a,b) in enumerate(gates):
            x,y = wires[a],wires[b]
            z = (1 if j==g-1 else inputs) if forced else 1-x*y
            rows.extend(row(x,y,z))
            wires.append(z)
        return wires,rows
    for x in (0,1):
        assert rows_for(x,False)[0][-1]==0
    w0=rows_for(0,True)[1]
    w1=rows_for(1,True)[1]
    assert sq([a+b for a,b in zip(w0,w1)])==2*g
    assert sq([a-b for a,b in zip(w0,w1)])==18*(g-1)+6
    w=rows_for(0,False)[1];w[-4:]=row(1,1,1)
    assert sq(w)==g+2
    rng=Random(189)
    for m in [((1,0,0,0),(0,1,0,0),(0,0,1,0),(0,0,0,1)),
              ((1,1,1,1),(1,-1,1,-1),(1,1,-1,-1),(1,-1,-1,1))]:
        alpha=sq(m[0]); q=104729
        perm=list(range(4*g)); rng.shuffle(perm)
        signs=rng.choices((-1,1),k=4*g)
        def apply(v):
            a=[c for i in range(0,len(v),4) for c in mx(m,v[i:i+4])]
            return [a[j]*s for j,s in zip(perm,signs)]
        e=[rng.randrange(q) for _ in perm]
        y0=[(a-b)%q for a,b in zip(e,apply(w0))]
        y1=[(a-b)%q for a,b in zip(e,apply(w1))]
        lift=lambda x:(x+q//2)%q-q//2
        delta=[lift(b-a) for a,b in zip(y0,y1)]
        dist=[sq([lift(s+d//2+h*(d%2)-a) for s,d,a in zip(y0,delta,e)]) for h in (0,1)]
        assert min(dist)<=alpha*g and sum(dist)<=2*alpha*g
        print(g,alpha,dist)
if __name__=='__main__':
    experiment()
```
