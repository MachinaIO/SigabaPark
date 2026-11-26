---
title: Building the masked evaluator without iO - positional local reprogramming, why BGG+ two-block encodings cannot entangle the keys, GGH15 as the entangling mechanism
refs: [definition:WE_CircuitSAT, note:pq-we-witness-prf-masked-evaluator, note:pq-we-hybrid-count-barrier, note:pq-we-evaluation-oracle-crux, note:pq-we-matrix-collision-barrier, note:pq-we-decryptor-attribute-dead-end, note:pq-we-function-hiding-crux, note:pq-we-ggh15-chain-verdict, theorem:AdvancedEncryption.WE.MaskedEval.mask_leak, theorem:AdvancedEncryption.WE.Hybrid.hardAt_chain]
tags: [witness-encryption, strategy, candidate, barrier]
---
This note continues `pq-we-witness-prf-masked-evaluator`. It addresses how to build, from falsifiable
assumptions and far more simply than iO, a public mechanism `Ô` returning
`O(x, w) = CPRF(k, (x, w)) + PRF(k', x)` that is usable with the constrained key `ck_C`. Arguments
are informal.

## 1. Which security notion for `Ô`?

**Correct only on valid pairs is circular.** An `Ô` that is required to be correct only where
`C(x, w) = 1` is a witness-PRF evaluator by itself, and `ck_C` adds nothing. The decomposition pays
off only if the proof uses `Ô` on **invalid** pairs, where `CPRF` is pseudorandom given `ck_C`.

**No statement-independent, polynomial-hop notion is sufficient.** Suppose `Ô`'s security were an
indistinguishability `(ck_C, Ô) ≈ (ck_C, Ô')` with an instance that does not depend on `x*`, used
in polynomially many hops. Then by `pq-we-hybrid-count-barrier` the resulting WE would put NP in
SZK. Concretely, every such `Ô'` that makes the mask of `x*` independent also changes `O` at some
valid pair of some true statement, and the decryptor distinguishes there. So a sufficient notion is
either statement-dependent (MEV of the companion note: "for this `x* ∉ L`, the mask is
pseudorandom", which is a statement-dependent assumption on one fixed family) or it is used in
about `2^128` hops.

**The weakest sufficient falsifiable notion we found: positional local reprogramming (PLR).**
The evaluator generator takes a hidden position `(x*, t)` with `t ∈ {0, …, 2^{|w|}}` and outputs
`Ô_t`. It computes

`O_t(x, w) = CPRF(k, (x, w)) + PRF(k', x)` unless `x = x*` and `w < t`, where it outputs
`CPRF(k, (x, w)) + PRF(k'', x)` (`k''` independent).

The real evaluator is `Ô_0`; for `t = 0` the position is irrelevant, so `Ô_0` does not depend on
`x*`. Security has two parts:

* **(Hiding of the position at `t = 0`)** Statistical or by definition: `Ô_0` is the same for every
  `x*`.
* **(PLR hop)** For every `x*`, `t` with `C(x*, t) = 0`:
  `(ck_C, Ô_t) ≈ (ck_C, Ô_{t+1})` with advantage `ε`.

The PLR hop is **falsifiable**: the challenger checks `C(x*, t) = 0` in polynomial time. It is
**statement-independent** in the sense of the barrier: it is indexed by a point, not by a statement,
and it is meant to hold also at non-witness points of true statements (the decryptor never queries
there). It is **sufficient**: `2^{|w|}` hops reach `Ô_{2^{|w|}}`, whose answers at `x*` are all masked
by the independent `k''`, so `PRF(k', x*)` is independent of the view. The accounting is that of
`AdvancedEncryption.WE.Hybrid.hardAt_chain`: premises of about `128 + 2·128 = 384` bits give
`λ = 128`.

**How PLR differs from iO, and the Branco–Jain–Srinivasan warning.** BJS (ePrint 2025/2215) show
that sub-exponential LWE plus *average-case iO for PRFs* gives iO. PLR differs in three ways:

* It is one fixed algebraic family.
* Each hop changes the function, at one point whose new value is pseudorandom given `ck_C`, which
  is public leakage of everything else. iO and aiO speak about functionally equivalent programs and
  never require a change of output to be hidden.
* Only the mask of `x*` must end up hidden, and nothing about the keys `k, k'`.

We see no reduction from aiO-for-PRFs to PLR. PLR implies WE, and whether it implies iO is open.
Its closest relative is the instance-independent assumption of positional WE
(Gentry–Lewko–Waters, CRYPTO 2014), which is also not known to imply iO. **Warning, stated
honestly:** PLR for a family that allows hiding *arbitrary* positions inside general programs would
be close to iO. PLR is weaker only if the family's positional structure is fixed (a comparator on
`w` against a threshold) and the function family is the specific one below.

## 2. Concrete encodings: why the two keys must be entangled, and why BGG+ cannot do it

Write `t = (s; s')`. Publishing an evaluator of the single key-homomorphic PRF
`⌊tᵀ[A_{U_z}; B_x]⌉` in the clear reveals `t`. The mechanism must output `sᵀA_{U_z} + s'ᵀB_x`
without letting either summand be computed alone, except that `ck_C` gives `sᵀA_{U_z}` on valid `z`.

**BGG+ with two attribute blocks: dichotomy.** Joint encodings
`c_i = tᵀ(M_i − a_i G_t) + e_i` with `G_t = diag(G, G')`.

* *Block-diagonal* `M_i = diag(A_i, B_i)`. Every `EvalF` step `M_a G_t⁻¹(M_b)` stays
  block-diagonal (`G_t⁻¹` acts block-wise), so the `s'`-component of any evaluation is the
  evaluation of the `s'`-encodings alone. The `s'`-encodings carry an attribute the adversary knows
  (it can only depend on `x`, since the mask must not depend on `w`). For any circuit `g` with value
  `0` on that attribute, the adversary gets `s'ᵀB_g`, and in particular the mask circuit's output.
  Making the value depend on `w` makes the mask `w`-dependent, and making it depend on `C` turns the
  `s'` part into a second BV key: the plain-BGG+ deviation of `mask_leak` returns. **Decoupled ⇒
  mask computable.**
* *Entangled* (off-diagonal blocks). `G_t⁻¹` of a stacked matrix mixes the blocks, so the
  `s`-component of the joint `EvalF(U_z)` is not `A_{U_z} = EvalF(U_z, A)` and does not cancel
  against `ck_C`. Agreement on all `2^128` points is an evaluation collision
  (`pq-we-matrix-collision-barrier`): structural ones are reachable by constant circuits, and no
  non-structural mechanism is known. **Entangled ⇒ collision.**

**Rounding** (`⌊·⌉_p` anywhere) only adds deterministic errors and does not change the normal form
`s_lastᵀ(M − vG) + err` of public-matrix processing. **Succinct/decomposed-LWE public trapdoors**
only re-express attributes (`pq-we-decryptor-attribute-dead-end`) or are closed under short linear
combinations (rank-one access, `pq-we-matrix-collision-barrier`). Neither supplies entanglement.

**The entangling mechanism is hidden-matrix GGH15.** In
`D_{i,b} ← A_{i−1}⁻¹(Ŝ_{i,b} A_i + E)` with hidden `A_i` and block secrets
`Ŝ = diag(mask block, M ⊗ S', S)`, the blocks are entangled through the hidden matrices. The
decryptor sees only products of the `D`'s, and only through the published left vectors `J A_0`. It
cannot evaluate one block alone unless some left vector isolates that block; the rank-one
left-vector condition of the companion note §5 is exactly this. So the masked γ⊗-GGH15 scheme is
the concrete form of "keep `s` and `s'` entangled": `S` is the CPRF block (`s`), the mask block is
`s'`, and `ck_C` is the second left vector, which cancels the `S` block on paths where the
constraint block vanishes.

## 3. The PLR instance: positional masked γ⊗-GGH15

Statement fixed (`x* = φ`), levels read `w` (with the Tseitin gate bits), CNF diagonal BP `M_{i,b}`
of `Ψ_φ`. Per level:

`Ŝ_{i,b} = diag(P_{i,b} ⊗ R_{i,b}, M_{i,b} ⊗ S'_{i,b}, S_{i,b})`

* **Comparator mask block.** `P_{i,b}` is the reflected-Gray comparator (states lt/eq/gt) against
  the threshold `t`, as in the positional candidates. The final rows of `A_h` are `mask'` on state
  lt and `mask` on eq/gt. `R_{i,b}` are fresh secrets per (level, bit).
* **Constraint and CPRF blocks** as in the companion note.
* **Left vectors.** `u_O` reads the comparator's start state and the `S` block; `u_C` reads the
  constraint block and the `S` block. Their difference has rank one, by the companion note's rank
  repair.
* **Real ciphertext.** `t = 0`: every path ends in eq/gt, so `O − ck = mask` on witnesses, and the
  ciphertext carries `⌊mask⌉ + μ`.
* **Final hybrid.** `t = 2^{|w|}`: every path ends in lt, so `mask` no longer appears in the view.

Hops `t → t+1` (path `t` a non-witness) follow the pattern of the positional GGH15 note in open PR #42:

* flip the isolated eq leaf of path `t` from `mask` to `mask'`, justified by `M_t ≠ 0`;
* reroute the now-decided subtree into lt;
* isolate path `t+1`.

What is new compared with PR #42:

* **The path secrets are γ⊗ products.** The comparator and constraint blocks use `P ⊗ R` and
  `M ⊗ S'`, the γ⊗ form for which CVW18 prove LWE security of single-left-vector encodings
  (Cor. 5.9).
* **The flip is local in a precise sense.** On path `t` the constraint block contributes
  `C(t) = (j_C M_t ⊗ s'_0 S'_t)A^{con} ≠ 0`. The `O − ck` value of path `t` is `mask − C(t)`,
  and `C(t)` is a fresh-looking product along path `t` alone.

**Missing lemma (PLR hop for positional masked γ⊗-GGH15).** In the setting above, for `t` with
`C(φ, t) = 0`, the views of hybrids `t` and `t+1` differ by at most `poly(h)·ε_LWE`. It would
follow from a two-left-vector version of CVW18 Cor. 5.9 restricted to the case "the eq-path `t` has
a non-zero constraint product". A natural first instance is `h = 2`: two levels and a two-clause
CNF.

**Cost** (rough). Width `t_dim = 3·d_R + (#clauses)·n' + n`. With Tseitin for `2^12` NAND gates
there are about `3·2^12` clauses, so `t_dim ≈ 1.2·10^4 · n'`, and `h ≈ 2^12 + 128` levels.
Everything is polynomial and concretely very large, yet much simpler than any iO: no bundling
scalars, no Kilian randomization, no permutation BPs, read-once, two left vectors.

## Verdict

* The masked evaluator is workable as an interface.
* Its weakest sufficient falsifiable notion is PLR: hops indexed by points with an efficiently
  checkable `C(z) = 0`, about `2^128` of them, as the barrier forces.
* BGG+-type encodings (block-diagonal or entangled), rounding and succinct or decomposed public
  trapdoors cannot realize it (decoupled ⇒ the mask is computable; entangled ⇒ evaluation
  collision).
* Hidden-matrix GGH15 entangles the keys by construction. The positional masked γ⊗-GGH15
  instance reduces WE for `Def_WE_CircuitSAT` to one local lemma (the PLR hop above).
