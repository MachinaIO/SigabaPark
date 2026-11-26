---
title: Per-path noise as LWE noise with TLWE trapdoor hints - what the handle must be, an entropy and rank bound, the witness-entry trilemma, and three variants (barrier)
refs: [definition:WE_CircuitSAT_Capped, definition:WE_CircuitSAT, definition:GGH15, note:pq-we-tlwe-trapdoor-hint-zero-test, note:pq-we-tlwe-masked-ggh15-leaf, note:pq-we-hybrid-count-barrier, note:pq-we-native-hop-designs, note:pq-we-xwe-per-item-cost, note:pq-we-ksplit-xwe-routes, note:pq-we-two-input-abe-secret-key, note:pq-we-affine-syzygy-barrier, note:pq-we-evaluation-oracle-crux, note:pq-we-hinted-lattice-assumptions, theorem:AdvancedEncryption.WE.TLWE.eval_difference, theorem:AdvancedEncryption.WE.TLWE.linear_closure, theorem:AdvancedEncryption.WE.TLWE.invalid_offset_cancel, theorem:AdvancedEncryption.WE.TLWE.antitone_chain_few_changes, theorem:AdvancedEncryption.WE.TLWEGGH15.affine_relation_kills_linear_pad, theorem:AdvancedEncryption.WE.TLWEGGH15.cancel_prefix_closed, theorem:AdvancedEncryption.WE.TLWEGGH15.wide_gate, theorem:AdvancedEncryption.WE.KSplit.mix_leak, theorem:AdvancedEncryption.WE.Codes.card_fresh_le_finrank, theorem:AdvancedEncryption.WE.LinearHop.card_killed_le_finrank]
tags: [witness-encryption, tlwe, barrier, strategy]
---
Design-AI sub-task (pp) on `Def_WE_CircuitSAT_Capped` (NAND Circuit-SAT, 128-bit witness, `2^12`
gates, `λ = κ = 128`, cost at most `2^100`). The project owner asks again whether the
**"per-path noise as LWE noise" handle** can be obtained with LWE with trapdoor hints (TLWE,
Aggarwal–Jain–Lin–Wu, ePrint 2026/2927, "AJLW26"). The idea: put constrained-PRF outputs into the
LWE **error**, so that the master-key and constrained-key evaluations at `(x, w)` are close only on
valid pairs, and let a public TLWE trapdoor remove the `sᵀA` mask only when two errors are close.

Prior results this note builds on: `pq-we-tlwe-trapdoor-hint-zero-test` (PR #78: inside linear
processing TLWE is a linear zero test), `pq-we-tlwe-masked-ggh15-leaf` (PR #86: TLWE at the GGH15
leaf decodes exactly but gives no per-path handle), `pq-we-native-hop-designs` (PR #108: a poly-size
positional walk must re-encode), `pq-we-xwe-per-item-cost` (PR #95: BGG+ noise structure), and
`KSplit.mix_leak` (PRs #80/#87). Open PR #110 (`pq-we-zero-entry-crossing`, not merged, cited by
number) adds that TLWE-type lossiness needs `σ_e σ_t ≳ q m`, which honest decryption violates.

The six theorems `AdvancedEncryption.WE.NoiseHandle.*` come with complete proofs in the same PR.
They are not in `refs` because they are not merged yet.

## Answer

1. **The handle, stated exactly (§2).** A per-path LWE handle at a path `w*` is a hybrid step in
   which an LWE challenge's fresh noise *becomes* the noise of path `w*`, while every other path
   value keeps its distribution. In support form this needs **local freshness**: the value of path
   `w*` is not determined by the values of all the other paths. A `2^128`-hop proof on a false
   statement needs such a step at every one of the `2^128` paths.
2. **Entropy and rank bound (§3, Lean).** In any single distribution, at most `N` paths can be
   locally fresh at once if the ciphertext has `N` bits (`fresh_paths_le_bits`, from
   `two_pow_le_card_of_locally_fresh`). If the decryptor's path values are linear in the ciphertext
   (BGG+, GGH15 with public right factors, any short public combination), at most `dim` paths admit
   a perturbation that moves only their own value (`linear_fresh_card_le_finrank`). For
   `WE_CircuitSAT_Capped` the ciphertext has at most `2^100` bits, so at most `2^100` of the `2^128`
   paths. The structured family `{sA_w + e H_w}` is exactly as hard as plain LWE, but its handle
   is **global**: one LWE hop switches all paths, valid ones included. Per-path hops therefore need
   a **different ciphertext structure in each hybrid** (puncturing or re-encoding). That is the
   re-encoding gap of `pq-we-native-hop-designs`, not a noise question.
3. **The owner's gate, exactly (§4).** Rounding commutes with differences up to a carry in `{0,1}`
   (`floor_sub_carry`). So the master-minus-constrained value at `w` is a public linear image of the
   ciphertext. TLWE decodes it iff (i) the secret part is aligned with the trapdoor's matrix and
   (ii) the error is at most `t ≤ q/(4mτ)` (AJLW26 Thm 3.2). On invalid paths the error must sit in
   the regime where TLWE is proven, `σ_e ≥ (q/τ)·ω(√log λ)` per coordinate (Thm 1.1/4.1), a factor
   of order `4 m^{1.5}` above the radius.
4. **Witness-entry trilemma (§5).** Witness bits enter the computation in one of three ways:
   * in the evaluated circuit `U_w`: the decoded matrix depends on `w` (Case I of PR #78), or the
     gate is a hidden-vector linear zero test (Case II);
   * as attributes under one secret: both bit encodings are present, so `mix_leak` applies;
   * as per-bit-value encodings: additive composition satisfies exact rectangle relations
     (`additive_rectangle`) and gives affine gates. An affine gate jumps by at most a factor 3
     across a face with three small corners (`affine_face_gap`). A clause-local affine gate puts
     every path of a false unit-clause-free CNF within `3×` the decoding radius, far outside the
     TLWE regime, and is broken. Multiplicative
     composition is GGH15, already settled in PR #86 (`affine_relation_kills_linear_pad`,
     `cancel_prefix_closed`).
5. **Three variants (§6).**
   * **V1, CPRF in the error.** Rounded PRF outputs are either known to the evaluator or narrow
     carries. An FHE/BGG+ known-coordinate trick does put a wide, exact `β·PRF(w)` into an LWE
     error, with master and constrained values equal exactly on valid paths: the closeness half of
     the idea works. The alignment half fails. The decoded matrix depends on the public evaluated
     FHE ciphertexts (Case I). With public-coin matrices, the same channel lets anyone strip the
     secret part on one side alone, which is FHE decryption at every path, or leaves wide masks that
     do not cancel (`eval_difference`).
   * **V2, noise-as-message decoding at the last step.** This is PR #86: exact decoding and no
     handle.
   * **V3, subspace-restricted (gadget) hints.** These are linear zero tests (`linear_closure`).
     They have the shortcut and linearization attacks of PR #78, and at most `dim` positional
     changes (`antitone_chain_few_changes`).
6. **Verdict.** The handle in the owner's sense does not exist in any lattice design whose
   decryptor computes linearly with rounding, with or without TLWE. This is a theorem-level
   statement for per-path freshness (items 1–2). It is a case analysis, with Lean lemmas for each
   case, for the TLWE gate (items 3–5). No design survives, so there is no cost to compare with
   `2^100`. Three weaker handles remain (§7):
   * the global handle (one LWE hop on the whole family, statement-independent, so blocked by
     `pq-we-hybrid-count-barrier`);
   * a per-hybrid handle on at most `dim` paths, which needs a functionality-preserving
     re-encoding between hybrids (the open lemma of PRs #86/#108);
   * gated wide errors at the GGH15 leaf (`wide_gate`), which are per-path but linear in the gated
     row.

## 1. What AJLW26 gives (read from the full text)

* **Definition 1.1 (TLWE).** Distinguish `(A, T, sᵀA + eᵀ mod q)` from `(A, T, uᵀ)` for
  `A ← Z_q^{n×m}`, `s ← Z_q^n`, `e ← D_{Z^m, σ_e}`, with `T` a Gaussian full trapdoor of
  `Λ_q^⊥(A)` of width `σ_t`. The paper notes that it is trivially broken when
  `σ_e σ_t = o(q/√m)`, because then `eᵀT mod q = eᵀT` over `Z`.
* **Theorem 1.1 (informal).** For `4n log q ≤ m ≤ poly(n)`, `τ^c/2 < q < τ^c`,
  `σ_t ≥ m·τ·ω(√log n)` and `σ_e ≥ (q/τ)·ω(√log n)`, TLWE is hard assuming LWE in dimension
  `Ω(n/log q)` with modulus-to-noise ratio `τ m^{1.5}`.
* **Theorem 3.2 (trapdoor sampling, from MP12, with the two-sided form of Remark 3.3).**
  `TdInvert(A, R, t, Aᵀs + e)` returns `(s, e)` if `‖e‖ ≤ t` and `⊥` if `t < ‖e‖ < q − t`, for
  `t ≤ q/(4mτ)`.
* **Theorem 4.1 (public-coin form).** `(A, R, sᵀA + eᵀ, C, sᵀC + e'ᵀ) ≈_c (A, R, uᵀ, C, u'ᵀ)` for
  `(A, R) ← TdSamp`, `σ ≥ τ^{c−1}·ω(√log λ)` and payload samples on `C` with narrower `σ'`.

**The gap factor.** A vector that TLWE protects has `‖e‖ ≳ (q/τ)√m·ω(√log λ)`. A vector the
trapdoor decodes has `‖e‖ ≤ q/(4mτ)`. Every design that uses the trapdoor both to decrypt valid
paths and as public data next to invalid paths must make the error jump by a factor of at least
`4 m^{1.5}·ω(√log λ)` between valid and invalid paths. The trapdoor cannot be told to stop at the
honest radius: the honest decryption algorithm is also an attack algorithm for all errors up to
`q/(4mτ)` (the same observation as PR #110).

## 2. What a per-path handle must be

Fix a statement `φ` and write `Y_w(ct)` for the value the decryptor computes on path `w` (before
decoding). A `2^128`-hop proof on a false statement (`pq-we-hybrid-count-barrier`, consequence 2)
needs, for each candidate `w*`, a step `H → H'` with:

1. **(LWE embedding)** a simulator `Sim` with `Sim(A*, s*A* + e*) ≡ H` and `Sim(A*, u) ≡ H'`, where
   `(A*, ·)` is a statement-independent LWE or TLWE instance;
2. **(locality)** the joint distribution of `(Y_v)_{v ≠ w*}` (with everything else in the view) is
   the same in `H` and `H'`;
3. **(noise is the path noise)** `e*` enters `Y_{w*}` as its additive noise, so the step is
   justified by `w*` being invalid and nothing else.

Conditions (2) and (3) say that `Y_{w*}` can move while every other path stays fixed. Their
information-theoretic shadow is **local freshness** of `w*` on the support of `Y(ct)`:

> for every `ct` there is a `ct'` with `Y_{w*}(ct') ≠ Y_{w*}(ct)` and `Y_v(ct') = Y_v(ct)` for
> all `v ≠ w*`.

Its linear shadow, when `Y_w(ct) = φ_w(ct)` is linear, is a direction `x` with `φ_{w*}(x) ≠ 0` and
`φ_v(x) = 0` for every other path `v`.

The owner's "per-path noise as LWE noise" is the statement that the **real** ciphertext has this
property at every invalid path, so that each hop is a direct LWE step on the scheme's own noise.

## 3. Entropy and rank bound

**`two_pow_le_card_of_locally_fresh` (Lean).** If every coordinate in `S` is locally fresh on a
nonempty finite set `P` of path-value families, then `|P| ≥ 2^{|S|}`. Proof by induction: split
`P` by the value at one coordinate. Each part stays fresh in the other coordinates, and freshness
at the split coordinate gives two nonempty parts.

**`fresh_paths_le_bits` (Lean).** If `Y : Ω → (paths → X)` and `|Ω| ≤ 2^N`, the number of
simultaneously locally fresh paths is at most `N`. This is "a poly-size ciphertext has poly
entropy" in exactly the form the hybrid needs. It is stronger than counting independent coordinates:
it needs no independence, only that no path is a function of the others.

**`linear_fresh_card_le_finrank` (Lean).** If the path values are linear maps `φ_w : V → U` on a
`K`-vector space `V` (the ciphertext mod a prime `q`), at most `dim V` paths can each have a
direction that moves only their own value. This is the simultaneous version of the one-sided
statements `Codes.card_fresh_le_finrank` and `LinearHop.card_killed_le_finrank`.

**Consequences.**

* `Def_WE_CircuitSAT_Capped` caps the cost, and so the ciphertext length, at `2^100` bits. So at
  most `2^100` of the `2^128` candidate paths are ever locally fresh at once, and with linear
  evaluation at most `dim ≪ 2^100`. Per-path fresh noise in the real ciphertext is impossible
  without any cryptographic assumption.
* **The structured family is as hard as LWE, with a global handle only.** In BGG+,
  `Y_w = s A_{U_w} + e H_{U_w}` (with `H` depending on the attribute, `pq-we-xwe-per-item-cost`), and
  in GGH15 the analogous product form holds. The whole family is a public function of
  `poly` fresh LWE samples, so it is pseudorandom (where it is not trivially structured) by **one**
  LWE hop. That hop changes every path at once, valid paths on true statements included. It is
  statement-independent and polynomial, so by `pq-we-hybrid-count-barrier` it cannot carry WE
  security. Its noises `e H_w` span at most `dim e` dimensions, and by the rank bound at most
  `dim e` paths can be switched individually.
* **What a `2^128`-hop chain therefore needs.** In hybrid `H_t` only the frontier path `t` (or a
  subcube) has to be fresh. That is compatible with the bounds, but only if `H_t` is a *different*
  poly-size ciphertext structure for each `t`. This is the "functionality-preserving re-encoding"
  of `pq-we-native-hop-designs` (counting argument, §6 there): pad merges, reroutes, the masked
  two-vector lemma. The noise is never the obstacle. The re-encoding is.

## 4. The owner's gate in normal form

Following `pq-we-tlwe-trapdoor-hint-zero-test` §2, every vector the decryptor computes is
`ct·L` for a public `L` (depending on `φ`, `w` and public data), up to rounding.

**Rounding adds nothing (`floor_sub_carry`, Lean).** `⌊a⌋ − ⌊b⌋ ∈ {⌊a − b⌋, ⌊a − b⌋ + 1}`.
Coordinatewise, rounding the master-side and constrained-side values and subtracting equals
rounding the unrounded difference, up to a carry of 1. A rounding-based PRF (BV15, BKM, LWR) moved
"into the error" by rounding therefore gates exactly what the linear difference
`ct·(L^O_w − L^C_w)` gates. Rounding errors themselves are at most `1/2`, far below any TLWE width.

**Decoding condition.** Write the difference as
`d_w = δ·A_w + Δ_w + ν_w`, with a secret part `δ·A_w`, a gate `Δ_w` (zero on valid paths), and
narrow noise `ν_w`. The public trapdoor of a matrix `A` decodes `d_w` iff

* (i) `A_w = A` up to the decoded linear map (alignment), and
* (ii) `‖Δ_w + ν_w‖ ≤ t ≤ q/(4mτ)`.

Security needs `Δ_w` in TLWE's regime on every invalid path (§1, gap factor). So the two halves of
the idea are separate:

* **closeness**: making `Δ_w` vanish exactly on valid `w` and be wide elsewhere;
* **alignment**: making `A_w` fixed, or trapdoored, without a per-`w` trapdoor.

The variants below achieve at most one of them.

## 5. Where the witness bits enter: a trilemma

The decryptor supplies `w`. The ciphertext must let it compute path `w` for every `w`, so the
ciphertext must contain material for both values of every bit, or the bits must select a public
computation.

**(W1) `w` selects the circuit.** The decryptor evaluates `U_w` on fixed encodings (BGG+, the BV15
CPRF). The input error difference evolves by a public linear map (`TLWE.eval_difference`), so
closeness cannot come from the evaluation mechanics and must be planted. The decoded matrix
`A_{U_w}` depends on `w`.

* *Per-`w` trapdoor:* the evaluation-oracle crux (`pq-we-evaluation-oracle-crux`), i.e. XWE
  enumeration.
* *Public-coin trapdoor at all `w`* (`A_i = B R_i + x_{0,i} G`): alignment holds everywhere, so the
  gate is purely `Δ_w = h·K_w` for a hidden `h` and public `K_w = L^O_w − L^C_w`. This is Case II of
  PR #78, a hidden-vector linear zero test, and `linear_closure` and `invalid_offset_cancel`
  apply.
* Moreover, the TLWE-wide input errors needed for public `R_i` make `e·H_w` wide. The `H`
  matrices depend on the attribute, so master and constrained wide parts do not cancel even at
  valid paths (PR #78 §3.1).

**(W2) `w` as an attribute under one secret.** The ciphertext holds `s(A_i − 0·G) + e` and
`s(A_i − G) + e'`. Their difference is `sG + (e − e')` (`KSplit.mix_leak`), which reveals `s`.
TLWE-wide `e` does not help: the decryptor must evaluate on both, so the errors must be narrow
enough to survive evaluation below `t`. Then `sG + (e − e')` with `‖e − e'‖ ≪ q/(4mτ)` decodes
under the gadget trapdoor.

**(W3) `w` as per-bit-value encodings.** Bit `i` with value `b` contributes its own piece
`f_i(b)`: secret, error and gate.

* *Additive composition* (sums of BGG+-type pieces, or linear key-homomorphism). Every component
  satisfies exact rectangle relations (`additive_rectangle`, Lean):
  `F(w) + F(w') = F(u) + F(u')` whenever `{u_i, u'_i} = {w_i, w'_i}` coordinatewise. In
  particular the gate is affine in `w`, `Δ_w = d + Σ_i w_i c_i`. **`affine_face_gap` (Lean):** if
  `d + c_1`, `d + c_2` and `d + c_1 + c_2` all have norm at most `t`, then `‖d‖ ≤ 3t`.
  * *Clause-local gates (an attack).* Take the statement to be a CNF over the witness bits (a
    special case of Circuit-SAT) and a clause-local gate: block `k` depends only on clause `k` and
    its literals, the natural additive design. Correctness on the satisfiable formula consisting
    of clause `k` alone forces block `k` to have norm at most `r` (the decoding radius) on its
    satisfying literal patterns. If clause `k` has at least two literals, fix the others to false:
    the violating pattern has block norm at most `3r`. Take a **false** CNF with no unit clause
    (for example any false 3-CNF). Every Boolean path has every block within `3r`, so
    `‖Δ_w‖ ≤ 3r·√K` against `r·√K` on a would-be valid path, i.e. a factor 3:
    * if the designer takes `r√K ≤ q/(12mτ)`, `TdInvert` itself decodes every invalid path. It
      returns the path's secret part, which is the payload whenever the payload is
      witness-independent (the design of §4), so the scheme is broken;
    * otherwise invalid errors are within a factor 3 of the honest radius, a factor about
      `4m^{1.5}/3` below the regime where TLWE (or anything else) is proven hard.
  * *General affine gates.* `affine_face_gap` says that at gap factor above 3 the set of small
    points is closed under completing a face of the cube with three small corners. So on every
    true statement whose satisfying set has three corners of a face, the fourth (invalid) corner is
    within `3r`, and the TLWE regime fails there. On false statements the lemma alone gives no
    attack. The encryptor then needs `φ ↦ (d, C)` to be a gap reduction from Circuit-SAT to a
    closest-vector problem on the cube, and the gate is a hidden-vector linear zero test (Case II).

* *Multiplicative composition* (matrix products, GGH15). This is PR #86:
  `affine_relation_kills_linear_pad` (relations among gated rows remove the wide error with the
  pad) and `cancel_prefix_closed` (wide errors can only gate dead prefixes).

## 6. The three requested variants

### V1. CPRF outputs moved into the error

* *Rounded outputs.* In BV15/BKM the constrained evaluator computes `⌊s·A_{C,w}⌉` itself, so the
  value is known and is not noise. Rounding a masked vector yields an error of at most `1/2`, and
  by `floor_sub_carry` it is validity-blind (§4).
* *FHE-carried PRF (the strongest form).* Use a secret with a known last coordinate,
  `s = (s̄, 1)`. Then `s·G·G^{-1}(β e_n) = β`, so BGG+ inner-product decryption of a public FHE
  ciphertext `γ_w = FHE.Eval(PRF(·, w), Enc(k))` against BGG+ encodings of `sk` yields
  `y_w = s·A_{IP,γ_w} − ⟨γ_w, sk⟩ + noise`, with `⟨γ_w, sk⟩ = β·PRF_k(w) + e_FHE`. This **does**
  put an exact, wide, pseudorandom `β·PRF(w)` into an LWE error. With a constrained side
  `γ^C_w = Eval(U(k, φ, w))`, which equals `PRF_k(w)` iff `C(φ, w) = 1`, the plaintexts agree
  exactly on valid paths. So the closeness half works.
  * *Alignment fails.* The decoded matrix is `Σ_j A_j G^{-1}((γ^O_{w,j} − γ^C_{w,j})G)`. It depends
    on the public ciphertexts `γ_w` (fresh per `w`), so this is Case I.
  * *Making it public-coin* (`A_j = B R_j`, with a TLWE sample `b = sB + e_B`) gives the public
    `R_γ`. Then `(y_γ − b R_γ)·G^{-1}(e_n) = −⟨γ, sk⟩ + (noise − e_B R_γ G^{-1}(e_n))`. With narrow
    `e_B` this is FHE decryption **at every path**, so the PRF is revealed and nothing is gated.
    With TLWE-wide `e_B` the masks `e_B R^O_γ` and `e_B R^C_γ` differ (different public `R`), so
    they do not cancel even on valid paths (`eval_difference`).
  * Taking identical maps `L^O_w = L^C_w` cancels the masks at every path, valid or not, and the
    gate collapses to the exact channel. That channel is a public linear image of the ciphertext,
    so the gate is again a hidden-vector linear zero test.
* *Mix-and-match.* `w` selects the circuit, so there is no mix of bit encodings (W1). The attack
  surface is the linear zero test: short combinations `Σ α_w K_w` that hit the hidden kernel.
  For pseudorandom `K_w` (bit decompositions of FHE ciphertexts) this is an SIS-like search over
  `2^128` structured columns, not obviously efficient. But no proof route exists: under exact TLWE
  every short public functional of the error is wide (PR #78 §4), so the step "structured error ≈
  TLWE error" is the whole WE security and is statement-dependent.

**Outcome:** closeness achieved, alignment impossible without a per-`w` trapdoor or a linear zero
test. No per-path handle, since all path values are linear in one ciphertext (§3).

### V2. Noise-as-message decoding with a TLWE hint at the final step only

This is the masked γ⊗-GGH15 leaf of PR #86. Decoding is exact (`μ_h` on every witness path), and
gated wide errors (`wide_gate`) are per-path in the sense that they vanish exactly on witness
paths. But they are linear in the gated row, so every affine relation removes them together with
the pad (`affine_relation_kills_linear_pad`), and they cannot sit at inner levels
(`cancel_prefix_closed`). By `linear_fresh_card_le_finrank` at most `dim` (GGH15 width times
levels) paths can be individually switched in one hybrid.

**Outcome:** correct and exact, no handle. The open lemma is unchanged: the overcomplete cut lemma
or masked two-vector lemma with `2^128` witness-indexed hops, which needs re-encoding.

### V3. Gadget-structured hints that decode only along a subspace

A hint that decodes `sA + e` only when the error's projection `π(e)` is small (a short basis of a
sublattice, or a gadget trapdoor for `A·P` only) makes the passing set
`{L : secret part aligned, ‖π(E L)‖ ≤ t}`. This set is closed under short combinations
(`linear_closure`), so it is a linear zero test on the hidden `π(E)`. "Reached iff the errors
match" means `K_w ∈ ker π(E)` for public `K_w`, i.e. hidden-kernel membership:

* the public-α shortcut and the Veronese linearization of PR #78 §3.3 apply;
* positional hybrids change at most `dim` times (`antitone_chain_few_changes`);
* only `dim` paths are individually switchable (`linear_fresh_card_le_finrank`).

If the projection is narrow enough to keep `π(E)` TLWE-wide, the hint inherits AJLW26's hardness
only for the whole `A`, which is not what is published. No theorem of AJLW26 covers a projected
trapdoor.

**Outcome:** no new handle. The construction is a GGH13-type hidden-lattice zero test with no
falsifiable statement-independent hardness.

## 7. Verdict and what remains

* **Barrier (theorem level for freshness).** No scheme has per-path fresh noise at more than `N`
  paths (`fresh_paths_le_bits`). With linear evaluation, which covers all lattice designs with
  rounding by `floor_sub_carry`, no scheme has more than `dim` individually switchable paths
  (`linear_fresh_card_le_finrank`). This holds for the real ciphertext and for every single
  hybrid. TLWE does not change it: it adds a decoding step after the linear evaluation.
* **Barrier (case analysis for the TLWE gate).** Closeness and alignment cannot both hold without
  a per-`w` trapdoor (W1/Case I), a single-secret mix (W2, `mix_leak`), an affine gate (W3 additive:
  broken when clause-local, `affine_face_gap`, and a linear zero test otherwise), or GGH15 (W3 multiplicative, PR #86). Every remaining
  option is a hidden-vector linear zero test (PR #78 Case II).
* **Security chains.** Every TLWE/LWE hop available in these designs has a statement-independent
  instance and switches all paths at once (the global handle). A `2^128`-hop chain needs
  hybrid-local freshness, which by §3 requires a different poly-size structure in each hybrid.
* **Weaker handles that do exist.**
  1. *Global:* `{sA_w + eH_w}_w` is pseudorandom from one LWE hop. It is useful for the
     statement-independent parts of a proof, and insufficient alone.
  2. *Bounded per-hybrid:* up to `dim` paths (a subcube's worth when the structure is
     prefix-aligned) can be switched by native LWE steps inside one hybrid. This is the
     `NativeHop` "native kills" of PR #108.
  3. *Gated wide leaf errors* (`wide_gate`, PR #86): exact per-path zero/wide behaviour at the
     leaf, linear in the gated row.

  All three leave the same open object: a statement-independent, functionality-preserving
  re-encoding step between positional hybrids.
* **Cost.** No design survives, so there is no estimate against `2^100`. For the record, V1 would
  need FHE evaluation of a PRF per path inside BGG+ (`log q` in the hundreds of thousands, as in
  `pq-we-xwe-per-item-cost`) before any security question.

## Lean nodes in this PR

| Theorem | Statement | Used in |
| --- | --- | --- |
| `NoiseHandle.two_pow_le_card_of_locally_fresh` | `S` locally fresh on nonempty `P` ⇒ `2^{|S|} ≤ |P|` | §3 |
| `NoiseHandle.fresh_paths_le_bits` | `|Ω| ≤ 2^N`, `S` locally fresh on the image of `Y` ⇒ `|S| ≤ N` | §3, §7 |
| `NoiseHandle.linear_fresh_card_le_finrank` | each `w ∈ S` has `x` with `φ_w x ≠ 0`, `φ_v x = 0` (other `v ∈ S`) ⇒ `|S| ≤ dim V` | §3, V2, V3 |
| `NoiseHandle.floor_sub_carry` | `⌊a−b⌋ ≤ ⌊a⌋−⌊b⌋ ≤ ⌊a−b⌋+1` | §4, V1 |
| `NoiseHandle.additive_rectangle` | `Σf_i(w_i) + Σf_i(w'_i) = Σf_i(u_i) + Σf_i(u'_i)` when the pairs agree up to order | W3 |
| `NoiseHandle.affine_face_gap` | `‖d+c₁‖, ‖d+c₂‖, ‖d+c₁+c₂‖ ≤ t ⇒ ‖d‖ ≤ 3t` | W3 |
