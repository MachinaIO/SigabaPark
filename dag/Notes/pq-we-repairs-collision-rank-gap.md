---
title: Repair attempts for three dead WE candidates (kernel collision, rank-one decomposed LWE, rank gap as an LWE-dimension gap) and where each stops
refs: [definition:WE_CircuitSAT, definition:DecomposedLWE, note:pq-we-matrix-collision-barrier, note:pq-we-gap-structure-routes, note:pq-we-evaluation-oracle-crux, note:pq-we-rank-gap-lattice-barriers, note:pq-we-ggh15-chain-verdict, theorem:AdvancedEncryption.WE.Repair.gadget_decode_unique]
tags: [witness-encryption, candidate, attack, dead-end, repair]
---
Design-AI sub-task: revisit candidates declared dead and try hard to repair them, for
`Def_WE_CircuitSAT` from falsifiable statement-independent post-quantum assumptions (no iO, no
evasive LWE, no statement-dependent assumption). This note covers three candidates whose
obstruction looked local: the kernel collision on a switch wire and the rank-one access of
decomposed LWE (both in `pq-we-matrix-collision-barrier`), and "rank gap as an LWE-dimension gap"
(`pq-we-gap-structure-routes`, §4, candidate 1). For each, it restates the obstruction exactly,
lists the repairs tried, and says where each stops. The fourth candidate (positional GGH15) is the
subject of the companion note `pq-we-ggh15-row-partitioned-trapdoors`, where all three repairs
below end up. Arguments are informal, except the one Lean theorem
`AdvancedEncryption.WE.Repair.gadget_decode_unique` (complete proof in this PR).

## 1. Kernel collision on a switch wire

**Obstruction (exact).** The candidate needs a public short `Δ` with `A_{U_w} Δ = 0` for all
`w`, obtained by ending `U_w` with a multiplication by a constant-`1` wire of matrix `C` and taking
`P Δ = 0` for `P = G^{-1}(C)`. Attack 1: a low-rank `Δ` leaves columns of `k'_b − k_b = sᵀG(I − Δ) +
noise` equal to columns of `sᵀG`. Attack 2: `A_g Δ = 0` holds for **every** circuit `g` ending with
the same gate, whatever its value, so `g = (x_1 ∨ ¬x_1) ∧ 1_C` decrypts.

Repairs tried:

* **K1. Full-rank `Δ`.** Take `Δ` a short combination of many short kernel vectors of `P` with
  `I − Δ` of full rank but with no short inverse. Then `sᵀG(I − Δ) + e` has no column of `sᵀG`
  in clear, and decoding needs a short preimage basis of `G(I − Δ)`, which is not implied by
  `Δ` short. Attack 1 seems to be avoided. **Stops at attack 2**, which does not use the rank of `Δ`.
* **K2. Last factor from an attribute wire** (multiply by an attribute bit fixed to `1` by the
  encryptor, instead of a constant wire). The adversary multiplies by the same attribute wire.
  **Dead (attack 2).**
* **K3. Witness-dependent last factor `P_w`** (the last gate of `U_w` selects one of a few factors
  by bits of `w`). With a few factors a common kernel exists, but the constant-`1` circuit ending
  in any one of them collides. With many factors the common kernel is `{0}` generically.
  **Dead.**
* **K4. Approximate collisions** (`A_{U_w} Δ` small instead of zero, so that only
  `sᵀ A_{U_w} Δ` is small). BGG+ evaluation applies `G^{-1}` after every multiplication, which is
  discontinuous. An approximate collision of the evaluated matrices must already be exact before
  the last `G^{-1}` layer, which brings back K1 to K3. **Dead.**
* **K5. Hidden `Δ`.** The decryptor multiplies by `X' = G^{-1}(A_b) − Δ`, so `X'` is public, and
  so is `Δ = G^{-1}(A_b) − X'`. **Dead.**
* **K6. Restrict which circuits can be evaluated.** Attack 2 works because BGG+ lets anyone
  evaluate any circuit on the fixed attribute `φ`. The only way found to restrict evaluation to the
  family `{U_w}` is to swap the roles: the attribute is the decryptor's `w`, and the circuit `φ` is
  fixed by the encryptor inside a key `K_φ ← [A_φ − G | B']^{-1}(u)`. A key for `A_φ` does not help
  for any other circuit's matrix, so attack 2 disappears. Encoding the decryptor's `w` needs either
  both encodings `sᵀA_i`, `sᵀ(A_i − G)` of each bit (which gives `sᵀG`) or one secret per
  candidate `w`, compressed as products along a read-once chain. The latter is the GGH15 + BGG+
  leaf of `pq-we-ggh15-chain-verdict`, point 4. **Moved to the companion note.**

## 2. Rank-one access in decomposed LWE

**Obstruction (exact).** Decryption needs `sᵀA_u` for the witness-dependent `u`. Any access
mechanism that works for every `u ∈ {0,1}^t` gives `sᵀA_{e_i}B_j`, and `y_{ii} − sᵀA_iB_i = sᵀG +
small`. The attack uses only that all `y_{ij}` share `s` and that short combinations of noisy
encodings are again noisy encodings.

* **D1. Access only for certificate vectors `u ∈ U_φ`.** With Hair–Sahai's reduction, `U_φ` is the
  set of `u(w)` over candidate witnesses. The encryptor cannot list it, and granting access to
  `sᵀA_{u(w)}` only when `φ(w) = 1` is witness encryption itself. **Circular.**
* **D2. Restrict `u` to a code (minimum distance, no unit vectors).** Linear closure is over all
  short integer combinations. The attacker does not need `e_i`, only some `u` whose split
  `A_u = Σ u_i A_i` it knows. A code `U` with `0, e_i ∉ span(U)` but `U` spanning a sublattice
  that contains two vectors differing in one coordinate gives `e_i` back. Avoiding that for all
  pairs while keeping every Hair–Sahai certificate is a statement-dependent condition. **Dead.**
* **D3. One secret per candidate `u`** (blocks linear closure, which needs a common secret). This
  needs exponentially many secrets, compressed as products: the GGH15 path secrets again.
  **Moved to the companion note.**

## 3. Rank gap as an LWE-dimension gap

**Obstruction (exact).** Publish `y_j = P M_j s + e_j` (`j ≤ t`, `P ∈ Z_q^{k×m}`). A certificate
`Σ a_j M_j = u vᵀ` gives `Σ a_j y_j = (Pu)(vᵀs) + Σ a_j e_j`, a rank-one instance. Hair–Sahai's
coefficients `a_j ∈ F_p` with `p ≈ 2^m` make `Σ a_j e_j` large. Small coefficients bring back linear
closure, and a polylogarithmic rank gap gives at most a quasi-polynomial LWE gap.

* **R1. Gadget-decompose the coefficients.** Publish `y_j^{(b)} = 2^b P M_j s + e_j^{(b)}` for
  `b < ⌈log q⌉` and combine with the bits of `a_j`. Then `Σ_{j,b} a_{j,b} y_j^{(b)} = P(u vᵀ)s +
  small`. **Broken:** noisy gadget encodings of one value are uniquely decodable
  (`AdvancedEncryption.WE.Repair.gadget_decode_unique`: if the error differences stay below
  `2^{k−1}`, two values with the same encodings agree mod `2^k`; greedy top-bit-first decoding
  finds the value). So `P M_j s` is recovered exactly for every `j`, and then `s` by linear algebra.
  *Masked variant* `y_j^{(b)} = A_{j,b} r + 2^b P M_j s + e`: the decryptor must cancel
  `Σ a_{j,b} A_{j,b} r` for a witness-dependent binary `a`, which is the target-cancellation object
  of `pq-we-evaluation-oracle-crux`. *Masked with `2^b A_j r`*: gadget decoding returns
  `A_j r + P M_j s` exactly, a noiseless linear system, solved by Gaussian elimination once the
  number of published values exceeds the number of unknowns. **Dead in all three forms.**
* **R2. A different NP-hardness reduction with small certificate coefficients.** We know of none
  for a rank-one YES side. The diagonal embedding of codes gives weight-`d` diagonal YES matrices,
  not rank one. Even if one existed, the scheme is one short integer combination of noisy samples
  on public matrices, so the unifying reduction of `pq-we-gap-structure-routes` (§4) applies. Concretely, the attacker may use
  *any* short `c = (c_j)` with `Σ_j c_jᵀ P M_j = 0 (mod q)`, not only the tensor form
  `c_j = a_j λ` that the decryptor uses. By pigeonhole such `c` with entries in `[−B, B]` exist as
  soon as `(B + 1)^{kt} > q^m`, whatever the ranks. The rank gap only controls tensor-form vectors,
  for which the length gap is about `q^{(R−1)/k}`. Below the pigeonhole bound the matrix
  `[P M_j]_j` has full row rank generically, the samples are statistically uniform except for the
  planted dependencies, and we are in the GapSVP row of that note: the NP-hard range needs a
  statement-dependent assumption. **Dead.**
* **R3. Secret `P` (the bilinear form `sᵀ M_j r` of Hair–Sahai).** The decryption test also needs
  `Σ u_i x_i ≈ P u`, so noisy columns `x_i = P e_i + e'_i` are published, and `P` is public up to
  noise. The scheme becomes R2 with a short secret (Hair–Sahai's `r ∈ [m]^m`) and noise `E' M_j s +
  e_j`. **Dead (same argument).**
* **R4. Rounding (LWR) instead of noise.** Decryption is still one short combination followed by
  rounding, and rounding is deterministic noise. **Dead (same argument).**
* **R5. Add a witness-indexed walk.** Hair–Sahai's reduction is explicit (`w ↦ a(w), u(w),
  v(w)`), so a false statement gives the local fact `u(w)v(w)ᵀ ∉ S` for each `w`. It is exactly as
  local as `φ(w) = 0` and adds no hop mechanism. All `y_j` share `s` and `P`, so there is no
  candidate-local data to switch. Per-candidate secrets again lead to GGH15. **Moved to the
  companion note.**

The label-cover candidate of the same note (§4, candidate 2) falls under the same unifying
reduction: its secrets cancel for every small *signed* integer solution of the projection
equations, a lattice problem in the public data. Making the uniform fractional labeling
infeasible (non-regular projections) only moves the attack to other short integer solutions, and
an instance family whose NO side has only long ones is again the statement-dependent lattice row.

## Summary

| Candidate | Repairs | Where it stops |
| --- | --- | --- |
| Kernel collision | K1 full-rank `Δ`; K2 attribute wire; K3 witness-dependent factor; K4 approximate; K5 hidden `Δ`; K6 swap circuit and attribute | K1–K5: attack 2 (collision is a property of the circuit's shape). K6 survives attack 2 and becomes the GGH15 + `K_φ` leaf |
| Rank-one decomposed LWE | D1 certificate-only access; D2 codes; D3 per-candidate secrets | D1 circular (is WE); D2 linear closure; D3 becomes GGH15 |
| Rank gap as LWE dimension | R1 gadget coefficients (3 forms); R2 small-coefficient reductions; R3 secret `P`; R4 LWR; R5 walk | R1 broken by gadget decoding (theorem); R2–R4 by the unifying reduction (short non-tensor dual vectors, or statement-dependent GapSVP); R5 becomes GGH15 |

All three candidates fail for one reason. A common secret across candidate witnesses, together
with closure of noisy encodings under short combinations, lets the attacker form what the
decryptor forms without a witness. Every repair that removes the common secret ends at
per-candidate secrets compressed along a read-once chain, with the statement fixed in a leaf key.
The companion note `pq-we-ggh15-row-partitioned-trapdoors` pushes that shape further.
