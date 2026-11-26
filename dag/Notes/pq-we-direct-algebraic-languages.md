---
title: Direct WE for algebraic NP languages (exact cover, regular syndrome decoding, subset sum, polynomial systems, group actions) - the one-gate relaxation attack and where each route ends
refs: [definition:WE, definition:WE_CircuitSAT, note:pq-we-summary-2026-11, note:pq-we-hybrid-count-barrier, note:pq-we-gap-structure-routes, note:pq-we-non-lattice-algebras, note:pq-we-proof-system-routes, note:pq-we-affine-syzygy-barrier, note:pq-we-new-directions, note:pq-we-multipass-ggh15, note:pq-we-shallow-split-arrangements, note:pq-we-evaluation-oracle-crux, theorem:AdvancedEncryption.WE.CertDual.dichotomy, theorem:AdvancedEncryption.WE.Hybrid.hardAt_chain, theorem:AdvancedEncryption.WE.Direct.nand_gadget_affine_closure, theorem:AdvancedEncryption.WE.Direct.rsd_nand_relaxation]
tags: [witness-encryption, attack, barrier, dead-end, strategy]
---
Design-AI sub-task on `Def_WE_CircuitSAT` (NAND Circuit-SAT, 128-bit witness, `2^12` gates,
`λ = κ = 128`). The aim was to leave XWE / ABE enumeration and build WE **directly** for an
NP-complete language with rich algebraic structure, with polynomial-size ciphertexts (at most about
`2^60`). The 4096-gate instance should reduce to that language with small blow-up, encryption and
decryption should be natural for the structure, and the witness-indexed proof should have hops that
are instances of an allowed assumption. Two lemmas are proved in Lean (complete proofs, Mathlib
only): `AdvancedEncryption.WE.Direct.nand_gadget_affine_closure` and
`AdvancedEncryption.WE.Direct.rsd_nand_relaxation`. The rest is informal, checked step by step by
the submitting agent. No second model was used.

## 0. Bottom line

* **Every encoding that is linear in per-gate local data is broken on false statements, in
  polynomial time, by a relaxed witness that violates one gate.** This covers exact cover with
  noisy-linear (LWE or LPN) encodings instead of multilinear maps, subset sum and knapsack with a
  final rounding, regular syndrome decoding with dual-LPN or dual-LWE encryption, and the degree-2
  Nullstellensatz scheme of `pq-we-new-directions`. The reason is one identity: the four valid
  NAND triples affinely span `{0,1}^3` with coefficient `ℓ₁` norm at most 5 (Lean). Multilinear maps
  in GGSW13 forbid exactly this, because exponent vectors cannot be negative and additions at the
  top level do not cancel.
* **For polynomial systems** we answer the first cryptanalysis target of `pq-we-new-directions`
  §2.6 at degree `D = 2`: every false circuit has an explicit pseudo-solution made of three
  evaluation points (coefficients `−1, 1, 1`), so CD-LWE(2) is false. The check is complete under a
  mild normal-form condition (C) and sketched in general. At `D = 3` this three-point object fails, and
  we compute why (§3.3). The ciphertext budget `2^60` allows only `D ≤ 5`, so the open question is
  now short pseudo-solutions at `D ∈ {3, 4, 5}`.
* **Group actions (3-coloring, clique)** and **LPN plus local PRG** add nothing beyond
  `pq-we-non-lattice-algebras` (§4).
* **No new candidate beats MP2/MP3.** Only multiplicative (product) encodings survive the
  relaxation attack. With standard assumptions the only lattice product available is GGH15, and a
  GGH15 chain over an exact-cover or syndrome-decoding instance is a branching program over the
  wires. That is the MP2 line of `pq-we-multipass-ggh15` again, with the same open lemma (§5).
  A further structural cost: the direct languages blow the witness up from 128 input bits to the
  whole wire assignment (8320 bits for regular syndrome decoding). A hybrid indexed by those
  witnesses costs `2 · 8320` bits by `AdvancedEncryption.WE.Hybrid.hardAt_chain`, so the walk must
  still be indexed by the 128 input bits. The encoding must then "know" that the wires are
  determined by the inputs, which means circuit evaluation (BGG+ or a GGH15 branching program).

## 1. The reduction: NAND Circuit-SAT to regular syndrome decoding (and exact cover)

Let the circuit have `n = 128` inputs and `G = 4096` NAND gates. Variables over `F_2`:

* for each input `i`, a pair `(p_i, p̄_i)` with `p_i + p̄_i = 1`;
* for each gate `g` with input wires `a, b` and output wire `c`, a block
  `u_g = (u_{00}, u_{01}, u_{10}, u_{11}) ∈ F_2^4` (columns indexed by the input pair), with
  `Σ u_g = 1`, `u_{10} + u_{11} = val(a)`, `u_{01} + u_{11} = val(b)`. Here `val(x)` is `p_i` for
  an input wire and `u'_{00} + u'_{01} + u'_{10}` (the producer's output) for a gate wire;
* the output constraint `val(out) = 1`.

A **regular** solution has exactly one 1 in each block (pair or gate block). Regular solutions
correspond one-to-one to satisfying assignments: one-hot blocks force each gate to the NAND of its
inputs. Sizes: `N = 4G + 2n = 16 640` columns, `n + G + 2G + 1 = 12 417` rows, and regular weight
`t = G + n = 4224`. This is a **regular syndrome decoding** instance (one non-zero per block, as in
the FSB hash and the silent-OT literature), with a structured, statement-dependent parity-check
matrix `H_φ`. Read over `Z` (`u ∈ {0,1}`), the same system is a 0/1 exact-cover-type system:
"exactly one of each block" plus equalities between disjoint sums. Exact cover proper, and subset
sum through base-`B` digits, follow by standard local gadgets with polynomial blow-up (not worked
out here). Section 2 needs only that the gadgets are local with an affine wire interface.

## 2. The one-gate relaxation attack on linear encodings

### 2.1 The two lemmas (Lean, complete proofs)

**`nand_gadget_affine_closure`.** Let `L : V →+ W` be any additive map (the constraint map of a
linear encoding) and let `sol x y` be block solutions for the four valid triples, with
`L(sol x y) = T(x, y, NAND(x, y))` for an affine `T(a, b, c) = t0 + a t1 + b t2 + c t3`. Then every
triple `(a, b, c) ∈ {0,1}^3` is reached by an integer combination with `ℓ₁` norm at most 5:

| triple | combination of `sol(x, y)` |
| --- | --- |
| `(0,0,0)` | `2·(0,0) − (0,1) − (1,0) + (1,1)` |
| `(0,1,0)` | `(0,0) − (1,0) + (1,1)` |
| `(1,0,0)` | `(0,0) − (0,1) + (1,1)` |
| `(1,1,1)` | `−(0,0) + (0,1) + (1,0)` |

The coefficients sum to 1, so the combination is affine and works for every affine gadget, over
`Z`, `Z_q` or `F_p`.

**`rsd_nand_relaxation`.** In the `F_2` encoding of §1, for **any** triples `(a_g, b_g, c_g)`
(consistent or not), the block constraints have a solution of total weight
`G + 2 · #(violated gates)`. A valid gate costs weight 1, a violated one weight 3 (the `4 × 4`
system is invertible over `F_2`, so the block is unique).

### 2.2 The attack

Take a false `φ` and any input `α`. Evaluate honestly; the output gate yields 0. Force its output
to 1. Only the output gate is violated, so the system of §1 has an `F_2` solution `x̃` of weight
`t + 2` (from `rsd_nand_relaxation`). Over `Z`, the closure combination `−(0,0) + (0,1) + (1,0)`
of the output block gives an integer solution of `ℓ₁` norm `t + 2`. Both are computed in linear
time.

* **Dual-LPN / dual-LWE WE for regular syndrome decoding.** `Enc(φ, μ)`: `c = sᵀH_φ + eᵀ`,
  `k = sᵀy_φ + e' + μ·Δ`. `Dec(x)`: `k − ⟨c, x⟩ = μΔ + e' − ⟨e, x⟩`. Over `F_2` with
  `e ← Ber(τ)^N`, the honest bias is `(1 − 2τ)^t / 2`, so correctness needs `τ ≲ 1/t ≈ 2^{-12}`.
  The relaxed `x̃` has bias `(1 − 2τ)^{t+2} / 2`, a factor `(1 − 2τ)^2 ≈ 1` smaller: **decryption
  works on every false statement.** Over `Z_q` the noise grows from `‖x‖₁ = t` to `t + 2`.
* **Exact cover with noisy-linear encodings** (GGSW13's language, multilinear map replaced by
  LWE/LPN): publish `c_T = ⟨s, Σ_{j ∈ T} a_j⟩ + e_T` for every set `T` and
  `c* = ⟨s, Σ_j a_j⟩ + e* + μΔ`. A cover `S` decrypts through `c* − Σ_{T ∈ S} c_T`. Any integer `x`
  with `M x = 1` (`M` the incidence matrix) decrypts equally, with noise `‖x‖₁ B`. For instances
  obtained from circuits by local gadgets with an affine wire interface, the closure lemma gives
  such an `x` with one violated gate and `‖x‖₁ ≤ |S| + 4`.
* **Subset sum / knapsack with a final rounding.** The same: the rounding is applied to the
  combined value, so it accepts every short integer combination that hits the target, and the
  relaxed one is short.
* **What the multilinear map did.** In GGSW13 a set is encoded at level `|T|` as `Π_{j ∈ T} a_j`.
  A product of encodings has exponent vector `M x` with `x ∈ N^m`, and sums at the top level do not
  cancel generically. The decryptor's target `Π_j a_j` is therefore reachable only by `M x = 1`
  with `x ≥ 0`, which is exact cover itself. Noisy-linear encodings turn exponents into signed
  coefficients, and that is the relaxation. The lattice replacements are (a) NTRU-type graded
  encodings (GGH13), which are not an allowed assumption and are subject to zeroizing attacks,
  and (b) GGH15, which is non-commutative: it forces an order on sets or elements, hence an
  automaton (§5).

This is a concrete, explicit instance of the "induced lattice gap" of `pq-we-gap-structure-routes`
§4: the relaxation lattice `{x : M x = 1}` always contains a short vector for circuit-derived
instances, so the gap is not merely unproven but absent.

### 2.3 What would be needed to escape

A gadget whose invalid-triple blocks are far from every valid combination would need a *global*
weight gap (a PCP-style Gap-RSD). A per-gate gap is impossible by the closure lemma: an invalid
block costs at most `5×` (`3×` over `F_2`) a valid one, and only one gate needs to be violated. For
the noise to separate weights `t` and `(1 + γ)t`, one needs `(1 − 2τ)^{γt} = 2^{-λ}` while
`(1 − 2τ)^t` is noticeable, so `γ ≥ λ / O(log)`. That is a super-logarithmic gap, not known to be
NP-hard (`pq-we-gap-structure-routes`, minimum-distance row). Even then, security is a decoding
assumption on the statement's code (statement-dependent), and a poly-hop proof would put the
language in SZK (`pq-we-hybrid-count-barrier`).

## 3. Polynomial systems (MQ / Nullstellensatz view)

### 3.1 "Random element of the ideal plus μ"

`Enc(φ, μ) = Σ_i r_i f_i + μ` (degree `≤ D`, `r_i` uniform), decrypted by evaluation at the witness,
is exactly the certificate-dual scheme of `pq-we-new-directions` §2. By
`AdvancedEncryption.WE.CertDual.dichotomy` it is perfectly hiding if `1 ∈ I_D` (a degree-`D`
Nullstellensatz refutation exists). Otherwise it is broken by linear algebra in the clear, and
under an LWE mask by any *short* pseudo-solution. No MQ assumption instance ever appears: MQ
hardness is about solving random systems, while here the system is the statement and, for false
statements, has nothing to solve. Security is ideal membership, which is statement-dependent. The
compressed variant (give the decryptor an evaluator for `x ↦ μ + r(x)(1 − φ(x))` with `r` a PRF)
is literally the evaluation-oracle crux (`pq-we-evaluation-oracle-crux`).

Size. For a PRG `Prg` secure against `N_D`-time adversaries, most statements "`y ∈ Im(Prg)`" with
random `y` have no degree-`D` refutation: otherwise linear algebra in time `poly(N_D)` would find
one for random `y` and never for pseudorandom `y`, which distinguishes. So the statistical regime
needs `N_D` above the PRG's security. With the ciphertext budget `2^60` the table of
`pq-we-new-directions` §2.1 gives `D ≤ 5` (`log₂ N_5 = 53.3`).

### 3.2 Degree 2: an explicit pseudo-solution for every false circuit (CD-LWE(2) is false)

Setting of `pq-we-new-directions` §2.1: variables for inputs and gate outputs, `f_g = z_g + x_g y_g − 1`,
`z_out − 1`, multilinear monomials of degree `≤ D`, columns `m·f` with `deg(m f) ≤ D`. The
decryptor uses `⟨v_a, c⟩`, where `v_a` holds the monomial values at a Boolean point.

Take a false `φ`, any input `α`, and suppose first that the output gate reads two distinct wires
`k ≠ l`. Its honest output is 0, so the honest values are `w_k = w_l = 1`. For `x, y ∈ {0,1}`, let
`P_{xy}` be the Boolean point obtained by forcing `z_k = x`, `z_l = y` and `z_out = 1`, and
recomputing every other wire honestly from `α` and the forced values. Set

`h = v_{P_{10}} + v_{P_{01}} − v_{P_{00}}`,

which is the `(1,1,1)` row of the closure table. Check against every column at `D = 2`, under
condition (C) below:

* `h(1) = 1`;
* gates other than `out`, `prod(k)` and `prod(l)` hold at every `P_{xy}` (they are recomputed),
  and `(z_out − 1)·m` vanishes at every point;
* `f_out = 1 + xy − 1 = xy` is 0 at `10`, `01` and `00`;
* if `k` is an input variable there is no producer constraint. Otherwise suppose `prod(k)` is a
  NAND with two distinct inputs, so its constraint has degree 2 and only `m = 1` occurs at `D = 2`.
  The inputs of `prod(k)` are ancestors of `k`, so they do not depend on `x`; they depend on `y`
  when `l` is an ancestor of `k`. So `f_{prod(k)} = x + π_k(y) − 1`. With
  `λ = (λ_{00}, λ_{01}, λ_{10}, λ_{11}) = (−1, 1, 1, 0)` we have `Σ λ x = 1` and
  `Σ λ π_k(y) = (λ_{01} + λ_{11}) π_k(1) + (λ_{00} + λ_{10}) π_k(0) = π_k(1)`. Hence
  `h(f_{prod(k)}) = 1 + π_k(1) − 1 = π_k(1) = 0`, because `π_k(1)` is the honest value and
  `w_k = 1`. The same holds for `prod(l)`.

So `h` vanishes on the degree-2 Nullstellensatz span and `h(1) = 1`. The checks above are complete
under the condition **(C)**: the output gate has distinct inputs, each an input variable or the
output of a NAND with two distinct inputs. The other shapes are handled as follows (sketch,
checked case by case but not written out in full):

* NOT gates (`NAND(a, a)`, multilinear constraint `z + z_a − 1` of degree 1, hence multiplied by
  variables at `D = 2`) between `k` and its NAND producer: force the whole NOT chain alternately
  (`x, 1 − x, …`). Every NOT constraint then vanishes pointwise, and the affine argument above
  applies at the first NAND with distinct inputs, or at an input variable. Without this, the
  three-point `h` fails: `Σ λ z_l (x + z_a − 1) = −1`.
* If the output gate is a NOT (`NAND(i, i)`), force `z_i = 0` and `z_out = 1` and flip one level
  down, at `prod(i) = NAND(k, l)`, with pseudo-moments `(E x, E y, E xy) = (w_k, w_l, 1)`. Since
  `w_i = 1`, `(w_k, w_l) ≠ (1, 1)`, and the unique `λ` is the closure-table row of the invalid
  triple `(w_k, w_l, 0)`. The same affine argument gives `h(f) = f(honest) = 0` for the producers.
* If the two forced chains meet, `φ` is constant 1 (satisfiable) or the output reduces to the NOT
  case. A chain of NOT gates down to an input would make `φ` satisfiable, so the recursion stops.

Noise: `‖h‖₂ ≤ ‖v_{P_{10}}‖₂ + ‖v_{P_{01}}‖₂ + ‖v_{P_{00}}‖₂`, at most three times the largest
honest decryption vector. Correctness must hold for every witness, so the parameters cover the
worst Boolean point; with `2^{-128}` honest failure (about `13σ` of slack) the attacker keeps more
than `4σ`, hence advantage close to 1. **CD-LWE(2) is false**: proved by hand under (C), and sketched for every
false circuit.

### 3.3 Degree 3: why the three-point object fails

At `D = 3` the columns include `m · f_{prod(k)}` for variables `m`. Take `m = z_l`: the values of
`y (x − 1)` at `10`, `01`, `00` are `0, −1, 0`, so `h = −1 ≠ 0`. Pseudo-moments must also satisfy
`E[y (x − 1)] = 0`, i.e. `E[xy] = E[y] = 1`, which contradicts `E[xy] = 0` from `f_out`. A degree-3
pseudo-solution must also violate the producers, by forcing their inputs. This is a
Sherali–Adams-type local distribution on the backward cone of depth about `D/2`. We expect it to
exist with support `3^{O(D)}` when the top cone is tree-like (no reconvergent fan-out), but that is
unverified. Reconvergence is exactly where a designer could try to make low-degree pseudo-solutions
long. **Precise open question:** for `D ∈ {3, 4, 5}`, does every false 128-input, 4096-gate
circuit have a pseudo-solution of `ℓ₂` norm `poly(D) · √N_D`? If yes, the certificate-dual line is
dead inside the `2^60` budget; if a circuit transformation forces norm `≥ q / σ`, CD-LWE(`D`)
becomes a concrete statement-dependent assumption (still excluded by the task's rules).

## 4. Group actions, and LPN plus local PRGs

* **3-coloring or clique over a regular group action.** An edge constraint between two colored
  vertices is a two-term relation `ℓ_u − ℓ_v = g`, which a generic algorithm can test. The key must
  depend on *all* edges, and combining `≥ 3` hidden elements is the parallelization problem. So
  the honest decryptor cannot compute it, and the scheme is not even correct
  (`pq-we-non-lattice-algebras` §1). Dead.
* **LPN for the linear layer, Goldreich PRG / local predicates for gates.** If the decryption is
  linear in the LPN data and the gate predicates are evaluated in the clear on witness bits, the
  relaxation of §2 applies to the linear layer. If the predicates act on ciphertext bits, the
  decryption has constant degree and falls under the degree-`D` affine-syzygy argument
  (`pq-we-affine-syzygy-barrier`). The closure lemma does **not** directly cover decryptions that
  are multilinear products over blocks: there a relaxed block expands into terms with
  wire-inconsistent neighbours, and those terms need not decrypt. This is the multiplicative case
  of §5.

## 5. Best candidate and the precise gap

Only **products over the witness** survive §2. With allowed assumptions the product structure is
GGH15 (LWE), applied to the exact-cover or syndrome-decoding instance as an automaton:

* Element-major order: each element `j` is a 2-state "covered exactly once" automaton, and the
  per-set choice must be consistent across the elements of the set. This consistency is the mixing
  problem, which MP2/MP3 handle with equality clauses between passes
  (`pq-we-multipass-ggh15`).
* Gate-major order: blocks are read in topological order, and the state carries the live wire
  values, so the width is `2^{cutwidth}`. For single-prefix flips the fixed-cut lemma of
  `pq-we-shallow-split-arrangements` gives width `≥ 2^{64}`.

In both orders the hybrid must run over the 128 input bits, not over the 8320-bit block witness
(§0). Reading only input bits is a branching program for `φ`, i.e. MP2/MP3 itself. **Precise
remaining gap:** unchanged from `pq-we-summary-2026-11` §4, the masked-leak lemma of the MP2/MP3
threshold reroute (or the weaker equality-cube flip). The direct-language route contributes a
proof that the additive alternatives are not merely unproven but broken, and one new concrete
target: short Nullstellensatz pseudo-solutions at degrees 3 to 5 (§3.3).

| Route | Scheme | Reduction size | Per-hop assumption | Attack | Verdict |
| --- | --- | --- | --- | --- | --- |
| Regular SD + dual LPN/LWE | `sᵀH_φ + e`, `sᵀy_φ + μΔ` | `12 417 × 16 640`, weight 4224 | none possible | one-gate relaxation, weight `t + 2` (Lean) | broken |
| Exact cover / subset sum + noisy-linear encodings | additive set encodings, final rounding | constant factor over RSD | none possible | closure, `‖x‖₁ ≤ |S| + 4` (Lean) | broken |
| Exact cover + multiplicative encodings | GGH13 / GGH15 | as above | GGH13 not allowed; GGH15 → MP2 hops | zeroizing (GGH13) | reduces to MP2 |
| Ideal + μ (Nullstellensatz), `D = 2` | certificate-dual | `N_2 = 2^{23.1}` | statistical only if refutable | 3-point pseudo-solution (§3.2) | broken |
| Same, `D ∈ {3,4,5}` | certificate-dual | `N_5 = 2^{53.3}` | statement-dependent CD-LWE(`D`) | open (§3.3) | excluded assumption; open attack |
| Group action, 3-coloring/clique | edge key agreement | linear | — | parallelization needed | not correct |
| LPN + local PRG | linear layer + NC0 | linear | — | §2 / degree-`D` syzygy | dead or covered |
