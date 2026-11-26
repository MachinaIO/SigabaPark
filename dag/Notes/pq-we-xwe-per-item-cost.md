---
title: Per-item cost of LWE-based XWE for WE_CircuitSAT - noise, depth, premise and word model; padding gives N about 2^128.6, lattice XWE wins only at low asymmetric level
refs: [definition:WE, definition:WE_CircuitSAT, theorem:AdvancedEncryption.WE.Hybrid.hardAt_chain, note:pq-we-hybrid-count-barrier, note:pq-we-split-witness-abe, note:pq-we-concrete-regime-constructions, note:pq-we-decryptor-attribute-dead-end, note:we-circuitsat-bruteforce-explicit-cost]
tags: [witness-encryption, abe, bgg14, cost-estimate, noise, barrier]
---
Design-AI sub-task (gg) for `WE_CircuitSAT` (`m = 128` witness bits, `2^12` NAND gates,
`λ = κ = 128`, `N = time(Enc) + time(Dec) + descLen`). Open PR #83 instantiates the 2-split XWE of
Brakerski–Jain–Komargodski–Passelègue–Wichs (ePrint 2017/874, Thm. 3.2) with ring BGG+ KP-ABE:
`d = 2^25`, `log q ≈ 287 638`, one key ≈ `2^76` word operations, `N ≈ 2^147.7`. Open PR #87 shows that
more slots do not help, because the total exponent is about `(128 + Σ per-item exponents)/k`.
This note asks how far the **per-item** cost can go down, with correctness proved for every
4096-gate circuit. Allowed: plain, Ring and Module LWE and their circular variants, succinct LWE,
decomposed LWE and TLWE. Excluded: iO, evasive LWE, local mixing, statement-dependent assumptions.

Three theorem nodes with complete proofs come with this note (not in `refs` because they are not
merged yet): `AdvancedEncryption.WE.Reach.hardAt_of_take`, `AdvancedEncryption.WE.Noise.slpBound_le_alevel`
and `AdvancedEncryption.WE.Premise.hardAt_of_reduction`. The numbers come from a script that reproduces
PR #83's optimiser (its `2^147.7` row is reproduced exactly) and checks every premise with the
repository's Python mirror of the lattice estimator (`python/lwemodel`, primal uSVP).

## 0. Summary

| Item | Result |
| --- | --- |
| **Padding baseline (new, assumption-free)** | `Enc(φ, β) = 0^P ‖ β` with `P ≈ 2^127` (encoded position `≥ 2^128`) is false-statement secure in the machine model by `hardAt_of_take`, so `N ≈ 2^128.6`. Every WE design has to beat this, not `2^188`. |
| Worst case, PR #83 accounting (`ℓ∞` noise) | `N = 2^147.7` (reproduced) |
| Worst case, best found here (spectral noise, re-randomised constants, lazy reduction) | `N ≈ 2^145.5` (`c = 24`, `d = 2^24`, `log q ≈ 182 000`, premise 334 bits). **Still above the padding baseline.** |
| Per statement, asymmetric level `L` | `N ≈ 2^111` at `L = 1`, `2^113.4` at `L = 2`, `2^116.2` at `L = 4` … (table in §2). XWE beats padding only while `L ≲ 60`. |
| `N ≤ 2^120` | Reached only for statements with `L ≤ 8` (branching-program-like statements). It is not reached for the worst case, and no allowed technique is known to reach it. |

The lever is the *asymmetric level* `L` (multiplied edges on a path), not the gate count or
`log q` by itself. The worst-case 4096-gate circuit has `L ≈ 2048`, and no allowed assumption
gives a KP-ABE whose noise does not depend on depth.

## 1. Noise: what the per-level factor really is

**Asymmetric level (proved).** Ring BGG+ evaluates `NAND(a, b)` as `c_one − (c_b·H + y_b·c_a)` with
`H = g^{-1}(B_a)`, so `e_out = e_one − e_b·H − y_b·e_a`. Only one operand is multiplied by the
large matrix. The repository's bound `slpBound` (`WN·bound(a) + bound(b)`, with `a` the multiplied
operand) satisfies

    slpBound ≤ (WN + 1)^L · (depth + 1)^(L + 1) · E        (slpBound_le_alevel)

where `L` is 0 at inputs and at `1` and `max(L(a) + 1, L(b))` at a gate. The existing
`slpBound_le_depth` charges `WN` per level of depth; this one charges it per *multiplied edge*,
with only a polynomial factor in depth. Orienting every gate so that its shallower operand is
multiplied makes `L` the Strahler-type number `max(L_a, L_b) + [L_a = L_b]`. Consequences:

* **Branching-program shape (GV15 phenomenon, (1)).** If every multiplied operand is an input, a
  constant or an advice attribute (§3), then `L = 1` and the noise is `poly(depth)·WN·E`. This
  is the circuit form of Gorbunov–Vinayagamurthy's polynomial-modulus ABE for branching programs
  (ASIACRYPT 2015) and of the sequential (asymmetric) multiplication of Brakerski–Vaikuntanathan
  (ITCS 2014) and Alperin-Sheriff–Peikert (CRYPTO 2014). Skew circuits (each AND has an input
  variable as one operand) are exactly the `L = 1` programs, and they are polynomially equivalent
  to branching programs. Nested BPs whose read wires have level `≤ L − 1` sit at level `L`.
* **Worst case.** In the Fibonacci chain `g_{t+1} = NAND(g_t, g_{t−1})` every orientation reaches
  `L ≈ s/2 = 2048`. The chain itself collapses (it is a function of its two seeds), but chains
  that keep a window of `r` live wires and inject fresh inputs, `g_{t+1} = NAND(g_t, NAND(g_{t−r}, x))`,
  have Strahler level about `s/(2r)` and branching-program width `2^r`. For `r ≈ 20`, `L ≈ 100`
  and a BP is too wide. Segmenting the circuit into windows of `t` gates gives `L ≤ s/t` at a cost
  of `4 s t 2^t` products, which loses for every `t` (for `t = 4` it costs `2^8` more products and
  saves only `2^4` in `log³ q`). **No evaluation strategy that provably lowers the worst-case `L`
  below `≈ s/2` is known.** A proof would need BP-type lower-bound technology. Re-synthesis by
  depth reduction (Paterson–Valiant `O(s / log s)`) has no useful constant at `s = 2^12`, and
  Barrington costs `4^depth`.
* **Collusion-resistant unbounded-depth ABE needs a forbidden assumption.** Hsieh–Lin–Luo (ePrint
  2023/1716, FOCS 2023) get unbounded depth from *evasive circular LWE*. Their circular-security-only
  results are 1-key ABE, LFE and reusable garbling. XWE issues `2^{m1}` keys under one master key,
  so 1-key schemes do not apply. Wee's poly(depth) ABE also uses evasive LWE.

**Spectral instead of `ℓ∞` growth (sound with one modification).** PR #83 charges
`β = k·d·(2^c − 1)` per level, a worst-case `ℓ∞` bound. Fresh errors are independent of the public
matrices, so given those matrices the decryption error is Gaussian with a variance fixed by
`s1(H)`. For a `k×k` ring matrix with i.i.d. uniform balanced digits,
`s1(H) ≤ 8.4·2^{c−1}·√(dk)` except with probability `2^{-128}` (a 1/4-net bound per CRT slot, a union
bound over `d` slots and `2^12` gates). This saves `0.5·log(dk) − 3` bits per level (about 16 of
70 at PR #83's parameters) and makes small `c` competitive: at `c = 16` the factor is about 37 bits
per level against 70. The trapdoor `R_f` (key width) obeys the same recursion. **Modification:**
the digit matrices must have the claimed distribution. `B_g = B_one − B_b H` reuses `B_one` at
every gate, so the gates are correlated. Give each gate its own constant-1 wire
`B'_g = A·R_g + G` with a fresh public short `R_g`. Its encoding `c_A·R_g` is computable by the
decryptor, and in the simulation it is an attribute of value 1, so security is unchanged. Each
`B_g` is then statistically uniform given the past (ring regularity over `R_g`). `B'_g` does not
depend on `w1`, so it is computed once for all keys. The cost is one key's work in `Enc` and a
factor 3 in `Dec`'s single evaluation. **Remaining proof obligations:** the net bound on `s1` of
negacyclic digit matrices, and the Gaussian tail of the decryption error, as theorems.

**Other noise items.** Balanced digits save 1 bit per level. Replacing PR #83's `2^{140}`
flooding by BGG+'s `e_i = e_A R_i` (generalized leftover hash) saves about 220 bits of `log q`,
negligible in the worst case and significant at `L ≤ 4`. Two-to-one recoding (GVW13) has a
smaller per-level factor (≈43 bits) and no key-width doubling, but it is symmetric (`L` = depth =
4096 for the chain) and costs about 32× more per gate. It is a wash.

## 2. Parameters as a function of the asymmetric level

Model: 4096 multiplied gates per key. Costs are PR #83's formulas in 62-bit word operations, with
`2^14` steps per word operation. `k = ⌈log q / c⌉`, `m = 2k`, and `L` primes. `log q` is
`2·growth + init` (ciphertext noise times key width). The premise is the lazy accounting of §4. The
estimator checks `H(d, log q) ≥ H_need`. Columns: `c`, `log d`, the split `m1/m2`, `log q`,
`log₂` of the key cost `K` and the ciphertext cost `C` (word ops), `log₂ N` (steps), and the
premise needed versus the estimator's value.

| `L` | `c` | `log d` | `m1/m2` | `log q` | `K` | `C` | **`log N`** | premise need / estimator | `log N`, `ℓ∞` + PR #83 premise |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 1 | 32 | 14 | 60/68 | 180 | 35.8 | 28.1 | **111.0** | 310 / 346 | 114.6 |
| 2 | 48 | 15 | 60/68 | 358 | 38.2 | 30.6 | **113.4** | 311 / 347 | 116.3 |
| 4 | 12 | 15 | 60/68 | 365 | 41.6 | 32.6 | **116.2** | 314 / 339 | 118.5 |
| 8 | 16 | 16 | 60/68 | 732 | 44.2 | 35.3 | **118.8** | 315 / 339 | 120.8 |
| 16 | 16 | 17 | 59/69 | 1 419 | 47.6 | 38.3 | **122.0** | 318 / 352 | 123.6 |
| 32 | 16 | 18 | 59/69 | 2 824 | 51.3 | 41.3 | **125.3** | 320 / 355 | 126.8 |
| 64 | 16 | 19 | 59/69 | 5 695 | 55.1 | 44.4 | **128.8** | 322 / 352 | 130.3 |
| ≈2048 (worst case, Fibonacci growth) | 24 | 24 | 57/71 | 182 417 | 73.8 | 59.2 | **145.5** | 334 / 357 | 147.7 |

Each doubling of `L` costs about 3.3 bits of `N`; `L = 1` is about `2^{111}`.

The `ℓ∞`/PR #83-premise column gives `N` with PR #83's own noise and premise accounting at the
same level, for comparison. **`N ≤ 2^120` needs `L ≤ 8`; beating padding (`2^128.6`) needs
`L ≤ 60`.** The worst case (`L ≈ 2048`, Fibonacci growth) gives `2^145.5` (spectral) against
`2^147.7`. The reason is structural: `K ≈ log(4096·k²·L·d)` with `k ≥ 2·L_level`, so
`K ∝ 3 log log q + log d`, and the `2^{m1}` keys dominate.

## 3. (2) Decryptor-side auxiliary wires

* **Advice attributes are free and safe.** The ciphertext for `w2` may carry, as extra BGG+
  attribute bits, *any* function of `w2`, for example the values of all gates whose cone lies in
  `W2`. The key for `w1` evaluates `φ(w1‖·)` from these and from its own constants (gates in
  `W1`'s cone are constants, encoding 0). Correctness holds on consistent attributes, and security
  needs only that every key be unauthorized on every *published* attribute, which holds because
  the advice is the true value. Such wires sit at level 0. Their cost is `k` ring elements per
  extra bit per ciphertext.
* **Mixed wires cannot be supplied.** A gate value that depends on both halves would have to be
  published for both values under one secret (which leaks `sG`; see `mix_leak` in open PR #80),
  enumerated (each bit doubles one side, so `g` cut bits cost `2^{g/2}` in `N`), or carried by a
  two-input ABE (open from plain LWE, PR #87). Truth-table advice for a gate that depends on `j`
  bits of `W1` costs `2^j` attribute bits.
* **Gain.** Per statement: `L` drops to the level of the mixed subcircuit, and `Enc` (which knows
  `φ`) can choose the split to maximise locality. In the worst case the gain is zero: one layer of
  `NAND(x_i, y_i)` makes every later gate mixed.
* Cut wires: halving `L` saves about 3.6 bits of `N` at the worst case (§2), and a cut that halves
  a width-`w` region costs `w/2` bits. This is worth it only for `w ≤ 7`, which is the
  branching-program regime anyway.

## 4. (3) Premise: from 437 bits to about 334

PR #83 needs `H ≥ k_hop + log T_sim` with `k_hop = 128 + 2·log(5·2^{71})` and
`T_sim ≈ 2^{161}` steps (the reduction regenerates the whole ciphertext with `R_f`-simulated keys).
`hardAt_of_reduction` replaces the additive `T_sim` by a **per-step overhead** `α` plus `β/p`. The
reduction simulates `A` and generates each key or ciphertext only when `A`'s input head reaches
it. That costs `α = max(gen cost / item length)` per step of `A`. Setup `β` is divided by the
position `p` of the first item that can change the view, which is at least the key block of about
`2^{113}` bits. With the `R_f` factor `m` on keys and a generator on 3 extra tapes
(Hennie–Stearns `log` factor; `descLen` grows like `3^{tapes}`), `log α ≈ 46 + 12`. So
`H_need ≈ 334`, against 437. This lets `d = 2^24` at `log q ≈ 1.8·10^5`. The effect on `N` is about
0.2 bit, because `log q` is set by depth and not by the premise. **One hop for all `2^{71}`
ciphertexts is not available:** BGG+ selective security embeds a single attribute `x*` in the shared
`B_i`. A lossy-mode `A` would make each per-ciphertext hop statistical, but moving the embedding
from `x_j` to `x_{j+1}` is then no longer statistical (`A R_i` is not uniform for a lossy `A`), so
every hop still has computational sub-hops. The `2·log T` term is inherent to per-ciphertext
hybrids.

**Reach (`hardAt_of_take`, proved).** A machine with clock `t` reads only the first `t` input bits,
so two challenge laws that agree on a prefix of length `m ≥ t` give gain 0. Hops whose ciphertext
lies beyond `2^{128}` are therefore free, which reduces `T_eff` for designs with ciphertexts of
`2^{128}` bits or more (PR #83's `2^{133}`-bit ciphertext gets `T_eff ≈ 2^{65.6}`). It also gives
the **padding scheme**: `Enc(φ, β)` outputs `P` zeros and then `β`, with the bit placed at encoded
position `≥ 2^{128}`. Every machine with clock below that position has advantage 0, and every
other machine costs more than `2^{128}`. Then `time(Enc) ≈ 2^{127}` (the tuple framing roughly
doubles length), `time(Dec) ≈ 2^{128}`, `N ≈ 2^{128.6}`, with no assumption. This is the "time-lock"
route that `pq-we-concrete-regime-constructions` dismissed as dead. As a *cost* it beats the
registered `2^{188}` baseline and PR #83's `2^{147.7}`, and it is consistent with that note's
evaluation-only bound `N ≳ 2^{120}`. Any WE submission is meaningful only below about `2^{128.6}`.
A full submission (machines, correctness, `N`) is a separate, mostly mechanical task.

## 5. (4) Module/NTT choices and the word model

* **Module rank > 1** multiplies the gate cost by about `n²` (the gadget matrix is `nk × nk`) for
  the same total dimension. Rank 1 (ring) is optimal. NTT-friendly primes need `2d | p − 1`.
* **Word size.** On a binary multi-tape TM a `w`-bit modular multiplication costs about `4w²`
  steps, so per limb work scales like `w·log q`. 30-bit primes would save about 1 bit on the
  `k²·L·d` term, but the CRT term `k·d·L²` grows by 4×. Net: within about 1 bit. Bit-slicing across
  `t` tapes costs `descLen ∝ 3^t·6^{…}`, so the `2^{14}` steps per word operation can drop by at
  most a few bits at `≤ 40` tapes.
* **Gadget base.** With spectral noise the optimum moves from `c = 32` to `c = 16…24` at the worst
  case. At low level a large `c` (`k` of 5 to 10) is optimal.

## 6. What is proved, what remains

Proved (this PR): `hardAt_of_take` (input-head locality ⇒ a decision problem with `k` bits when
the laws agree on `2^k − 1` bits), `slpBound_le_alevel` (noise exponential only in the asymmetric
level) and `hardAt_of_reduction` (reduction accounting with per-step overhead and position-scaled
setup).

Remaining gaps:

1. The worst-case asymmetric level of 4096-gate circuits under any efficient re-synthesis. This
   decides whether lattice XWE can ever beat padding in the worst case. No proof technique is in
   sight (it is a branching-program lower-bound question at concrete size).
2. Spectral bound on negacyclic digit matrices and the Gaussian decryption tail (theorems), with
   the per-gate constant-1 re-randomisation.
3. The lazy reduction as an explicit machine (overhead `α`, extra tapes, `descLen`).
4. A padding submission (`Def_WE_CircuitSAT_Impl_Padding`) using `hardAt_of_take`, which would
   set the reference at `N ≈ 2^128.6`.
5. For per-statement use: `Enc` computes an orientation and `L`, and picks `(c, d, q)` from a
   table. The worst-case `N` of such a scheme is `max(N(L_max), 2^128.6)` with a padding fallback.
