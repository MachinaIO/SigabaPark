---
title: Non-trivially efficient WE from Ring-LWE BGG+ ABE (BJKPW17) - verified source, instantiation for WE_CircuitSAT, N about 2^148
refs: [definition:WE, definition:WE_CircuitSAT, theorem:AdvancedEncryption.WE.Hybrid.hardAt_chain, note:pq-we-hybrid-count-barrier, note:we-circuitsat-bruteforce-explicit-cost]
tags: [witness-encryption, design, abe, bgg14, cost-estimate, plan]
---
Design-AI plan for `WE_CircuitSAT` (NAND circuit SAT, `n = 128` inputs, `s = 2^12` gates,
`λ = κ = 128`, no setup) from **plain Ring-LWE only**. It follows Brakerski–Jain–Komargodski–
Passelègue–Wichs, *Non-Trivial Witness Encryption and Null-iO from Standard Assumptions*, ePrint
2017/874 (SCN 2018). The design target is an explicit cost of about `2^148` machine steps, against
`2^188` for the assumption-free baseline (`we-circuitsat-bruteforce-explicit-cost`). It uses only
the registry's `RingLWE.decision`, with no new assumption. The scheme is not iO, it uses no evasive
LWE, and its premise does not depend on the statement. Everything below is a paper design with
estimates; nothing here is proved in Lean yet. The staged plan is at the end.

## 1. What the source says (checked against the full text)

* **ABE (Def. 2.1).** Key-policy, *private-key*, unbounded-collusion ABE with algorithms `Setup`,
  `KG(msk, f)`, `Enc(msk, α, b)` and `Dec`. It is `(t, ε)`-*selectively* secure: for selectively
  chosen `f_1..f_p` and `α_1..α_p` with `f_i(α_j) = 0` for all `i, j`, the joint views
  `{KG(f_i), Enc(α_j, 0)}` and `{KG(f_i), Enc(α_j, 1)}` are `(t, ε)`-indistinguishable. These are
  **many ciphertexts at once**.
* **Thm. 2.3 ([BGG+14]).** Sub-exponential LWE gives sub-exponentially secure ABE with
  *time-efficient key generation* (`|f| · poly(λ, d)`) and *short keys* (`poly(d, λ)`). This is the
  BGG+ key-policy ABE for depth-bounded circuits. The paper also cites [GVW13] (Cor. 3.3) and
  [GPSW06] (DBDH, NC1).
* **Thm. 3.2 (XWE from ABE).** Split `w = w1 ‖ w2` into halves. `Enc` runs
  `msk ← Setup(1^λ̃)` with `λ̃ = max{λ, m^{2/τ}}`, issues `sk_{w1} ← KG(msk, V_{x,w1})` for
  every `w1` (with `V_{x,w1}(w2) = V(x, w1 w2)`), and `ct_{w2} ← Enc(msk, w2, b)` for every `w2`.
  `Dec` runs `ABE.Dec(sk_{w1}, ct_{w2})`. Encryption time, ciphertext size and decryption time are
  each `2^{m/2} · poly`, and decryption is `poly` in the RAM model. **Proof:** one invocation of
  Def. 2.1 with `p = 2^{m/2}`, keys and ciphertexts both. Sub-exponential hardness is used only so
  that the ABE stays secure against `poly(2^m)`-time adversaries. **Cor. 3.3** instantiates it from
  sub-exponential LWE.
* **Thm. 3.4 / Cor. 3.5.** With short keys, `w = w1 ‖ w2 ‖ w3` and the key for `w1` is
  `∨_{w3} V(x, w1 w2 w3)`. This gives encryption `2^{max(m1+m3, m2)}`, ciphertext
  `2^{max(m1, m2)}` and decryption `2^{max(m1, m2, m3)}`, and `m/3` each gives Cor. 3.5. Ciphertext
  size is traded against time; it does not lower `time(Enc)`, so we use `m3 = 0` with an
  **unbalanced** `m1 ≠ m2`, which is the same proof.
* **Correction to the sweep's summary.** Thm. 3.2's proof contains no explicit hybrids. In the
  concrete setting the `2^{m2}` hybrids sit inside multi-ciphertext ABE security, one hop per
  **ciphertext** `w2`. The `2^{m1}` keys need no hops: in each hop they are simulated with the BGG+
  trapdoor `R_f`, because every `f_{w1}(w2*) = 0`. This fits `pq-we-hybrid-count-barrier`, which
  asks for exponentially many hops, each using the local fact `φ(w) = 0` for one `w2` and all `w1`.

## 2. Instantiation for WE_CircuitSAT

**Ring and gadget.** `R_q = Z_q[X]/(X^d + 1)` with `d = 2^25`. `q` is a product of `L = 4640` NTT
primes of 62 bits (`2d | p − 1`), so `log q ≈ 287 638`. The gadget base is `2^c` with `c = 32`,
giving `k = ⌈log q / 32⌉ = 8989` and `g = (1, 2^32, …) ∈ R_q^{1×k}`. `A ∈ R_q^{1×m}` with
`m = 2k` is a ring gadget trapdoor (MP12). The width `2k`, with Gaussian `R_j` of width `2^20`,
makes `A R_j` statistically uniform (ring regularity). The scheme also uses `B_1..B_{|W2|}` and
`B_one ∈ R_q^{1×k}`, and `u ∈ R_q`. The encryptor samples all of them: there is no setup.

**Split.** `Enc` may choose the split per statement. The bound below holds for any split of the
input positions into `W1` (`m1 = 57` bits, enumerated by keys) and `W2` (`m2 = 71` bits, enumerated
by ciphertexts). The unbalanced split is optimal because a key costs about `2^15` times a
ciphertext.

**Gates.** NAND is `1 − ab`. With `H = g^{-1}(B_a)` (`k × k` digits `< 2^32`), the public matrix
is `B_out = B_one − B_b · H`. The decryptor's encodings `c_y = s(B_y − y g) + e_y` give
`c_out = c_one − (c_b · H + y_b · c_a)`, with error `e_one + e_b·H + y_b·e_a`. The algorithm
chooses which operand is `b`. Constants (the `w1` bits fixed in a key) have `B = y·g` and encoding
`0` with no error. A gate with a constant operand is `NOT` or the constant `1`, which is linear and
needs no `k²` product. Only gates with two non-constant inputs cost `k²` ring products, so a key
costs at most `4096` of them.

**Noise for every circuit with 4096 gates** (worst-case `ℓ∞`, so correctness needs no heuristic).
Let `β = k·d·(2^c − 1)`. A new wire has error at most `M + β·S`, where `M ≥ S` are the two largest
existing bounds: put the smaller one in position `b`. A NAND of a wire with itself is `NOT`, which
is linear. So the top two bounds follow `M' = M + βS`, `S' = M`, which grows like
`r^t` with `r = (1 + √(1 + 4β))/2 ≈ √β`. The Fibonacci chain `g_{t+1} = NAND(g_t, g_{t−1})`
attains this. Over 4096 gates the factor is `2^{4096·log r} ≈ 2^{143 600}` at the parameters
above. The simulation trapdoor `R_f` (`B_f = A R_f + f(x*) g`, update
`R_out = −(R_b H + y_b R_a)`) grows by the same factor. BGG+ keys must be Gaussians of width at
least `s₁(R_f)`, so that real keys (sampled with `A`'s trapdoor) and simulated keys
(`SampleRight` with `R_f`) have the same law. The decryption error is therefore about
(ciphertext error growth) × (key width), and `log q ≈ 2·4096·log r + O(300)`. **BGG+ needs
`q ≈ β^{depth-ish}` squared.** This is the source's "sub-exponential LWE", made concrete. The
fresh errors are flooded (`2^{140}` above `e_A R_j`), so ciphertexts need no `e_A R_j` products;
this adds about 230 bits, which is negligible.

**Costs, counted in 62-bit word operations** (scripted; the numbers are reproducible from the
formulas):

| item | formula | log₂ |
| --- | --- | --- |
| one gate in `KG` (digit transforms + MACs + CRT) | `k²·d·log d + k²·L·d + k·L·d·log d + k·d·L²` | 64.1 |
| one key (4096 gates, preimage sampling negligible) | | 76.1 |
| one ciphertext (`(m2+1)k + m + 1` ring elements, NTT) | `≈ 73k · L·d·log d` | 61.2 |
| Enc = `2^{57}` keys + `2^{71}` ciphertexts | | 133.7 |
| ciphertext length (bits) | keys `3k·d·log s_key`, cts `≈ 73k·d·log q` | 133.5 |
| Dec (scans the ciphertext once, evaluates `f` on one ct) | | ≈ 133.5 |

The digit transforms use the small coefficients of `g^{-1}(B_a)`: one forward transform per digit
polynomial over a 128-bit modulus, pointwise products with the precomputed limbs of `B_b`, and one
inverse transform per output limb. This avoids `k²·L` full transforms, which would cost 2^{3.5}
more (2^{135.2} for Enc).

**Machine steps.** We charge `2^{14}` steps per word operation (a schoolbook 64×64 multiply with
Barrett reduction is about `2^{13}` bit operations, and streaming head movement is a small factor).
This gives

    N ≈ time(Enc) + time(Dec) + descLen ≈ 2^{147.7},

about `2^{40}` below the brute-force baseline's `2^{188}`. Two constraints of the tape model:

1. `descLen` grows like `3^{tapes}` (the baseline pays `6·9842·3^{40}·178 ≈ 2^{86.7}` for 40
   tapes). The machine must stay below about 80 tapes (`3^{80} ≈ 2^{127}`). The 256–264-tape
   layouts of the PE submissions would add about `2^{420}` and are unusable here.
2. Every primitive of the `Prog`/`XProg` model sweeps the tapes of its frame. The design must work
   on vectors (one carry primitive per word-parallel pass over a ring element, frames sized to one
   ring element). It must also stream the `k` operands of a row in order, never by indexed
   selection: indexed selection of `B_b[i]` from a `k`-element tape costs a `k·2^{43}`-bit sweep
   per access. With that discipline the overhead over the word count stays within the `2^{14}`
   above, roughly. The PE explicit-cost work shows that unframed or gate-level (SLP) evaluation
   costs hundreds of bits more; the margin of `2^{40}` absorbs only a careful design.

## 3. Security accounting (premise and strength)

The laws are `D_j`: ciphertexts `w2 < j` encrypt `1`, the rest `0`, for `j = 0..2^{71}`. Hop
`j → j+1` (`φ ∉ L`, so `φ(w1‖w2_j) = 0` for every `w1`) is BGG+ selective security with challenge
attribute `x* = w2_j`, in five sub-hops: real `A` → uniform `A` (stat./RLWE), `B_i = A R_i + x*_i g`
(regularity), keys by `SampleRight` with `R_{f_{w1}}` (identical law above the smoothing width),
`(c_A, c_u)` → uniform (**Ring-LWE**: `m + 1 = 2k + 1` samples, `n = d = 2^25`), then back. The
reduction samples every other component itself. Its overhead `T_sim` is the honest `Enc` plus the
`R_f` updates, a factor `m` on the key part: `log₂ T_sim ≈ 147.4 + 14 ≈ 161` steps.

* `hardAt_chain` with `T = 5·2^{71}` hops of strength `k_hop` gives
  `2^{k_hop}·gain ≤ T²·cost`. So `k_hop = 128 + 2·(71 + log₂ 5) ≈ 275` gives `λ = 128`.
* The Ring-LWE hop reduction gives `2^H·gain ≤ cost + T_sim ≤ cost·(1 + T_sim)`. So we need
  **`H ≥ k_hop + log₂ T_sim ≈ 437`**.
* `RingLWE.H` at `(N = 2^25, m = 2k + 1, q ≈ 2^{287 638}, error = secret = D_{Z,8})`: the
  repository's Python mirror of the estimator (`python/lwemodel`, primal uSVP / dual, MATZOV)
  gives **≈ 470 bits**, with block size well below `maxBeta = 16384`. So one premise
  `(RingLWE, p, 437)` suffices, with `≈ 33` bits of slack. At `d = 2^24` the premise is about 218
  bits and fails, which is why `d = 2^25`. Certifying `k ≤ H` at `q ≈ 2^{2.9·10^5}` and
  `n = 2^25` needs the large-parameter estimator bounds (`Estimator.estimatorBits_ge_of`), as in
  the PE work.

## 4. Optimizations considered

* **Split.** Balancing `2^{m1}·K = 2^{m2}·C` gives `m1 = 57`. A balanced 64/64 split costs
  `2^{140}` word operations.
* **Gadget base.** The noise is best at `c = 1`, but cost scales like `log q⁴ / c²`. At `c = 32`
  the estimate is 2^{133.7}; `c = 16` gives 2^{133.0} with `d = 2^24`, but that fails the premise.
* **Reusing structure across keys.** Gates that depend only on `W2` inputs are the same in every
  key and are computed once; gates that depend only on `W1` are constants and free. Only "mixed"
  gates cost `k²` per key. This does not help the worst case, but `Enc` knows `φ` and may choose
  `W1` to minimise the number of mixed gates (a per-statement optimisation; `N` is worst-case).
* **Not available:** a 2-input (multi-input) ABE from LWE (Appendix A of the paper, compression
  `1/(k+1)`) is open. Depth reduction of a general 4096-gate circuit is not available, and
  Barrington blows up at this depth. Module rank above 1 costs `n²` more than the ring.
* **Biggest lever left:** the `2·4096·log r` bits of `q` (section 4a).

## 4a. Depth reduction: what it would buy and why it is not available in the worst case

The size-4096 worst case behaves like **effective depth 2048** (each level multiplies the error by
`β + 1`). Re-running the same optimisation (same cost model, premise checked with the estimator
mirror) for circuits of bounded effective depth `D`:

| `D` | `d` | `log q` | `k` (`c = 32`) | `m1/m2` | `H` needed / mirror | Enc (word ops) | `N` (steps) |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 64 | 2^20 | 8 003 | 251 | 59/69 | 409 / 534 | 2^115.6 | 2^129.6 |
| 256 | 2^22 | 33 119 | 1 035 | 58/70 | 420 / 515 | 2^122.7 | 2^136.7 |
| 1024 | 2^24 | 139 816 | 4 370 | 57/71 | 432 / 485 | 2^130.0 | 2^144.0 |
| 2048 (any 4096-gate circuit) | 2^25 | 287 638 | 8 989 | 57/71 | 437 / 470 | 2^133.7 | 2^147.7 |

Depth matters, but less than one might expect (about `2^11` between `D = 256` and the worst case),
because the cost is dominated by the `2^{57}` keys times `4096` gates, not by `q` alone.

Generic depth reduction does not help `N`, which is a worst case over all statements:

* **Tseitin / CNF verifier (depth `O(log s)`).** This adds the 4096 wire values to the witness.
  XWE **enumerates the witness space**, keys over `W1` and ciphertexts over `W2`. Every new witness
  bit lands in one of them and doubles that side, so the witness length becomes `128 + 4096` and
  encryption costs `2^{(128+4096)/2}`. A wire that is not enumerated has to be *computed* by the
  key's function, which is the original depth again. Guessing a few cut wires costs `2^{g/2}` for
  `g` cut bits, and a chain of depth 4096 needs about 4096/D cuts to reach depth `D`. That is
  strictly worse than paying for depth.
* **Re-balancing.** Formulas (fan-out 1) can be balanced to depth `O(log size)` (Spira, Brent).
  Circuits with fan-out cannot in general: the best generic bound for size `s` is depth
  `O(s / log s)` (Paterson–Valiant), with no constant small enough to matter at `s = 2^12`. The
  Fibonacci chain `g_{t+1} = NAND(g_t, g_{t-1})` is a valid statement, so the worst case stays at
  effective depth 2048.
* **What is available.** `Enc` knows `φ`. It can compute the effective-depth bound of the given
  circuit, rebalance where possible, choose `W1` to minimise the number of mixed gates, and pick
  `(d, q, k)` **per statement** from a fixed table. The table is part of the machine, so its size
  is paid once. This makes typical statements cheaper, but the claimed `N` (a worst-case clock)
  is still the `D = 2048` row. A problem variant with a depth bound `D ≤ 256` would score about
  `2^{137}`.

## 5. Formalization plan (staged DAG nodes)

1. **Abstract XWE-from-ABE laws** (assumption-agnostic). An ABE given by its laws (`setup`,
   `key w1`, `ct w2 b` as `PMF (List Bool)` kernels), the XWE ciphertext law, the hybrid laws
   `D_j`, the endpoint identities `D_0 = Enc(φ,0)`, `D_T = Enc(φ,1)`, and the security theorem
   *every hop `HardAt k` ⇒ `2^k·gain ≤ T²·cost`* (from `hardAt_chain`). **Submitted with this
   note** as `Def_WE_XWE` and `AdvancedEncryption.WE.XWE.security`, with a complete proof.
2. **Ring BGG+ algebra** (reuse `SigabaNeoStd.Lattices.Homomorphic`: key relation, `sim_relation`,
   noise bounds). Add the NAND gate with the asymmetric choice, the Fibonacci noise and trapdoor
   bound for any 4096-gate circuit, and correctness at `4·noise + 2 < q`.
3. **Per-hop reduction**: the five sub-hops, each `HardAt` from `RingLWE.decision` at
   `p = (2^25, 2k+1, q, D_{Z,8}, D_{Z,8})` or statistical. `SampleRight`/`SamplePre`
   law equality reuses the box-sampled Gaussian keys of the PE work. The reduction machine's cost
   is bounded by `T_sim`.
4. **Machines**: `Enc` (key loop, ciphertext loop, NTT/RNS arithmetic as framed vector programs,
   ≤ 80 tapes) and `Dec` (scan, select, evaluate, round), with clocks certified by `NB.check`.
5. **Submission**: `Def_WE_CircuitSAT_Impl_XWEBGG` with one Ring-LWE premise at `k = 437`
   (proof of `k ≤ RingLWE.H p`), the `N` bound, and `SubmissionProp` assembled from 1–4.

Stage 1 is independent of lattices and should come first. Stages 2–3 are the bulk of the proof
work; stage 4 is the bulk of the machine work.
