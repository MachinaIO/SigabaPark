---
title: Cryptanalysis of the multi-pass masked GGH15 WE candidate (MP2/MP3) against the known GGH15 attack families
refs: [definition:WE_CircuitSAT, note:pq-we-multipass-ggh15, note:pq-we-masked-evaluator-mechanisms, note:pq-we-witness-prf-masked-evaluator]
tags: [witness-encryption, ggh15, cryptanalysis, candidate]
---
This note evaluates the MP2/MP3 candidate of `pq-we-multipass-ggh15` against the known attack
families on GGH15-based constructions. MP2/MP3 is a masked γ⊗-GGH15 that reads the 128-bit
witness in 2–3 passes, puts the comparator on pass 1 and the Tseitin clauses on the last pass,
adds equality clauses between copies, and decrypts canonically.

This is an analysis checked against the cited source texts. It is **not** a security proof. No
attack was found. The conclusion is that every known attack family needs an ingredient that a
false statement does not supply.

## 0. What the adversary has, for a false statement

WE security only concerns statements `φ` with no witness. The adversary holds the GGH15 encodings
`D_{i,b}`, the two left vectors `u_O`, `u_C`, and the ciphertext `⌊mask⌉ + μ`. The plaintext
matrix of a level string `z ∈ {0,1}^L` is

`Ŝ_z = diag(P_z ⊗ R, M_z ⊗ S'_z, S_z)`.

The decryption combination `(u_O − u_C)·D_z` cancels the CPRF block (rank-one left difference)
and evaluates to

`mask + (constraint term of M_z ⊗ S'_z) + E_z`.

* **Consistent strings** (all passes read the same `w`): the constraint product `M_z` is the
  diagonal of clause-falsification indicators of the CNF branching program (CVW18 Construction
  6.4). It is `0` iff every clause holds. For a false `φ`, `Tseitin(φ)` is unsatisfiable, so
  `M_z ≠ 0`.
* **Mixed strings:** each one falsifies an equality clause, so `M_z ≠ 0`
  (`pq-we-multipass-ggh15` §4).

So **no level string evaluates to a small value**: for a false statement there is no
*encoding of zero* and no *evaluation of zero*. Two distinct strings never share a plaintext,
because the bit-dependent constraint secrets `S'_{i,b}` and CPRF secrets `S_{i,b}` make every
path product distinct.

## 1. Attack families, checked against the sources

| Attack | What it needs (from the source) | MP2/MP3 on a false statement |
| --- | --- | --- |
| CVW18 §9 rank attacks: single-cut (Claim 9.4) and variable-partition (§9.3.2, Claim 9.8) | Evaluations of zero, so that the noise matrix can be read over the integers and its rank tested. CVW18 §1: "the attacks apply only to settings where the adversary can trivially obtain encodings of zero"; §10.3: zero-encodings "are not readily available in the witness encryption setting" | **Not applicable**: no zeros (§0). Even granting zeros, the §9.3.2 matrix dimension for `c` passes is `≥ t^{Θ(c)}`, beyond `2^{64}` at `n = 128` (`pq-we-multipass-ggh15` §4). CVW18's bound also has `m`-dependent terms; for `c = 2` the need is `ρ ≥ t³ + t²m + tm² + m³` with `m ≈ 2^{40}`, a stronger obstacle still |
| CHL+15 / CLLT16 (Coron–Lee–Lepoint–Tibouchi, ePrint 2015/1037): GGH15 key agreement | Several public encodings whose products along different paths encode **equal** plaintexts, so their differences are small (step 1, a CHL+15-type linear relation), then error correction (step 2) | **Not applicable**: no two distinct strings share a plaintext (§0). The left-vector products carry pseudorandom CPRF blocks |
| Statistical zeroizing, CCHKL (ePrint 2018/1081) | "uses evaluations of zeros of obfuscated programs": the sample variance of zero evaluations | **Not applicable**: no zero evaluations |
| Mixed-input attacks (the reason for bundling scalars; HHSS17, ePrint 2017/104, implements read-once programs only for this reason) | An inconsistent (mixed) input that evaluates to zero or accepts | **Blocked**: every mixed string falsifies an equality clause, so it is non-zero (`pq-we-multipass-ggh15` §4). No bundling is needed |
| Subtraction / inclusion–exclusion (CVW18 Remark 10.3) | Plaintext linear relations among strings in the bit-independent-secret variant | **Blocked by the γ⊗ tensoring** with bit-dependent `S'` (`pq-we-witness-prf-masked-evaluator`) |
| CGH17 (Chen–Gentry–Halevi, ePrint 2016/998) | Input-partitioned branching programs | **Not applicable**: every bit is read on both sides of every cut |
| Evasive-LWE counterexamples (ePrint 2026/2792, 2026/2548) | Refute general evasive-LWE and evasive-IPFE *assumptions*, using samplers built from obfuscation of specific programs | **Not an attack on a scheme.** MP2/MP3 assumes no evasive LWE. Its missing reroute lemma is to be proved from LWE. These works warn only that the reroute lemma must not be replaced by an evasive-type assumption |

## 2. Non-zeroizing linear-algebra attempts (our own)

* **Recover `mask` by a short combination.** A short `α` with `Σ_z α_z·(constraint terms) = 0`
  and `Σ α_z ≠ 0` would give `(Σ α_z)·mask` up to small noise. The constraint terms are products of
  hidden secrets along paths. The attacker sees them only inside noisy, full-size values mod `q`,
  so no left kernel of the hidden factor `F` in `Y = 1·mask + F·G + E` can be computed from `Y`.
  With noise, `Y` is full rank mod `q`. Finding such an `α` is a short-vector problem in dimension
  greater than the plaintext rank, which is SIS-like.
* **Bilinear rank over a cut.** Over a rectangle `X × Y` of strings, the values are
  `mask + f(x)·g(y) + E`. Rank tests need the values to be small, so that they can be read over the
  integers. Here they are uniform-size mod `q`, so the test has nothing to act on.
* **Differences cancel the mask.** `y_z − y_{z'}` removes `mask` and leaves only constraint terms,
  which carry no information about `mask`.

## 3. Where security actually rests

On a false statement, MP2/MP3's security is the claim that `mask` stays pseudorandom given noisy,
non-small, path-structured values. That is exactly the candidate's missing **two-pass reroute
lemma** (`pq-we-multipass-ggh15` §6). The cryptanalysis therefore leaves the candidate standing,
with the usual caveats:

1. All known attacks are **zeroizing** or **plaintext-relation** attacks. A new attack paradigm
   on non-zero GGH15 evaluations would not be covered by this note.
2. CVW18 Claim 9.8 shows that equivalent 2-repeating programs are distinguishable asymptotically
   **when zeros exist**. Any proof of the reroute lemma must use that the statement is false (no
   zeros) or take `c` large. The reroute lemma as stated in `pq-we-multipass-ggh15` §6 must hold
   on true statements too, so that caveat applies to it.
3. Parameters, from `pq-we-multipass-ggh15` §4: `m ≈ 2^{40}`, `log q ≈ 2^{16.5}`, about
   `2^{97}` bits, and LWE premises of about 400 bits for `≈ 2^{136}` hops. The rank and
   lattice-reduction attacks considered need dimensions far beyond `2^{64}`.

**Verdict.** No known attack applies to MP2/MP3 on false statements at the stated parameters. This
is consistent with CVW18's own assessment of GGH15-based witness encryption (§10.3). The candidate
remains an **unproven, unrefuted** post-quantum WE whose single missing piece is the reroute lemma.
