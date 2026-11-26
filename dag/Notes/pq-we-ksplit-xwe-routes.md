---
title: Splitting the XWE witness into k > 2 parts - what it needs, why plain LWE stays at 2^{m/2} for generic circuits, and a layered ABE chain for bounded-width verifiers
refs: [definition:WE_CircuitSAT, definition:SuccinctLWE, definition:DecomposedLWE, note:pq-we-hybrid-count-barrier, note:pq-we-tree-encodings, note:pq-we-evaluation-oracle-crux, note:pq-we-summary-2026-11, note:we-circuitsat-bruteforce-explicit-cost, theorem:AdvancedEncryption.WE.KSplit.table_sum_lower, theorem:AdvancedEncryption.WE.KSplit.chain_frontier, theorem:AdvancedEncryption.WE.KSplit.chain_reach_succ, theorem:AdvancedEncryption.WE.KSplit.mix_leak]
tags: [witness-encryption, attribute-based-encryption, cost, barrier, literature]
---
Design-AI sub-task on `Def_WE_CircuitSAT` (`m = 128` witness bits, `2^12` NAND gates). The 2-split
XWE of Brakerski–Jain–Komargodski–Passelègue–Wichs (ePrint 2017/874, "BJKPW", Theorem 3.2,
Corollary 3.3) issues `2^{m/2}` key-policy ABE keys (one per `w1`, for `V(w1, ·)`) and `2^{m/2}`
ciphertexts (one per `w2`). Its proof is a hybrid over the ciphertexts, in line with
`pq-we-hybrid-count-barrier`. Another sub-task is instantiating it (open PR #64). The question here
is whether a split into `k > 2` parts can bring encryption down to about `k·2^{m/k}` from allowed
assumptions: plain or Ring LWE, succinct LWE (`Def_SuccinctLWE`) or decomposed LWE
(`Def_DecomposedLWE`). Evasive LWE, iO and statement-dependent assumptions are excluded.

**Short answer.** Not for generic circuits with known techniques. A `k`-way split needs `(k−1)`-input ABE (§1),
and no allowed construction of it exists. The constructions from single-input ABE that we found
(recursion, nesting, compressed keys or ciphertexts) either reduce to the same missing object or
stay at exponent `1/2`. One construction is new and does beat `1/2`, but only for verifiers that
can be streamed with a narrow state (§3). The best generic cost from allowed assumptions remains
the 2-split, about `2·2^{64}·poly`. The note `pq-we-split-witness-abe` (PR #64) gives the exponent
frontier for the 2-split and its tail-block variant.

## 1. What BJKPW's k-split needs (Appendix A)

BJKPW Appendix A (Definition A.1 and the transform after it) uses a **k-input ABE** with a *single*
function key, for `V_x(w_1, …, w_k)`, and one slot-`i` ciphertext for each `w_i ∈ {0,1}^{m/k}`.
Decryption combines the key with one ciphertext per slot. Security needs one unauthorized key
against all `k·2^{m/k}` ciphertexts, and the decryptor can mix and match them across slots.
Collusion among keys is not needed, since only one key is issued. With a collusion-resistant
scheme, the keys can also index one witness part (`2^{m/k}` keys for `V(w_0, ·)`). A `k`-way
split then needs only `(k−1)`-input ABE, which matches BJKPW's compression `1/(k+1)` for
`k`-input ABE. Mixing ciphertexts across slots is the essential difficulty. The paper says (§1) that no instantiation from standard assumptions
is known.

**Literature check (confirms x3, PR #74).**

| Work | Arity / class | Assumption | Usable here |
| --- | --- | --- | --- |
| Agrawal–Yadav–Yamada, CRYPTO 2022 | 2, NC1 | LWE **plus pairings** in GGM or KOALA (knowledge) | no: pairings are not post-quantum, and GGM/KOALA |
| AYY22 | 2, P; 3, NC1 | heuristic (no proof) | no |
| Agrawal–Rossi–Yadav–Yamada, ePrint 2023/941 (CRYPTO 2023) | constant, NC1 / P | evasive LWE (+ tensor LWE for P) | no: evasive |
| Francati–Friolo–Malavolta–Venturi, ePrint 2022/806 (EUROCRYPT 2023; JoC 2024) | constant / poly | plain LWE | no: conjunctions of single-slot predicates only (see below), no collusion |
| ePrint 2025/001 (ABE for TMs) | single input | evasive + circular tensor LWE | no |

ARYY23's Table 1 gives the same picture. A search of 2024–2026 ePrint found no 2-input ABE from
plain LWE. FFMV23's class is `f(x_1, …, x_k) = ∧_i P_i(x_i)`. For such a verifier,
`∃w ∧_i P_i(w_i) ⇔ ∧_i ∃w_i P_i(w_i)`, so satisfiability can be decided slot by slot in time
`k·2^{m/k}` with no cryptography at all. Conjunction-class miABE therefore adds nothing for
CircuitSAT. **Secret-key** 2-input ABE from plain LWE would give about `2^{43}` (k = 2 slots plus
the key, BJKPW's `1/(k+1)` count with a polynomial-size instance). It remains open, and it is
exactly the mix-and-match problem below.

## 2. Routes that do not beat 2^{m/2} (generic circuits)

**(a) Table floor.** Suppose a decryption reads one entry from each of `k` tables that the
encryptor generates explicitly. The tables must jointly index all `2^m` witnesses, so
`∏ N_i ≥ 2^m`. Then `Σ N_i ≥ k·2^{m/k}` (`table_sum_lower`, AM-GM). Single-input ABE gives two
tables: keys and ciphertexts. To get more tables, some table must be *derived* by the decryptor
rather than generated, or nested (c).

**(b) Derivable or compressed ciphertexts (broadcast style).** Suppose the decryptor could derive
a BGG+ encoding `sᵀ(A − x⊗G) + e` for any `w2` from a short public object, with one secret and one
matrix per block. Then two attribute values give `(x' − x)·sᵀG + noise` (`mix_leak`). This reveals
`s`, so all ciphertexts open. Independent matrices per value avoid the leak, but then the key's
`A_f` depends on the value combination, and keys multiply back to `2^{m/2}`. The remaining option
is a non-linear derivation (GGH15 / tree encodings), and that is the evaluation-oracle crux. For
`Def_DecomposedLWE`-based tree encodings (ePrint 2026/741), `pq-we-tree-encodings` shows the
master side stays uncompressed, and the laconic ciphertexts fall inside the affine-syzygy barrier.

**(c) Succinct-LWE ABE (Wee, CRYPTO 2024; `Def_SuccinctLWE`).** It shortens each key or ciphertext
to `poly(depth, λ)`, independent of the attribute length. It does not reduce their number or the
`Ω(|f|)` key-generation time (the key-side `A_f` must still be evaluated). It saves a polynomial
factor (about `ℓ = 64` in ciphertext size), and the exponent stays `1/2`.

**(d) One big key or ciphertext.** A KP-ABE key for `F(w2) = ∃(w1,w3) V` or a CP-ABE ciphertext
for `∃w2 V(·, w2)` has circuit size `2^{a+c}·|V|`. Its key generation (`Eval_pk`) or encryption
costs that much, which moves the enumeration without removing it. ABE whose key generation is
sublinear in the machine's running time (ABE for TMs/RAM) uses evasive LWE (ePrint 2025/001,
Agrawal–Kumari–Yamada 2023).

**(e) Nesting with constant payloads.** An ABE payload is fixed per ciphertext and cannot depend on
the key. Nested layers (outer ciphertexts carrying inner keys) can therefore only forward
information that is *in the ciphertext index*. This is the chain of §3. Its cost depends on how
much state must be forwarded.

## 3. A layered ABE chain (new; allowed assumptions; gains only for narrow verifiers)

Suppose the verifier can be streamed: there are `h_i` and `Q` with
`V(w_1, …, w_k) = Q(σ_{k−1}, w_k)`, `σ_0 = ⊥` and `σ_i = h_i(σ_{i−1}, w_i)`, where each state
`σ_i` has `s` bits. Use independent single-input KP-ABE instances `ABE_2, …, ABE_k`, all from LWE
(BGG+14 or GVW13), with a KEM plus a one-time pad for long payloads.

* **Layer 1 (no ABE):** for each `w_1`, publish the `ABE_2` key `K_2[σ_1]` for `σ_1 = h_1(⊥, w_1)`
  (at most `2^{min(ℓ_1, s)}` distinct keys).
* **Layer i (2 ≤ i ≤ k−1):** `ABE_i` keys `K_i[σ]` are for `f_σ(w, σ') = [h_i(σ, w) = σ']`. For
  every `(w_i, σ_i)` publish `Enc_i(attr = (w_i, σ_i), msg = K_{i+1}[σ_i])` (`2^{ℓ_i + s}`
  ciphertexts).
* **Layer k:** `K_k[σ]` is for `Q(σ, ·)`. Publish `Enc_k(attr = w_k, msg = b)` for every `w_k`.
* **Dec** follows its own states: the key from layer 1, then one decryption per layer.

**Security** (false statement, induction over layers). Let `R_i` be the set of reachable states.
Then `R_{i+1} = {h_{i+1}(σ, w) : σ ∈ R_i}` (`chain_reach_succ`). Assume the revealed `ABE_i` keys
are exactly those for `R_{i−1}`. Then the layer-`i` ciphertexts with `σ_i ∉ h_i(R_{i−1}, w_i)` are
unauthorized for every revealed key. A hybrid over them, using `ABE_i` selective security, replaces
their payloads by junk. After that, the revealed `ABE_{i+1}` keys are exactly those for `R_i`. At
layer `k` the statement is false, so `Q(σ, w) = 0` for all `σ ∈ R_{k−1}` and all `w`. A hybrid over
the `2^{ℓ_k}` ciphertexts switches `b`. Every hop is a statement-independent LWE hop (one per
ciphertext), for about `Σ_i 2^{ℓ_i + s}` hops in total. This is the exponential-hybrid escape of
`pq-we-hybrid-count-barrier`, and the same squared-advantage accounting as the 2-split applies.

**Cost recurrence.** The layer exponents are `ℓ_1`, `ℓ_i + s` (middle) and `ℓ_k`. The keys add
`s ≤ e`. All layer exponents are `≤ e` iff `m + (k−2)·s ≤ k·e` (and `s ≤ e` when `k > 2`)
(`chain_frontier`, exact, with `j = k − 2`). For `m = 128` this means:

| k | best `e` | beats `2^{64}` iff |
| --- | --- | --- |
| 2 (BJKPW) | 64 | – |
| 3 | `⌈(128 + s)/3⌉` | `s ≤ 63` |
| 4 | `⌈(128 + 2s)/4⌉` | `s ≤ 63` |
| `k → ∞` | `→ s` | `s ≤ 63` |

For example, `s = 16` gives `e = 48` at `k = 3` and `e = 40` at `k = 4`. **Limitation:** `s` is the
streaming width of the verifier in some witness-bit order, that is, the cut between the gates
depending on the prefix and the rest. For worst-case `2^{12}`-gate circuits it is as large as the
prefix itself (a hash-like `V` needs `σ_i` of about `Σ_{j≤i} ℓ_j` bits), and then the chain is no
better than the 2-split. Since `Def_WE_CircuitSAT` prices the worst case, the chain gives no
generic improvement. It is a valid, fully allowed scheme for statements whose circuits are narrow,
for example layered circuits of small width, CNF/Tseitin checks whose clauses are local in the
witness order, or bounded-pathwidth circuits. A Tseitin re-encoding does not help generically:
every auxiliary wire bit enters the enumerated witness.

## 4. Verdicts and costs (vs the baseline `N ≈ 2^{188}` and MP2/MP3 at about `2^{97}`, unproved)

| Option | Assumption | Exponent of enc. items (m = 128) | Status |
| --- | --- | --- | --- |
| BJKPW 2-split | plain/Ring LWE | 64 (+ poly; rough sweep estimate about `2^{136}` total at depth 4096) | provable; best generic |
| k-way split via (k−1)-input ABE | none allowed (pairings+GGM/KOALA, evasive) | `⌈128/k⌉` (k = 4: 32, k = 8: 16) | excluded |
| secret-key 2-input ABE from LWE | open | about 43 | open target |
| derivable/broadcast ciphertexts, tree encodings | LWE / decomposed LWE | – | reduces to the evaluation-oracle crux (`mix_leak`, `pq-we-tree-encodings`) |
| succinct-LWE ABE | succinct LWE | 64 (smaller poly) | provable; poly-factor saving only |
| layered chain (§3) | plain/Ring LWE | `⌈(128 + (k−2)s)/k⌉` | provable; generic worst case `s ≈ prefix`, so 64 |

None of these items reaches `2^{97}` generically. The 2-split is below `2^{188}` only if the
polynomial factor is about `2^{120}` or less, which PR #64 has yet to establish. **Next steps:**
(i) secret-key 2-input ABE for the restricted class "BGG+ evaluation of a fixed public circuit on
two independently encrypted halves", stated as an open theorem node; (ii) a measurement of the
streaming width of the actual worst-case circuit family. If the problem were ever restricted to
narrow circuits, the chain would give `e ≈ (128 + (k−2)s)/k` at once.
