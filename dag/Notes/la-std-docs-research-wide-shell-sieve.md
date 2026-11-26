---
title: "Acceptance in a wide shell"
refs: []
tags: [lattice-attack]
---
*Moved from `docs/research/wide_shell_sieve.md` (core v0.1.2).*

# Acceptance in a wide shell

Let a fixed bank map source points in a finite set U to differences in a
finite target set T. Suppose every source has at most cA eligible indices
and each target has between l/c and ch representations, where c ≥ 1 and
l > 0. These are bounds on actual counts in the bank. Bounds on continuum
lens volumes alone do not imply them.

Exact cancellation assigns every target mass (l/c)/(cA |U|). Thus the
total success probability is p₀/c², where p₀ = |T| l/(A |U|). For a
nonempty target and positive success probability, the conditional output
is exactly uniform. Independent retries from this fixed good bank take
c²/p₀ trials in expectation. The Lean theorem windowAcceptance gives the
finite mass identity.

For a depth-m budget, if a separate survival analysis justifies inflating
each input batch by a fixed factor B per level, the input-size multiplier
is B^m. A quadratic scan on the enlarged batches then incurs at most
B^(2m) times its original pair budget (before integer rounding).
Its additive base-two log cost is 2m log₂ B, which is o(n) for fixed B
and m = O(log³ n). Establishing that such a B suffices requires bounds on
bank failure and terminal occupancy as well as independent uniform leaves.

For radial half-width w the squared interval has length 4wR². Length
at least one guarantees an integer label in the closed interval.
Representability in a given lattice is a separate counting question.
A positive ensemble mean implies existence of a populated instance when
the ensemble is finite. S1 requires a relative population error of at
most one percent on the instance under consideration.

## Expected wide-shell population at the Kyber512 planted shape (numerical)

Shape `(q, n, m, d) = (3329, 512, 175, 688)`. For uniform `A`, an integer vector `z` with all
`|z_i| < q` that is not a multiple of the planted point lies in the embedding lattice with
probability exactly `q^{−m}` (the condition reduces to `z_e − z_last·e + A(z_s − z_last·s) ≡ 0`
with `z_s ≢ z_last·s`, or `z_e ≢ z_last·e` when they agree). Hence
`E[#shell ∩ Λ \ ℤ·u] = #{z ∈ ℤ^d : |z|² ∈ I, z ∉ ℤu}/q^m`. Exact theta-series counts
(`r_688(k)` by repeated squaring of the truncated theta series, floating point with exponent
tracking):

| squared-radius interval `I` | `log₂ #{z ∈ ℤ^688 : |z|² ∈ I}` | `log₂ E[#Λ ∩ shell]` |
| --- | --- | --- |
| `[4475, 4476]` (width 1) | 2329.5 | 281.8 |
| `[4469, 4482]` (width ≈ 13, `w = Θ(1/n)`) | 2332.4 | 284.7 |
| `[4400, 4550]` | 2340.4 | 292.8 |

So the thin-shell emptiness is purely the integer-spectrum effect: any shell containing an integer
squared norm has an expected population of about `2^282`. This is an ensemble mean only; S1's
concentration (one-percent bound), S2 degree counts and S3′ coverage remain open, as does the
wide-shell T1 itself.
