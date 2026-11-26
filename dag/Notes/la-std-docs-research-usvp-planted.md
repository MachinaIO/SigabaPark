---
title: "The second minimum of a planted plain-LWE embedding"
refs: []
tags: [lattice-attack]
---
*Moved from `docs/research/usvp_planted.md` (core v0.1.2).*

# The second minimum of a planted plain-LWE embedding

Fix integer vectors e and s independently of the uniform matrix A over the
prime field of order q. Write m for the number of rows, n for the number of
columns and d=m+n+1. Define b=As+e in the field, p=(e,s,1), and
L={z=(x,y,t) integral : x+Ay=tb modulo q}. The syndrome map is onto
through x, so the index and covolume are exactly q^m for every A.
All probabilities below are over A with e,s fixed. Conditioning additionally
on an observed value of b would change this law.

## Finite-radius theorem (paper proof, pending independent audit)

Let B bound the absolute coordinates of e and s. Let V_d be the volume of
the Euclidean unit ball and G=(q^m/V_d)^(1/d). If R sqrt(1+B²)<q then

    Pr[there exists z in L outside Zp with ||z|| ≤ R]
       ≤ ((R+sqrt(d)/2)/G)^d.

In particular the same bound applies to Pr[λ₂(L) ≤ R]. When ||p|| ≤ R
the two events coincide, since the last coordinate makes p primitive.

Indeed set u=y-ts and v=te-x modulo q. Membership is Au=v. For u nonzero,
each row gives one surjective linear functional, so membership has probability
q^(-m). For u=0 membership is deterministic and requires v=0. In that
case every coordinate difference z_i-t p_i (i before the last coordinate)
is divisible by q, and Cauchy–Schwarz bounds its absolute value by
sqrt(1+B²) ||z||. Thus every difference vanishes over the integers.
Summing the remaining membership probabilities bounds the probability of
any independent point. The unit cubes at integer points of the closed
ball have disjoint interiors and lie in the ball of radius R+sqrt(d)/2.
This yields the displayed bound without an independence assumption on points.

For any fixed 0<c<1 take R=cG-sqrt(d)/2 when positive and below the
wraparound threshold. Failure is at most c^d. At m=2n, bounded B, and
primes q of order n^a for a>3/2, Stirling's formula gives
G asymptotic to sqrt(d/(2πe)) q^(m/d), hence G=o(q) and sqrt(d)=o(G).
This gives any fixed fraction below G with exponentially small failure.
It applies to the first moment. The growing-order shell statistics in
qary_crypto_shapes.md require additional estimates.

As a finite plain-matrix example, m=1024, n=512, q=3329, B=3 and R=1000
satisfy the wraparound test since 10·1000² < 3329². The exact bound is
V_1537 (1000+sqrt(1537)/2)^1537 / 3329^1024. Numerically G≈2113.39
and the base-two logarithm of the bound is approximately −1616.24.
No module rotations or structure are modeled. At fixed q one cannot take
a positive constant fraction of G uniformly in dimension at ratio two:
two independent coordinate vectors scaled by q give λ₂ ≤ q while G grows.

## Projection counts and the outstanding conditioning problem

For the orthogonal projection onto p-perp, every projected lattice point
has a unique lift in the half-open slab 0 ≤ <z,p> < ||p||²: differences
of lifts on the line are integral multiples of p. Consequently a bounded
window W in that hyperplane gives a finite deterministic list T of
integer lifts in the slab with projection in W. Its expected lattice count
is exactly the number in T with u=v=0 plus q^(-m) times the number with
u nonzero. For ordered tuples of lifts, form X with rows u and right-hand
sides from the v's. Joint membership has probability zero if any syndrome
column lies outside the image of X, and q^(-m rank X) otherwise, by
translation of each feasible affine fibre. This gives factorial moments
for fixed windows by summing over distinct lifts.

A reduced basis chosen from A makes its projected block and target window
depend on A. Substitution of that random window into a fixed-window average
does not establish the conditional counts. Neither their concentration nor
the corresponding BKZ success law is proved here.

## Machine-checked scope

In namespace SigabaNeo.Planted, planted_iff is the modular equivalence with
Au=v. affineCount gives q^((n-rank X)m) solutions for every feasible
system with m right-hand sides, using QAry.kernelCount (the counting
identity underlying QAry.meanValue). lift_multiple turns coordinatewise
residue equality into integer equality given strict discrepancy bounds.
The Euclidean estimate, probability inequality, projection argument and
numerical evaluation above have paper status. All three Lean declarations
print only propext, Classical.choice and Quot.sound.
