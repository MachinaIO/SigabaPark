---
title: "The terminal shell is empty at the proposed plain-LWE shape"
refs: []
tags: [lattice-attack]
---
*Moved from `docs/research/planted_polyq.md` (core v0.1.2).*

# The terminal shell is empty at the proposed plain-LWE shape

**Proposition.** Set $q=3329, m=175, n=512, d=m+n+1=688$. For every
integer lattice of covolume $q^m$ contained in $\mathbb Z^d$, the terminal
shell in §3.1 of [the sieve note](provable_sieving.md) is empty. Consequently
the probability over the public matrix of simultaneous S1, S2 and S3′ is zero,
including after conditioning on any fixed secret and error.

**Proof.** Work in the original integer coordinates. The ball of volume
$q^m$ has radius $G=q^{m/d}(344!)^{1/d}/\sqrt{\pi}$, by the even-dimensional
ball volume formula. The prescribed terminal radius is
$R=\sqrt{4/3}\exp(1/7)G$, since $\lceil\log 688\rceil=7$.
Write $w=688^{-2}$. The squared radial interval satisfies

$$
4475 < R^2(1-w)^2 < R^2(1+w)^2 < 4476 .
$$

The two endpoints are approximately 4475.66103 and 4475.69885. The following
exact rational certificate verifies the outer inequalities after taking
344th powers. The exponential tail after degree 12 is bounded by its first
term times the sum of a geometric progression of ratio $u/14$.
The bounds on π below also follow by inserting the alternating arctangent
series through degrees 13 and 15 into Machin's formula
$\pi=16\arctan(1/5)-4\arctan(1/239)$.

```python
from fractions import Fraction as F
from math import factorial

u = F(2, 7)
lo = sum(u**i / factorial(i) for i in range(13))
hi = lo + u**13 / factorial(13) / (1-u/14)
N = 3329**175 * factorial(344)
w = F(1, 688**2)
a = (1-w)**2 * F(4,3) * lo / F(314159266, 10**8)
b = (1+w)**2 * F(4,3) * hi / F(314159265, 10**8)
assert 4475**344 < a**344 * N
assert b**344 * N < 4476**344
```

Every squared length in the lattice is a sum of integer squares. Hence the
shell contains no lattice point. Its continuum volume is strictly positive
because its outer radius exceeds its positive inner radius. This contradicts
the S1 lower bound of 99 percent of the covolume-normalized volume. ∎

**Coverage.** If the nonzero planted vector has norm at most
$(1+1/7)G$, S3′ also fails for every matrix because the difference set of
the empty terminal shell is empty. The S1 conclusion needs no length bound
on the planted vector. Deleting its multiples cannot restore shell occupancy.

**Extent of the obstruction.** For any dimension and any integral squared-length
spectrum, the same proof applies whenever the closed squared radial interval
lies strictly between successive integers. Its exact width is $4wR^2$.
A width below one alone does not imply emptiness. The numerical certificate
is specific to the stated parameters and the exact volume-one radius. It
does not decide S2 separately or the asymptotic question for other polynomial
moduli and dimensions.

**Formalization.** `SigabaNeo.PolyQ.shell_empty_of_sq_gap` proves the general
interval criterion for any set with integer squared norms. The ball volume
substitution and the concrete endpoint certificate above are paper results.
