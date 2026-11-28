"""Statistics of the learning extension (spec sections 7.1 and 8.6), standard library only.

* `wilson`: the Wilson score 95% interval of a binomial proportion (a calibration estimate under
  the assumed independent sampling model; `None` when n = 0, never "0%").
* `cp_lower` / `cp_upper`: one-sided Clopper-Pearson bounds, computed exactly. The binomial tail
  is evaluated in integer arithmetic at dyadic points p = m / 2^B, and bisection keeps the
  conservative side: the returned lower bound is at most the exact one, the upper bound at least
  it, each within 2^-B (B = 40). Endpoints: `cp_lower(0, n) = 0`, `cp_upper(n, n) = 1`.
* `cp_union`: method `cp-union-v1`, the paired lower bound on the improvement
  `LB = CP_lower(w, n, alpha/2) - CP_upper(l, n, alpha/2)`, and for reporting the matching upper
  bound `UB = CP_upper(w, n, alpha/2) - CP_lower(l, n, alpha/2)`. By the union bound the two
  one-sided bounds hold together with probability at least 1 - alpha under the IID pair model,
  without assuming the win and loss counts independent.
"""

from __future__ import annotations

import math
from fractions import Fraction

METHOD = "cp-union-v1"
METHOD_VERSION = "1"
PRECISION_BITS = 40
Z95 = 1.959963984540054


def wilson(successes: int, n: int, z: float = Z95) -> tuple[float, float] | None:
    if n == 0:
        return None
    if not 0 <= successes <= n:
        raise ValueError("successes out of range")
    p = successes / n
    z2 = z * z
    den = 1 + z2 / n
    centre = (p + z2 / (2 * n)) / den
    half = z * math.sqrt(p * (1 - p) / n + z2 / (4 * n * n)) / den
    return (max(0.0, centre - half), min(1.0, centre + half))


def _terms(n: int, m: int, d: int) -> list[int]:
    """C(n,i) m^i (d-m)^(n-i) for i = 0..n (integers; the probabilities times d^n)."""
    a = [1] * (n + 1)
    b = [1] * (n + 1)
    for i in range(1, n + 1):
        a[i] = a[i - 1] * m
        b[i] = b[i - 1] * (d - m)
    return [math.comb(n, i) * a[i] * b[n - i] for i in range(n + 1)]


def _check(x: int, n: int, a: Fraction) -> None:
    if n < 1 or not 0 <= x <= n:
        raise ValueError("need 0 <= x <= n and n >= 1")
    if not 0 < a < 1:
        raise ValueError("the level must be in (0, 1)")


def cp_lower(x: int, n: int, a) -> float:
    """The largest dyadic p with P(X >= x; p) <= a: a conservative one-sided lower bound at
    level 1 - a."""
    a = Fraction(str(a)) if not isinstance(a, Fraction) else a
    _check(x, n, a)
    if x == 0:
        return 0.0
    d = 1 << PRECISION_BITS
    total = d ** n
    lo, hi = 0, d
    while hi - lo > 1:
        mid = (lo + hi) // 2
        tail = sum(_terms(n, mid, d)[x:])
        if tail * a.denominator <= a.numerator * total:
            lo = mid
        else:
            hi = mid
    return lo / d


def cp_upper(x: int, n: int, a) -> float:
    """The smallest dyadic p with P(X <= x; p) <= a: a conservative one-sided upper bound."""
    a = Fraction(str(a)) if not isinstance(a, Fraction) else a
    _check(x, n, a)
    if x == n:
        return 1.0
    d = 1 << PRECISION_BITS
    total = d ** n
    lo, hi = 0, d
    while hi - lo > 1:
        mid = (lo + hi) // 2
        cdf = sum(_terms(n, mid, d)[:x + 1])
        if cdf * a.denominator <= a.numerator * total:
            hi = mid
        else:
            lo = mid
    return hi / d


def cp_union(w: int, l: int, n: int, alpha) -> dict:
    """The paired bounds of method `cp-union-v1` (all None when n = 0)."""
    alpha = Fraction(str(alpha))
    if n == 0:
        return {"lower_bound": None, "upper_bound": None, "delta_hat": None}
    if w + l > n or w < 0 or l < 0:
        raise ValueError("need w + l <= n")
    half = alpha / 2
    lb = cp_lower(w, n, half) - cp_upper(l, n, half)
    ub = cp_upper(w, n, half) - cp_lower(l, n, half)
    return {"lower_bound": lb, "upper_bound": ub, "delta_hat": (w - l) / n}


def paired_counts(pairs: list[tuple[int, int]]) -> dict:
    """Aggregates of (incumbent, candidate) binary outcome pairs."""
    n = len(pairs)
    return {"n": n,
            "incumbent_successes": sum(a for a, _ in pairs),
            "candidate_successes": sum(b for _, b in pairs),
            "w": sum(1 for a, b in pairs if a == 0 and b == 1),
            "l": sum(1 for a, b in pairs if a == 1 and b == 0),
            "both_solved": sum(1 for a, b in pairs if a == 1 and b == 1),
            "both_failed": sum(1 for a, b in pairs if a == 0 and b == 0)}
