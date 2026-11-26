---
title: "Gaussian insertion can lose primitivity in a smooth block"
refs: []
tags: [lattice-attack]
---
*Moved from `docs/research/wall1_gaussian_blocks.md` (core v0.1.2).*

# Gaussian insertion can lose primitivity in a smooth block

For a width-two tour in dimension three, the law of the selected terminal quotient can be computed exactly. In the example below, as the Gaussian width grows, the first block satisfies arbitrarily strong dual smoothing bounds, yet the probability that the projected plant generates the unique shortest line tends to zero. The failure is arithmetic even though the terminal lattice has a strict length gap whenever the projected plant is nonzero.

## One insertion and its quotient law

Fix a prime $q$, let $L=\mathbb Ze_1+q\mathbb Ze_2+q\mathbb Ze_3$, and mark $u=e_1$. This is the modular kernel of the two coordinate checks on positions 2 and 3. Equivalently, take a uniform rank-two check matrix over $\mathbb F_q$ conditioned to annihilate $u$. Its last two columns form an invertible matrix, so every realization gives this lattice. Its only shortest vectors are $\pm u$ and its second successive minimum is $q$.

Start with the displayed ordered basis. In the first block draw a discrete Gaussian at width $s>0$, rejecting until its coefficient pair $(a,b)$ is primitive. Insert $v=(a,qb,0)$ unconditionally and complete the first block unimodularly. Thus the probability of each signed primitive pair is
$$
 p_s(a,b)=Z_s^{-1}\exp[-\pi(a^2+q^2b^2)/s^2],
$$
where $Z_s$ sums the numerator over all coprime pairs. Conditioning is well-defined because $(1,0)$ has positive mass and the full Gaussian sum converges. This specifies a transition on flags without a convention for completing the basis.

Indeed, choose integers $c,d$ with $ad-bc=1$ and put $w=(c,qd,0)$. For the orthogonal projection $P$ off $v$, the area of the planar parallelogram gives $\|Pw\|=q/\|v\|$. The inverse basis transform gives $Pu=-bPw$. Thus the exact law is the pushforward of $p_s$ under
$$
 (a,b)\longmapsto (Q,Pu),\qquad Q=\mathbb ZPw\ \perp\ q\mathbb Ze_3,\quad Pu=-bPw .
$$
Changing the oriented completion adds a multiple of $v$ to $w$ and leaves this formula unchanged. The next width-two block is the whole terminal quotient.

If $b\ne0$, then $\|v\|\ge q>1$ and $\pm Pw$ are the only shortest vectors. The projected plant itself generates their line as a lattice subgroup exactly when $|b|=1$. If $b=0$, the prefix already contains the plant and the terminal square grid has a tie. For example $q=2$, $(a,b)=(1,2)$ gives a unique shortest pair of length $2/\sqrt{17}$ and a projected plant of length $4/\sqrt{17}$. Merely testing the real direction of the plant would count this outcome as success. The distinction is the multiplicity condition in [the fixed-prefix criterion](wall1_planted_flags.md).

## Explicit probability and smoothing bounds

Even counting early capture as success, the probability is exactly
$$
 \frac{2e^{-\pi/s^2}+2e^{-\pi q^2/s^2}\sum_{a\in\mathbb Z}e^{-\pi a^2/s^2}}{Z_s}.
$$
The first term counts $b=0$, and every $a$ is allowed in each of the rows $b=\pm1$. The numerator is at most $4+2s$ by comparing the decreasing Gaussian on the positive half-line with its integral.

For $s\ge4q$ put $A=\lfloor s/2\rfloor$, $B=\lfloor s/(2q)\rfloor$. In $[1,A]\times[1,B]$ the number of pairs with any common divisor greater than one is at most
$$
 AB\sum_{k=2}^\infty k^{-2}\le AB(1/4+\int_2^\infty x^{-2}dx)=3AB/4 .
$$
Every remaining pair has weight at least $e^{-\pi/2}$. Including all four choices of signs gives $Z_s\ge AB e^{-\pi/2}\ge s^2 e^{-\pi/2}/(16q)$. Consequently success has probability at most $16e^{\pi/2}q(4+2s)/s^2$.

For the same block the dual is rectangular with spacings $1,1/q$. Writing $t=e^{-\pi(s/q)^2}$, its nonzero dual mass at parameter $1/s$ is at most
$$
 \left(1+2\sum_{j\ge1}t^j\right)^2-1=4t/(1-t)^2 .
$$
This uses $j^2\ge j$ in each coordinate. At fixed $q$ both the smoothing error bound and the success probability therefore tend to zero. Smoothing controls a Gaussian mass sum, while primitivity after projection depends here on a single integer coefficient.

## Scope for Wall 1

This computes one actual selected prefix, with an ideal primitive Gaussian oracle and unconditional insertion. It does not estimate the frequency of this block geometry in the plain-LWE embedding or the law after repeated tours. An improvement-only insertion changes the transition even in this example because the initial first vector is already shortest. For the requested random embedding, the missing estimate is a bound on projected multiplicity and competing lines under the visited-state distribution. No block size near 406 or running-time comparison with exact BKZ follows from this calculation.


## Independent audit (Nov 2026)

Verdict: **correct** (quotient law checked exactly for q ∈ {2,3,5} against brute-force enumeration; multiplicity |b| and
the limit confirmed; probabilities 0.718 / 0.307 / 0.129 at (q,s) = (2,8),(3,32),(5,128), decaying roughly like q/s). The counted
event includes b = 0, so it upper-bounds the probability of multiplicity one, as stated.
