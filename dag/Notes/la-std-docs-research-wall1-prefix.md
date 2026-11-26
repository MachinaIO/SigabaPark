---
title: "Prefix covolumes and the terminal BKZ profile"
refs: []
tags: [lattice-attack]
---
*Moved from `docs/research/wall1_prefix.md` (core v0.1.2).*

# Prefix covolumes and the terminal BKZ profile

For exact, fully BKZ-reduced bases there is a deterministic cutoff for the audited Haar flag estimate. It can be computed for **all** prefix ranks in one backward pass. Using this cutoff in the flag estimate loses hundreds of bits of *length ratio* in several dimensions below. Propagating an ambient shortest-vector lower bound through reducedness gives a much stronger Haar profile in these examples.

## Deterministic prefix envelope

Index from zero. Put $g_i=\|b_i^*\|$, $S_j=\sum_{i<j}\log g_i$, and first normalize $S_n=0$. Use the shortest-in-every-projected-block definition in [Reduction/BKZ.lean](../../SigabaNeoStd/Lattices/Reduction/BKZ.lean). The first vector remains shortest when a block is truncated on the right, because the sublattice contains that vector. Thus for every $2\le d\le\min(\beta,n-i)$,
$$
d(S_{i+1}-S_i)\le S_{i+d}-S_i+d c_d.
$$
Indeed the block determinant is the product of its GS lengths and Hermite bounds its squared minimum by $\gamma_d$ times its determinant to the power $2/d$. Take $c_d=\tfrac12\log\gamma_d$ if known. For computation take $c_d=\log h_d/(2d)$ in dimensions 2 through 8, with the classical values $h_d=\gamma_d^d$ equal to $4/3,2,4,8,64/3,64,256$, respectively. Otherwise take $c_d=\tfrac12\log(2/\pi)+\log\Gamma(2+d/2)/d$ by Blichfeldt. This is a fixed-point reducedness argument. A tour count for first-vector quality alone does not establish its hypothesis. [Hanrot–Pujol–Stehlé](https://perso.ens-lyon.fr/damien.stehle/downloads/bkz.pdf)

Set $u_n=u_{n-1}=0$. For $j=n-1,\ldots,1$ compute
$$
u_{j-1}=\max_{2\le d\le\min(\beta,n-j+1)}
\frac{d u_j-u_{j+d-1}-d c_d}{d-1},\qquad
U_j=u_j-(1-j/n)u_0.
$$
Define $U$ by the latter formula also at the endpoints. Then **$S_k\le U_k$**. In fact $U$ satisfies every block inequality, has zero endpoints, and has an active inequality at every interior index. These properties follow by construction since adding an affine function preserves the inequalities. At a positive maximum of $S_j-U_j$, choose an active $d$ for $U$. Subtraction bounds the maximum by the weighted average of the differences at $j-1$ and $j+d-1$ with positive weights $(d-1)/d,1/d$. Its left neighbor must attain that maximum too. Taking the leftmost maximizer contradicts the zero boundary. Since $U$ itself is feasible, this is the exact common upper envelope of the stated linear inequalities. Geometric realizability of the extremizer by a lattice basis is open here. For covolume $D$, rescaling gives $\det W_k\le D^{k/n}e^{U_k}$. The proof uses BKZ throughout and does not assume that slide-reduced bases satisfy every overlapping block condition.

## Two Haar lower profiles and an upper-prefix bootstrap

Fix a rank $k=n-b$, $2\le b\le\beta$, and failure probability $0<\epsilon<1$. Write $X=e^{U_k}$. Every basis prefix is primitive. For $k>0$ the audited flag estimate gives $g_k>R$ with probability at least $1-\epsilon$, simultaneously for every fully reduced basis of the random lattice, where
$$
R=\max\left\{X^{-1}(\epsilon/A(n,k+1))^{1/n},
\left[\frac{(n+1)\epsilon}{n A(n,k) A(b,1) X^{n+1}}\right]^{1/b}\right\}.
$$
Here $A(m,j)=m^{-1}\binom mj\prod_{i=1}^j V_{m-i+1}Z_i/(V_i Z_{m-i+1})$, $V_i=\pi^{i/2}/\Gamma(1+i/2)$, $Z_1=1$, $Z_i=\zeta(i)$ otherwise. Indeed $g_k$ is the projected minimum in this terminal block and the bad event is contained in Part 5's event at $(X,R)$. For $k=0$ use $R=T=(\epsilon/A(n,1))^{1/n}$ directly by Markov on primitive lines. Across several ranks one may allocate errors summing to $\epsilon$. [Audited proof](wall1_sublattice.md) and [Kim](https://arxiv.org/abs/2005.10874)

A single ambient line-count event gives a different, simultaneous profile. For each target $t$ set $p_t^{(t)}=0$ and work leftward. Suppressing the superscript, take
$$
p_i=\min_{2\le d\le\min(\beta,t+1-i)}
\frac{d c_d+\sum_{i<h<i+d}p_h}{d-1}.
$$
The block inequality, solved for $\log g_i$, proves inductively $\log(g_i/g_t)\le p_i$. On the event $\lambda_1(L)>T$ we have $g_0>T$ and therefore $g_t>T\exp(-p_0^{(t)})$ for every $t$, including $t=0$. Multiplying the suffix lower bounds gives the alternative Haar upper prefix cutoff
$$
S_k\le\min\{U_k,\;-(n-k)\log T+\sum_{t=k}^{n-1}p_0^{(t)}\}.
$$
One can use this random-event cutoff in Part 5 with a second error budget. More generally a Part 5 lower bound $g_i>r_i$ at a deterministic cutoff propagates to $g_t>r_i\exp(-p_i^{(t)})$ for $t\ge i$. Maximize these lower bounds before multiplying over the suffix. Each new invocation at a tightened cutoff uses its unconditional simultaneous event and a union bound with the previous budgets. This supplies an induction without any independence assumption. Pointwise one may also select the larger of the two tabulated radii at the same confidence *before* sampling, since the choice depends only on parameters.

## Numerical comparison

Set $b=\beta$ and $\epsilon=0.01$ per row. The heuristic GSA comparison uses $\delta=[(\pi\beta)^{1/\beta}\beta/(2\pi e)]^{1/(2(\beta-1))}$ and $G=\delta^{n-2k-1}$. All numerical columns are base-two logarithms, rounded for display. The last column uses the ambient line count and propagation alone. The exact expressions above specify the certificates. [70-decimal-digit table script](../../python/wall1_prefix.py)

| $n$ | $\beta$ | $\log_2 X$ | $\log_2 R$ (Part 5) | $\log_2 G$ | $\log_2(G/R)$ | propagated log radius |
|---:|---:|---:|---:|---:|---:|---:|
| 200 | 50 | 224.81648 | -155.05271 | -1.7474773 | 153.30523 | -8.1076072 |
| 200 | 100 | 197.2187 | -101.7687 | -0.013296053 | 101.75541 | -3.6961494 |
| 200 | 200 | 0.0 | 1.7698576 | 1.7980709 | 0.02821327 | 1.7698576 |
| 200 | 400 | — | — | — | — | — |
| 400 | 50 | 519.78634 | -418.55047 | -5.2078285 | 413.34264 | -19.37362 |
| 400 | 100 | 579.89154 | -401.91978 | -2.6725067 | 399.24727 | -10.909768 |
| 400 | 200 | 490.90408 | -249.74082 | -0.0090355321 | 249.73179 | -5.0956644 |
| 400 | 400 | 0.0 | 2.2735936 | 2.2877017 | 0.014108138 | 2.2735936 |
| 700 | 50 | 961.48431 | -836.81231 | -10.398355 | 826.41395 | -36.624643 |
| 700 | 100 | 1149.2917 | -914.16643 | -6.6613227 | 907.5051 | -21.855726 |
| 700 | 200 | 1204.0108 | -805.1792 | -2.7196952 | 802.4595 | -11.934878 |
| 700 | 400 | 895.17267 | -412.23698 | 0.56762523 | 412.8046 | -5.9453726 |

The dash denotes an inadmissible block size. At $(700,200)$ propagation brings the deficit down from 802.46 to 9.22 bits of length. At full dimension the small deficit comes from the ambient line count. Neither comparison measures runtime.

## Planting and polynomial modulus

The strict projected-vector test needs a reference height and an upper bound on the projected target length **in the same experiment**. In a fully reduced planted basis with a nonzero target projection into the terminal block, the opposite weak inequality holds identically: $g_k=\lambda_1(Q)\le\|\pi v\|$. If the projection vanishes, the strict numerical test supplies no new projected vector. The usual insertion test concerns the height *before* the target wins the block, or a modeled background height. Even a theorem for an unplanted Haar background requires a coupling to that height and control of the target projection to certify insertion. The Haar results therefore determine no certified planted block size, and a numerical difference in block sizes from the GSA estimator is undefined. Full-dimensional exact SVP returns the target up to sign under a separate unique-shortest-pair hypothesis.

For every full-rank integer modular kernel, including polynomial prime $q$, the deterministic envelope and propagation apply after scaling by $D^{-1/n}$; for an $m$-row check matrix of rank $a$ modulo $q$, the image has size $q^a$ and $D=q^a$. In original coordinates $g_0\ge1$ gives the unconditional bound $g_t\ge e^{-p_0^{(t)}}$. Also the squared rank-$(k+1)$ prefix determinant is a sum of squares of integer minors, at least one positive. Dividing the rank-$(k+1)$ volume by the rank-$k$ volume gives $g_k\ge D^{-k/n}e^{-U_k}$ in original units. Both deterministic arguments extend to any integral full-rank embedding with its actual determinant.

At fixed $n,q$ the normalized modular-kernel distribution has finite support; Haar's expected primitive-line and flag counts do not follow by rescaling. An asymptotic transfer would require a quantitative count for the growing dimensions, ranks and cutoffs used here. For independent uniform columns, a fixed coordinate prefix gives the quotient-column law conditional on those prefix columns. BKZ selects real prefix spans using the same input, and planting or module structure further changes its distribution. The fixed-coordinate result provides neither count nor coupling for that selection. [Coordinate calculation](avg_bkz.md), [selection obstruction](avg_bkz3.md), and [project status](../PROOF_GAP.md)

## Independent audit (Nov 2026)

Verdict: **correct**, no hidden heuristic. Every table entry reproduces (`uv run --with mpmath`); exact LPs
(scipy) for `(n,β) ∈ {(12,4),(20,6),(30,10),(40,12),(60,20)}` confirm both recursions equal their LP optima
(so the 9.22-bit deficit at `n = 700, β = 200` is the exact value of this LP; closing it needs sharper proven
Hermite bounds than Blichfeldt or extra structure). Hermite constants used are proven (exact for `d ≤ 8`,
Blichfeldt otherwise). The propagation is a Schnorr-type ratio bound `g_t ≥ g_0·e^{−p_0^{(t)}}`; the only random
input is `g_0 ≥ λ1(L)`. Wording gaps: the Part 5 bound applies to `g_i` only when `n − i ≤ β`; the q-ary "image of
size `q^a`" sentence is ambiguous about the side. Applies to fully BKZ-reduced bases; producing one (BKZ cost)
is not addressed.
