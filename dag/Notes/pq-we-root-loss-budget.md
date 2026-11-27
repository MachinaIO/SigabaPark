---
title: Width-matched root hybrids and a quantitative conditional security ledger
refs: [definition:WE_CircuitSAT, note:pq-we-quantum-prefix-tree, note:pq-we-quantum-preimage-hop]
tags: [witness-encryption, reduction, complexity, correctness]
---

**Objective.** In the induction of [VWW Lemma 5.2](https://ntt-research.com/wp-content/uploads/2023/01/Witness-encryption-and-null-iO-from-evasive-LWE.pdf), the second error in a PRE challenge becomes the prefix-table error for the next depth. The following is a sufficient *stage-indexed* version. It makes all widths and loss multipliers explicit and is conditional on a quantitative quantum evasive-LWE premise for the specified classical sampler family. It does not assert that this premise holds or that it follows from ordinary LWE. In particular one cannot freely substitute an induction hypothesis proved for a larger noise width to hide a table with smaller noise.

**Experiments.** Fix one message and one false statement, and write D_i(T) for an upper bound on quantum distinguishing advantage at time T in the depth-i root-table experiment, including its suffix and the public factor list used in the proof. Use fresh Gaussian table errors of width f_i. At depth H there is no suffix, so D_H<=beta_H, where beta_i is the bound for the isolated prefix table at the same width f_i from the preceding note. A near-uniform public key incurs its marginal error when switched; include these in the endpoint allowances below. Each induction stage i=1,...,H-1 uses the actual stacked prefix secret S_i, both next targets P=[F_(i+1,0) A_(i+1)+E_0 | F_(i+1,1) A_(i+1)+E_1], and the correlated future suffix and factors as aux, as in VWW. Its PRE first error has width f_i and its PRE second error width f_(i+1). The POST preimage width must equal the corresponding honest transition width and its key and error laws must match. Only f_1 is an honest root noise width. The other f_i concern the proof experiments.

Assume for this sampler that POST advantage at time T is bounded by Q_i times PRE advantage at the induced time, plus eta_i. Include key and implementation switches in an additive post-scale term z_i, charging each switch on the side on which it occurs (a PRE switch is multiplied by Q_i). First flood out the shift S_i [E_0|E_1] in PRE, at statistical cost s_i. The resulting second component is exactly the depth-(i+1) table with width f_(i+1), up to a public reshaping. In this replacement the wrapper can simulate the first component from the revealed factors and an independent key. Next replace the first component by uniform using the depth-i isolated prefix bound; the independent uniform second component and the future suffix can be simulated given the factors. Thus

    D_i(T_i) <= Q_i (D_(i+1)(T_(i+1)) + beta_i(T_(i+1)) + s_i) + z_i.

T_(i+1) must cover the maximal induced PRE test and both simulations; e.g. take the assumed PRE time overhead on T_i plus the larger simulation time. Estimate beta_i at that induced time including the tree-generation cost of its own LWE wrappers. A polynomial loss symbol with no numerical value is not a security-bit estimate. Let W_i=product of Q_1,...,Q_i and W_0=1. The resulting bound is W_(H-1) beta_H plus the sum over i<H of W_i(beta_i+s_i)+W_(i-1)z_i. For H=1 only beta_1 remains. To bound the message-bit gap, discard any proof-only factor leakage, replace the remaining transitions by their message-independent comparison law using the preimage-hop bound, and sum the resulting bounds for messages zero and one. The two comparisons need the same public framing, dimensions, and ideal output law. Eta_i and all sampler errors have to be included for each message. This derives an advantage expression for the stated quantum experiment; it does not change the adversary type of the existing DAG definition.

**Exact shift moment.** Use the earlier notation n for tensor dimension, m for column count, v for the variance of a centered independent tensor entry, e_t for the variance of a fresh centered late transition error and U_i=sum_x ||alpha_x||² for depth i. Then

    E || S_i [E_0 | E_1] ||_F² = 2m e_t n (nv)^i U_i.

For a path x, the squared Frobenius norm of its stacked block alpha_x tensor S_x is ||alpha_x||² ||S_x||_F². Multiplication by one new independent square factor multiplies expected squared norm by nv, starting from n for the identity. Conditional on the entire prefix, right-multiplication by the concatenated noise contributes 2m e_t times the squared norm. Shared columns across paths do not change the sum of expected squares. The independent flooding Gaussian gives s_i <= sqrt(pi E||shift||²/2)/f_(i+1), by the relative-entropy shift calculation in the prefix-tree note. For the isolated table beta_i the statistical term is at most sqrt(pi L_i/2)/f_i with L_i as in that note. Any computational LWE term in beta_i is charged separately at weight W_i (W_(H-1) for the base). The formula assumes ideal centered entries and independent fresh noises as specified. A non-centered implementation needs an additional bias analysis or a statistical switch.

**Choosing widths.** Hold the quantum premise parameters, multipliers and times fixed provisionally. Supply minimum width ratios g_i>=1 required by that premise and define G_i as the product of ratios before depth i. Aggregate the two types of flooding into coefficients c_i so the weighted flooding cost is bounded by sum_i c_i/f_i. The code uses ceiling square roots and pi<4 to bound these coefficients with integers. Under f_i>=g_i f_(i+1), any fixed f_1 permits f_i<=f_1/G_i; taking equality minimizes this upper bound. To spend at most epsilon on flooding it suffices to take f_1>=sum_i c_i G_i / epsilon. For integer g_i the listing returns the smallest integral last-stage width with exact adjacent ratios and this rounded certificate. It does not optimize the other terms or solve for the assumed Q_i. Recheck the hardness, PRE time, preimage widths, correctness noise and honest modulus against the chosen f_1. If g_i and Q_i are at most polynomial in an exponentially sized prefix table, their logarithms accumulate polynomially in H and log(lambda); this accounting alone does not force exponential *bit lengths* for f_1. A proof of the premises at those parameters is still essential.

**Control.** For the eight-level shear/identity example in the linked prefix note, Q_i=2 and g_i=4 are illustrative inputs, not established security constants. At n=4, m=16 and unit entry variances, a flooding-only budget of 2^-32 gives f_1=1977060109477344182272 and f_8=120670172697591808. These are proof-width controls; this is not a 32-bit secrecy result. Across 200 deterministic test cases the weighted closed form equaled the expanded recurrence exactly and decreasing the terminal width by one violated the requested certificate when it was greater than one.

~~~python
from fractions import Fraction as F
from math import isqrt,prod

def ceil_sqrt(x):
    x=F(x)
    a=isqrt(x.numerator//x.denominator)
    return a+int(a*a<x)

def schedule(energies,n,m,v,fresh,late,multipliers,gaps,flood_budget):
    # energies[i-1] = sum of squared logical prefix norms at depth i.
    H=len(energies)
    if H<1 or len(gaps)!=H-1 or len(multipliers)!=H-1:
        raise ValueError("inconsistent height")
    if min(n,m)<1 or min(v,fresh,late)<0 or not 0<flood_budget<=1:
        raise ValueError("invalid moment or budget")
    if any(g<1 for g in gaps) or any(c<1 for c in multipliers):
        raise ValueError("invalid loss or width ratio")
    W=G=1
    coeff=[0]*H
    moment=F(0)
    for i,U in enumerate(energies):
        moment=fresh+n*F(v)*moment
        prefix=ceil_sqrt(2*n*m*U*moment)
        if i==H-1:
            coeff[i]+=W*prefix
        else:
            W*=multipliers[i]
            coeff[i]+=W*prefix
            shift=ceil_sqrt(4*n*m*U*(n*F(v))**(i+1)*late)
            coeff[i+1]+=W*shift
    ratios=[1]
    for g in gaps:
        ratios.append(ratios[-1]*g)
    # Require integral widths and exact adjacent ratios.
    scaled=sum(c*g for c,g in zip(coeff,ratios))
    required=F(scaled,ratios[-1])/flood_budget
    unit=max(1,-(-required.numerator//required.denominator))
    return [unit*(ratios[-1]//g) for g in ratios],coeff

def unfold(base,prefix,shift,gain,post_error):
    value=F(base)
    for i in reversed(range(len(gain))):
        value=gain[i]*(value+prefix[i]+shift[i])+post_error[i]
    return value
~~~
