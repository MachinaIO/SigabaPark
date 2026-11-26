---
title: Bounded bit-clock gadget setup and reusable coset basis for tensor encryption
refs: [definition:WE_CircuitSAT, note:pq-we-clocked-gaussian, note:pq-we-compiler-transport]
tags: [witness-encryption, sampling, complexity]
---

A tensor encoder repeatedly asks for short columns x with Ax=y modulo q. Here is a bounded reference realization of setup and the column sampler, for integer q >= 2. It specializes the gadget trapdoor of [Micciancio and Peikert](https://eprint.iacr.org/2011/501.pdf) and the backward basis sampler of [Gentry, Peikert and Vaikuntanathan](https://web.eecs.umich.edu/~cpeikert/pubs/trap_lattice.pdf). All centers and squared widths are computed exactly. The elementary construction has polynomial overhead and a conservative public Gaussian width. Using it in the full WE parameter selection requires recomputing noise growth with that width.

**Matrix and basis.** Let n be the number of syndrome rows, k = ceil(log2 q), ell = nk, G the block gadget with digits 1,2,...,2^(k-1), and d=h+ell. Publish A = [U | G-UR] for a nearly uniform n by h matrix U and an independent h by ell uniform binary R. The integral shear (a,t) maps to (a+Rt,t), on which A acts as Ua+Gt. To lift y set a=0 and let t contain its standard binary residues. A basis in shear coordinates first has h columns (e_j,digits(-U_j)), then the gadget kernel in the last ell coordinates. In one gadget block its first k-1 relations are 2e_i-e_(i+1). The last relation is digits(q) for q<2^k and 2e_(k-1) for q=2^k. The first relations identify every coordinate with its binary multiple of the first in the quotient, and the last kills precisely q times the first. Thus this is a full kernel basis even for composite q. Eliminating a with the first h columns proves fullness for the combined matrix. The shear has determinant one. Every resulting column has Euclidean norm at most sqrt(d)(ell+3), since the digit corrections have l1 norm at most ell and a carry has l1 norm at most three.

**Public matrix distribution.** With exactly uniform U, distinct binary r,r' collide under U with probability q^(-n) because one coefficient of r-r' is a unit. For uniform r, the expected collision probability conditioned on U is at most 2^-h + q^-n. Cauchy-Schwarz gives mean total variation from uniform at most (1/2)sqrt(q^n/2^h). Conditioned on U the columns are independent. Telescoping their product bounds joint distance for the public A by ell times the one-column bound. Taking h = nk + 2(b+ceil(log2 ell)) costs at most 2^(-b-1) here. Generating each entry of U from p=k+ceil(log2(nh))+b+1 uniform bits modulo q adds at most nh q/2^p <= 2^(-b-1), by data processing before forming A. This controls the public matrix marginal; the trapdoor stays private.

**Backward sampling.** Cache the rational Gram-Schmidt vectors u_i of the basis columns v_i and squared norms N_i. Starting at the lift x, work backwards, adding z_i v_i, with center -<x,u_i>/N_i and scalar squared width W_i=sigma²/N_i. Implement the shell sampler with L=ceil(sqrt(W_i)) computed by integer square root, and exponent argument (j-c)^2/W_i. Its proof applies unchanged when W_i >= 1. Even the timeout output stays in the coset. For fixed W_i the one-dimensional normalizing sum divided by sqrt(W_i) differs from one by at most epsilon_i = 2 exp(-pi W_i)/(1-exp(-pi W_i)), by Poisson summation and bounding the nonzero Fourier modes by a geometric series, uniformly in the center. Orthogonality makes the product of unnormalized weights exactly exp(-pi ||x_final||²/sigma²), because later backward updates preserve the already fixed projections. As the integer coefficient tuple is unique, the ideal sequential law and the desired coset Gaussian have pointwise likelihood ratios between 1/J and J, where J = ((1+epsilon)/(1-epsilon))^d and epsilon = max epsilon_i. Their total variation is at most J-1. For b>=1, set T=b+ceil(log2 d)+4 and public sigma²=d(ell+3)^2 T. Then W_i>=T, epsilon<=4 exp(-pi T)<=2^(-T), and log J <= 3d epsilon <= 3 times 2^(-b-4). Hence J-1 <= 2^(-b-1). Giving each bounded scalar draw precision b+ceil(log2 d)+1 adds at most another 2^(-b-1). Budget b separately across setup calls and columns for the desired encryption-level error.

**Worst-case cost.** One exact orthogonalization takes O(d³) rational operations per key. Each new column uses O(d²) rational operations in addition to d bounded scalar draws. The entries of the residual x stay integral. Projection entries have polynomial bit length by the determinant formula for Gram-system projection and Hadamard's inequality on the bounded integer columns. Every update increases the residual norm by at most a multiplicative factor 1+||v_i||/||u_i|| and an additive O(t ceil(sqrt(W_i))||v_i||), from the shell support or fallback. The logarithms of these factors are polynomial in the input lengths, so d updates preserve polynomial bit length on every path. Exact fractions in the classical Gram-Schmidt sums have polynomial bit length too, using the common Gram determinant denominators of each individual projection and summing at most d projections per output vector. For polynomially many columns this supplies a worst-case polynomial bit clock. The width bound may be costly in practice. The WE error parameters, tensor-factor and root noise samplers, full encryption and decryption clocks in the registered machine model, and a quantum-valid security reduction remain separate obligations.

**Reference checks.** Across q=2,...,19 and two matrix shapes, the 36 generated bases had determinant of absolute value q^n and every column had zero syndrome. All 108 sampled preimages passed their target congruences, including forced scalar timeouts. A second test used the binary setup algorithm and the public width rule for q in {2,3,8,13,17,257}. All 18 columns with targets (M tensor S)y satisfied the requested congruences. The tests used small parameters and check exact algebra. Distributional guarantees above are analytic.

~~~python
from fractions import Fraction as F
from functools import lru_cache
from math import ceil, isqrt

@lru_cache(None)
def pi_approx(bits):
    # For both arctangents the alternating remainder is below 5^(-2N-1).
    N = bits + 4
    def atan_inv(k):
        return sum((F((-1)**j, (2*j+1)*k**(2*j+1)) for j in range(N)), F(0))
    unit = 1 << (bits+2)
    return F(int((16*atan_inv(5) - 4*atan_inv(239))*unit),unit)

def threshold(v, p):
    # v = ((j-center)/width)^2. Return a p-bit coin threshold.
    d = ceil(4*v).bit_length()
    guard = p + d + 5
    x = pi_approx(guard)*v/(1 << d)
    unit = 1 << guard
    x = F(int(x*unit),unit)
    term = total = F(1)
    for i in range(1, guard+3):
        term *= -x/i
        total += term
    a = max(0,min(unit,int(total*unit)))
    for _ in range(d):
        a = a*a//unit
    return a >> (guard-p)

def sample_squared(center, width2, b, bits):
    # Exact rational input, width >= 1, b >= 1. bits(k) supplies k uniform bits.
    assert width2 >= 1 and b >= 1
    t = isqrt((b+12)//4)+1
    width2 = F(width2)
    L = 1+isqrt((width2.numerator-1)//width2.denominator)
    qbits = (L-1).bit_length()
    trials = 256*(b+2)
    p = b+trials.bit_length()+4
    mid = center.__floor__()
    for _ in range(trials):
        shell = t-bits(t).bit_length()
        if shell == t:
            continue
        idx = bits(qbits)
        if idx >= L:
            continue
        k = shell*L+idx
        j = mid-k if bits(1)==0 else mid+1+k
        v = F(j-center)**2/width2
        if bits(p) < min(1<<p,threshold(v,p+shell)):
            return j
    return mid
# Execute after the scalar threshold and sample_squared definitions.
def dot(x,y):
    return sum(a*b for a,b in zip(x,y,strict=True))

def orthogonalize(cols):
    directions=[]
    for col in cols:
        v=list(map(F,col))
        for u,norm2 in directions:
            coef=dot(col,u)/norm2
            v=[x-coef*y for x,y in zip(v,u)]
        norm2=dot(v,v)
        if not norm2:
            raise ValueError("dependent basis")
        directions.append((v,norm2))
    return directions

def preimage(cols,directions,lift,sigma2,b,bits):
    # lift is any integral representative of the requested coset.
    x=list(lift)
    for col,(u,norm2) in reversed(list(zip(cols,directions,strict=True))):
        center=-dot(x,u)/norm2
        z=sample_squared(center,F(sigma2)/norm2,b,bits)
        x=[a+z*h for a,h in zip(x,col)]
    return x

def gadget_basis(Abar,R,q):
    # Abar has n rows and h columns. R has h rows and n*k columns.
    n,h=len(Abar),len(R)
    k=(q-1).bit_length()
    def digits(v):
        return [(a%q >> j)&1 for a in v for j in range(k)]
    def shear(a,t):
        return [x+dot(row,t) for x,row in zip(a,R)]+t
    def lift(v):
        return shear([0]*h,digits(v))
    cols=[]
    for j in range(h):
        cols.append(shear([int(i==j) for i in range(h)],digits([-row[j] for row in Abar])))
    for i in range(n):
        for j in range(k):
            t=[0]*(n*k)
            if j+1<k:
                t[i*k+j]=2
                t[i*k+j+1]=-1
            elif q==1<<k:
                t[i*k+j]=2
            else:
                t[i*k:(i+1)*k]=[(q>>a)&1 for a in range(k)]
            cols.append(shear([0]*h,t))
    return cols,lift

def setup(n,h,q,b,bits):
    k=(q-1).bit_length()
    p=k+(n*h-1).bit_length()+b+1
    Abar=[[bits(p)%q for _ in range(h)] for _ in range(n)]
    R=[[bits(1) for _ in range(n*k)] for _ in range(h)]
    cols,lift=gadget_basis(Abar,R,q)
    directions=orthogonalize(cols)
    A=[row+[((1<<(j%k) if i==j//k else 0)-
              sum(row[a]*R[a][j] for a in range(h)))%q for j in range(n*k)]
       for i,row in enumerate(Abar)]
    return A,cols,directions,lift

def prepare_columns(n,q,b,bits):
    """Return the public matrix and a private sampler with per-column TV <= 2^-b."""
    assert n >= 1 and q >= 2 and b >= 1
    ell=n*(q-1).bit_length()
    h=ell+2*(b+(ell-1).bit_length())
    d=h+ell
    T=b+(d-1).bit_length()+4
    sigma2=d*(ell+3)**2*T
    A,cols,dirs,lift=setup(n,h,q,b,bits)
    def draw(y):
        assert len(y)==n
        return preimage(cols,dirs,lift(y),sigma2,T-3,bits)
    return A,draw
~~~
