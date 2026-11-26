---
title: A rectangular AFV variant over powers of two for bounded binary predicates
refs: [definition:WE_CircuitSAT, theorem:AdvancedEncryption.WE.IPE.ordinary_registry_flatten, theorem:AdvancedEncryption.WE.IPE.ordinary_cbd16_strength_640]
tags: [witness-encryption, predicate-encryption, lwe, trapdoor]
---

[PR #88](https://github.com/MachinaIO/SigabaPark/pull/88) uses a zero inner product on binary vectors to authorize decryption in a split-witness table. [PR #93](https://github.com/MachinaIO/SigabaPark/pull/93) reduces the number of entries, sometimes at considerable predicate dimension p. Here we change the encryption scheme and its proof to pay fewer residues per coordinate and to use the registry's precise CBD(16) error and secret laws. The table compiler, public dispatch, and need to bound the entire reduction on all false statements are as before. Our starting points are [AFV Sections 3–4, including Games 0–2](https://theory.stanford.edu/~dfreeman/papers/FuncEnc.pdf) and the [Micciancio–Peikert gadget trapdoor](https://eprint.iacr.org/2011/501). The changes below require their own game analysis.

### Construction and dimensions

Write q=2^e, radix B=2^r, k=ceil(e/r), d=nk. Let G be n disjoint rows of (1,B,...,B^(k-1)). For an integer t with 1<=t<=e, every entry of a blinding matrix is U-V for independent uniforms on [0,2^t). The entries have absolute value below 2^t. Sample A0 uniformly of shape n by a and S of shape a by d from the blinding law. Set A=[A0 | G-A0 S], m=a+d. Independently sample p matrices A_i of shape n by d and a target u of length n uniformly modulo q. For v in {0,1}^p define C_v=sum_i v_i A_i. Use the trapdoor S to sample a short key y in the coset [A|C_v] y=u with the Gaussian procedure below. Its length is m+d.

To encrypt a bit b for w in {0,1}^p, draw s of length n, x of length m and scalar x' independently from CBD(16) in each coordinate. Draw independent m by d blinding matrices R_i. Output

    c0=A^T s+x,   ci=(Ai+w_i G)^T s+Ri^T x,   c'=u^T s+x'+b(q/2)   mod q.

Decrypt by rounding c'-y^T[c0;sum_i v_i ci] to 0 or q/2. If the inner product is zero the G term vanishes. The score z=sum_i v_i w_i is an ordinary integer; assume p<q. The masks, key labels and table indices are obtained from the witness and public compiler as in #88. One ciphertext uses 1+m+pd residues. The n(m+pd+1) public setup residues are needed during encryption and by the PE simulator. The WE decryptor needs the key, the ciphertext and the recomputable labels/dimensions, so its transmitted table need not include these setup matrices. Fixed G costs neither fresh ciphertext coins nor a dense matrix multiplication: G^T s consists of radix shifts of coordinates of s. The conditional noise law here differs from the sign law measured in #89.

### Short bases when a rejecting score is even

In a selective simulation for w*, program A_i=A R_i-w_i* G. For a rejecting key let R=sum_i v_i R_i and z=<v,w*>0. The matrix for its coset is [A | AR-zG]. If g=gcd(z,q)>1, inverting z modulo q is impossible. Set Q=q/g and use the invertible scalar z/g modulo Q. Sample A from the independent uniform LWE columns. Except with probability at most 2^(n-m), its reduction mod 2 has row rank n, by a union over nonzero row combinations. On this event select n columns P with odd determinant, invertible modulo every g under consideration. Here P stands for the pivot matrix in formulas.

First use coordinates [A|-zG]. To hit any u, put P^-1 u mod g on the top pivot coordinates and zero elsewhere (all zero if g=1). For this top vector x, solve Gy=(z/g)^-1(Ax-u)/g mod Q by radix expansion, independently per row. A representative of the syndrome divided by g is well-defined modulo Q. Map (x,y) to (x-Ry,y). This also lifts top vectors of the mod-g kernel to the zero coset. That top kernel has a basis consisting first of g times each pivot unit vector, then each nonpivot unit vector corrected on the pivots by -P^-1 A_j mod g. The ordered Gram–Schmidt lengths are at most g.

For a single right row modulo Q use the k-1 columns B e_j-e_(j+1), followed by a digit vector t_Q with (1,B,...,B^(k-1)) t_Q=Q. Allow the last digit to equal B if necessary. This basis has determinant of absolute value Q (expand along the radix row, or eliminate the successive coordinates using the bidiagonal columns). The first lengths are at most sqrt(B²+1) and the last perpendicular length is Q/||(1,B,...,B^(k-1))|| <= B. This includes k=1. Take the direct sum over n rows. For the full simulated lattice place these right basis columns first, then the lifted top basis. The projection onto the top coordinates before shearing has exactly the top mod-g kernel as image, and its zero fiber is exactly the right mod-Q kernel; hence these columns span. The index is Q^n g^n=q^n.

After the shear, distances of the first columns to their previous spans increase by at most 1+||R||_2. All later columns, modulo the span of these first columns, are represented by (x,0). Subtract any real combination of preceding top columns before orthogonal projection; their Gram–Schmidt lengths are thus still at most g. A bound for the simulated basis is max(g,(1+||R||_2)sqrt(B²+1)). In the real system reorder [A|C_v] as [A0|C_v|G-A0 S]; the same argument uses z=-1, g=1 and the shear with top rows -S followed by zero rows. This real basis does not require a rank test on A0. Gaussian coset sampling removes basis dependence up to the explicit approximation below.

### Hashing with many bits per entry over a composite modulus

For a uniform n by a matrix H and an independent column U of uniforms on [0,2^t), the expected chi-square divergence of H U from uniform, conditioned on H, equals

    sum_(j=1)^e (2^(nj)-2^(n(j-1))) 2^(-a min(j,t)).

Indeed for fixed difference of two columns, the probability over H that it hashes to zero is q^-n 2^(n v), where v is the common 2-adic valuation capped at e. Expand 2^(nv) by telescoping. The probability of a collision modulo 2^j in every coordinate is 2^(-a min(j,t)). This calculation also explains why reusing the original all-odd sign alphabet over an even modulus would fail.

Conditioning on auxiliary leakage f(U) of at most J values multiplies the collision-probability upper bound for each residue projection by at most J. For each leakage value l and residue-vector class c we have Pr[c,l]<=2^(-a min(j,t)); bound sum_c Pr[c,l]^2/Pr[l] by that number and sum over l. Condition on V before applying this to U-V; subtracting HV translates the hash and (U-V)^T x mod q has at most q values for fixed x. Combining the collision expression with Cauchy–Schwarz, the one-column TV bound is at most

    (1/2) sqrt(J e 2^max(n-a, ne-at))     for a>=n.

Independent columns with common H cost a factor equal to their count by changing one column at a time conditional on H; integrate over H after this product bound. For the challenge use m in place of a. With l=ceil(log2 e)+2(384+ceil(log2(pd+1)))+e, take a=max(n+l,ceil((ne+l)/t)). The trap-generation switch (d columns, no leakage) and the challenge switch (pd columns, J<=q) each cost at most 2^-384. The program may use a sharper leakage bound if needed.

### Selective message security

Replace real keys by coset Gaussians before switching bases. Now the key law depends on the published matrices and predicates alone, up to the sampling error. Replace A by uniform. In the conceptual real challenge on w*, first fix s,x,u and retain the R_i^T x leakage. Switch the independent uniform A_i to A R_i-w_i*G via the preceding conditional hash bound. Adding the public-matrix product prescribed by the encryption formula now gives c_i=R_i^T c0. The simulator gets m+1 independent sample columns under one CBD(16) secret from the ordinary LWE challenge; the first m supply A and c0 and the last supplies u and its label, to which it adds b q/2. Replace the conceptual keys by samples using the simulated bases. The simulator can generate the other WE ciphertexts honestly using the public matrices. When all LWE labels are uniform, the last label is an independent one-time pad even given u, the programmed matrices, keys and the other labels. No trapdoor for a randomized ciphertext polluter and no second attribute-hiding challenge are needed for this message-only game. The small rank failure in the uniform matrix case can be charged explicitly. Statistical bounds apply also to quantum postprocessing of the classical output; a computational quantum claim requires the corresponding quantum LWE premise. The registered Sigaba machine and estimator do not themselves prove QPT hardness.

### Correctness, finite coins and sizes

Let lg denote ceiling binary logarithm, slg(x)=ceil(lg(x)/2). A deliberately conservative uniform basis bound is 2^g0 for g0=r+2+t+lg(p)+slg(md), using the Frobenius norm of the sum of blinding matrices and g<=p. Use Gaussian parameter sigma=2^(g0+4). In decreasing basis order sample each integer coefficient with center determined by the current coset representative and width s_i=sigma/||b_i*||>=16. The density convention is exp(-pi(j-c)^2/s_i²). By one-dimensional Poisson summation every shifted normalizer divided by s_i is between 1-eta and 1+eta for eta=2 sum_{k>=1} exp(-pi*256*k²). Multiplying the conditional probabilities gives a density proportional to exp(-pi||y||²/sigma²) within ratio ((1+eta)/(1-eta))^(m+d) across outputs; normalization yields a corresponding TV bound. This is the elementary coset-sampling argument of [Gentry, Peikert and Vaikuntanathan](https://eprint.iacr.org/2007/432).

One finite implementation discards proposal points farther than 16s_i from their center. Use a centered power-of-two proposal interval covering those points with at most 74s_i slots and accept with the above Gaussian weight. Bound the tail by a decreasing Gaussian integral plus its first term (less than 2^-990 at s_i>=16); retained normalizing mass is greater than 0.99s_i. Thus success per proposal exceeds 1/80. Use at most 65,536 proposals per coordinate. A downward dyadic acceptance approximation within 2 units at 512 fractional bits costs at most 2^-495 per coordinate by a coupling over the proposals. Timeout contributes at most exp(-65536/80). These estimates allow a conservative per-coordinate sampling error of 2^-490 including the normalizer discrepancy for the tabulated dimensions. All truncation and timeout effects must be charged for the relevant keys and hybrids. Squared widths and centers can be computed with rational Gram–Schmidt, avoiding approximate decisions about the basis. Certified exponential evaluation and rational bit complexity need an explicit machine bound. The small reference checks the ball-enclosure width before using a threshold. It uses a PRNG for reproduction.

Every completed truncated key satisfies ||y||<=16 sigma sqrt(m+d) by orthogonality of its Gram–Schmidt residuals. CBD(16) coefficients have absolute value at most 16. The accepted-pair decoding error has absolute value at most

    16 + 16 ||y|| sqrt(m) + 16 ||y|| p m 2^t sqrt(d).

The script checks a power-of-two upper bound on this expression below q/4; the bounds here do not rely on independent decryption errors. Public matrices and all per-entry costs remain large. A fixed-width encoding of a completed signed key coordinate costs at most lg(sigma)+4+slg(m+d)+2 bits. The encrypted table lengths below omit framing, mode tags and statement data. They count the actual coordinate widths rather than treating key coordinates as residues.

| n | e | p | t | r | m | d | log2 sigma | Upper log2 error | Residues per ciphertext | Integers per key |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 4096 | 128 | 1076 | 7 | 22 | 99611 | 24576 | 62 | 124 | 26543388 | 124187 |
| 4096 | 256 | 831 | 21 | 128 | 58176 | 8192 | 180 | 253 | 6865729 | 66368 |
| 262144 | 1024 | 1076 | 204 | 512 | 1840158 | 524288 | 753 | 1020 | 565974047 | 2364446 |
| 262144 | 1024 | 831 | 205 | 512 | 1833739 | 524288 | 753 | 1020 | 437517068 | 2358027 |

**The first two rows fail the security target.** Running the registered Lean estimator's Usvp.cost alone on exactly m+1 samples returns floor costs of 107 and 55 bits, respectively. Since H is a minimum, neither can support even 128 bits at that parameter set, despite passing the decoding and hash checks. The third row with 209,012,224 keys and 458,752 ciphertexts requires 646,405,677,514,254,336 table bits under this encoding. The fourth with 8,965,806,142 keys and 79,437,951 ciphertexts needs 51,868,632,414,167,824,212 bits. Both use 770-bit signed key coordinates. These figures are static estimates per WE message bit. They do not include the public preprocessing and key generation clocks.

### Dropping ciphertext bits with a worst-case decoding bound

Round every ciphertext coordinate to the nearest multiple of 2^(e-h) on the modular circle and transmit its h-bit quotient. Reconstruct before the usual decryption. For any selected predicate, the base block incurs at most half a step per coordinate and the summed attribute block at most p half-steps. Writing L=m+d and Y=16 sigma sqrt(L), the added absolute error modulo q has a lift bounded by (1+p sqrt(L) Y) 2^(e-h-1), including the scalar rounding. This is deterministic and independent of ciphertext noise correlations. Put u=4+lg(sigma)+slg(L), h=min(e,u+lg(p)+slg(L)+4). If h<e the added error is at most q/16; for h=e it vanishes. For our two rows the original error is at most q/16. The combined error is strictly below q/4. Public rounding is a message-independent map of the challenge and therefore preserves the selective distinguishing bound.

The following are integer counts for the same two cut profiles. We enumerated target gadget lengths 1 through 64, with r=ceil(e/k), and all blinding widths from 1 to e, subject to the certified sample cap and the original error at most q/16. No global optimality is asserted. Both retain n=262144 and e=1024.

| p | r | t | Key bits per coordinate | Ciphertext bits per coordinate | Table bits per WE bit after rounding | Saving against the full-width table above |
|---:|---:|---:|---:|---:|---:|---:|
| 1076 | 512 | 204 | 770 | 794 | 586688080532105216 | 9.24% |
| 831 | 512 | 177 | 742 | 765 | 43665650132294512303 | 15.81% |

### Reduction budget and comparison to Praxis

The accompanying unconditional Lean inequality covers both large rows using the same ordinary-LWE sample budget M=2^22. Each simulated single challenge consumes m+1 independent samples, with m+1 <= M. The registered hardness number is a numeric estimator result. A post-quantum secrecy claim additionally needs a decisional assumption against the chosen quantum adversaries, a reduction in that model, and a clock bound. For example, if every single-challenge simulator costs at most 2^448 T and its advantage bound is the square root of cost divided by 2^640, then C < 2^27 ciphertext hybrids cost at most 2 C sqrt(2^448 T / 2^640) <= 2^-68 sqrt(T), plus statistical errors. The simulator time premise and the compiled WE submission remain open.

[Praxis, Sections 5.4 and 6.1–6.4](https://eprint.iacr.org/2026/2971) gives a different comparison point. For the honestly set-up Groth16 verifier, the authors report 7.88 GiB at their 100-bit target, with 256-bit messages in the formalization. Their extraction theorem uses the bilinear generic group and random oracles in addition to MSIS. Section 6.2 puts the estimator at about 103.5 bits for its MSIS instance and the reduction at about 108 bits of work at the target. Its pairing implementation and verification model supply no quantum security for the dyadic scheme. [PR 77](https://github.com/MachinaIO/SigabaPark/pull/77) already studies direct pairing substitutions. The reusable efficiency idea here is to share a factor only when security covers its reuse. In the dyadic scheme the base (A,u) is public and can be shared under the selective game, while fresh s,x,x',R_i are required per ciphertext in the hybrid above. A direct move to sharing secret encryption noise would require a different joint distribution proof. The table sizes above are for specific cut profiles and a single bit, so dividing them by 7.88 GiB would not measure a speedup on a common instance.

### Reproducibility

The following integer calculation reproduces the static budgets.

~~~python
from math import isqrt

def lg(n):return (n-1).bit_length()
def ceildiv(a,b):return (a+b-1)//b
def slg(n):return ceildiv(lg(n),2)

def budget(n,e,t,r,p,K,C):
    assert 0<t<=e and 0<r<=e and 0<p<2**min(32,e)
    d=n*ceildiv(e,r)
    # Total TV <=2^-384 for each matrix switch. Allow K_leak=q.
    slack=e+lg(e)+2*(384+lg(p*d+1))
    a=max(n+slack,ceildiv(n*e+slack,t))
    m=a+d
    # Both the real and simulated Gram-Schmidt ceilings are <= 2^g.
    g=r+2+t+lg(p)+slg(m*d)
    logsigma=g+4
    keynorm=4+logsigma+slg(m+d)
    # Scalar error <= 16 + 16||e|| sqrt(m) + 16||e|| p m 2^t sqrt(d).
    # Upper bound the three positive terms by 4 times the largest.
    logerror=2+max(4,4+keynorm+slg(m),4+keynorm+lg(p)+lg(m)+t+slg(d))
    return dict(n=n,e=e,t=t,r=r,d=d,a=a,m=m,logsigma=logsigma,logerror=logerror,
                pk=n*((m+p*d)+1),ct=1+m+p*d,key=m+d,
                totalcoords=K*(m+d)+C*(1+m+p*d))

if __name__=='__main__':
    for n,e,p,K,C in [(4096,128,1076,209012224,458752),
                         (4096,256,831,8965806142,79437951)]:
        choices=[b for t in range(1,e+1) for r in range(1,e+1)
                 if (b:=budget(n,e,t,r,p,K,C))['logerror']<=e-3]
        if choices:
            best=min(choices,key=lambda b:(b['totalcoords'],b['pk'],b['logerror']))
            print(best)
        else:print('no fitting pair',n,e)
    n=1<<34;e=1<<26
    b=budget(n,e,e//8,e//4,1076,209012224,458752)
    M=n*(2*(e+1))
    assert b['logerror']<=e-3 and M>=b['m']+1
    print('large registry anchor',b,'M',M)
    # At fixed key/ciphertext counts the signed key width also affects bit volume.
    for p,K,C,t in [(1076,209012224,458752,204),(831,8965806142,79437951,205)]:
        b=budget(1<<18,1024,t,512,p,K,C)
        width=b['logsigma']+4+slg(b['key'])+2
        bits=width*K*b['key']+1024*C*b['ct']
        assert b['m']+1<=1<<22 and b['logerror']<=1021
        print('certificate row',b,'key bits per coordinate',width,'transmitted table bits',bits)

~~~

Append this loop to the budget listing to reproduce the rounded table search.

~~~python
for p,K,C in [(1076,209012224,458752),(831,8965806142,79437951)]:
 best=None
 for k in range(1,65):
  r=ceildiv(1024,k)
  for t in range(1,1025):
   a=budget(2**18,1024,t,r,p,K,C)
   if a['m']+1>2**22 or a['logerror']>1020:continue
   # ||v||_1 <= p, combined rounding coordinate <= p/2.
   yn=4+a['logsigma']+slg(a['key'])
   ell=yn+lg(p)+slg(a['key'])+4
   kw=yn+2
   val=kw*K*a['key']+min(ell,1024)*C*a['ct']
   row=(val,k,r,t,a['m'],a['d'],kw,ell,a['logerror'])
   if best is None or row<best:best=row
 print(best)

~~~

The following small Sage/Python check exercises the kernel basis and both message values. Its dimensions exercise the algebra only.

~~~python
from collections import Counter
from fractions import Fraction
from itertools import combinations, product
from math import gcd
from random import Random
from sympy import Matrix, diag, eye, zeros

def gadget(n,e,r):
    k=(e+r-1)//r
    return diag(*[Matrix([[2**(r*j) for j in range(k)]]) for _ in range(n)])

def integer_digits(value,k,b):
    out=[]
    for _ in range(k-1):
        value,d=divmod(value,b);out.append(d)
    return out+[value]

def right_basis(A,e,r,z,R,u):
    n,m=A.shape;q=2**e;G=gadget(n,e,r);d=G.cols;k=d//n;b=2**r
    g=gcd(z,q);Q=q//g;zinv=pow(z//g,-1,Q)
    P=next(ix for ix in combinations(range(m),n) if int(A[:,ix].det())%2) if g>1 else ()
    Pmat=A[:,P]
    inv=Pmat.adjugate()*pow(int(Pmat.det()),-1,g) if g>1 else zeros(n)
    def top(v):
        x=zeros(m,1)
        if g>1:
            for j,c in zip(P,inv*v):x[j]=int(c)%g
        return x
    def lift(x,v):
        rem=A*x-v
        assert all(int(y)%g==0 for y in rem)
        y=Matrix([digit for a in rem for digit in integer_digits(
            (int(a)//g*zinv)%Q,k,b)])
        return (x-R*y).col_join(y)
    block=zeros(k,k)
    for i in range(k-1):block[i,i]=b;block[i+1,i]=-1
    block[:,k-1]=Matrix(integer_digits(Q,k,b))
    ker=diag(*[block for _ in range(n)])
    columns=[(-R*y).col_join(y) for y in ker.columnspace()]
    for i in P:columns.append(lift(g*eye(m)[:,i],zeros(n,1)))
    for i in range(m):
        if i not in P:columns.append(lift(eye(m)[:,i]+top(-A[:,i]),zeros(n,1)))
    return Matrix.hstack(*columns),lift(top(u),u)

def exact_collision():
    for e,t,a in [(3,1,3),(3,2,2),(2,2,2),(4,2,2)]:
        q=1<<e;alphabet=range(1<<t);sources=list(product(alphabet,repeat=a))
        emp=0
        for row in product(range(q),repeat=a):
            cnt=Counter(sum(i*j for i,j in zip(row,v))%q for v in sources)
            emp+=sum(w*w for w in cnt.values())
        measured=q*Fraction(emp,q**a*len(sources)**2)-1
        formula=sum(Fraction((1<<j)-(1<<(j-1)),1<<(a*min(j,t))) for j in range(1,e+1))
        assert measured==formula

def test():
    exact_collision()
    rng=Random(1904)
    checks=0
    for n,m,e,r in [(1,3,4,1),(2,3,4,2),(2,4,5,3)]:
        G=gadget(n,e,r);q=2**e;d=G.cols
        A=eye(n).row_join(Matrix(n,m-n,lambda i,j:rng.randrange(q)))
        # Row mix and a column permutation prevent an assumed leading identity.
        if n==2:A=Matrix([[1,2],[1,3]])*A
        A=A[:,list(reversed(range(m)))]
        R=Matrix(m,d,lambda i,j:rng.randrange(-6,7))
        for z in range(1,min(q,13)):
            u=Matrix([rng.randrange(q) for _ in range(n)])
            B,y=right_basis(A,e,r,z,R,u);F=A.row_join(A*R-z*G)
            assert all(int(x)%q==0 for x in F*B)
            assert abs(B.det())==q**n
            assert all(int(x)%q==0 for x in F*y-u)
            checks+=1
    print('kernel/coset checks',checks)
if __name__=='__main__':test()
from math import isqrt
from sage.all import QQ, RealBallField
from sympy import Rational
BALL=RealBallField(600)

def one_dim(center,square,rng):
    # square is the exact squared Gaussian width.
    square=Rational(square);center=Rational(center)
    rad=isqrt(int(256*square))+1
    bits=(2*rad+2).bit_length()
    lo=int(center.floor())-(1<<(bits-1))
    for _ in range(65536):
        j=lo+rng.getrandbits(bits);v=(j-center)**2/square
        if v>256:continue
        arg=BALL(QQ(int(v.p))/int(v.q))
        ball=(-BALL.pi()*arg).exp()*(1<<512)
        a=max(0,int(ball.lower().floor()));b=min(1<<512,int(ball.upper().ceil()))
        assert b-a<=2
        if rng.getrandbits(512)<a:return j
    raise OverflowError

def klein(B,e0,sigma,rng):
    ortho=[]
    for i in range(B.cols):
        b=B[:,i]
        for v in ortho:b=b-(b.dot(v)/v.dot(v))*v
        ortho.append(b)
    y=e0.copy()
    for i in reversed(range(B.cols)):
        b=ortho[i];sq=sigma**2/b.dot(b)
        assert sq>=256
        y+=one_dim(-y.dot(b)/b.dot(b),sq,rng)*B[:,i]
    assert y.dot(y)<=256*sigma**2*B.cols
    return y

def smoke():
    rng=Random(198);q=1<<64;n=1;e=64;r=8;d=8;a=4;m=a+d;p=3;G=gadget(n,e,r)
    def uniform(i,j):return Matrix(i,j,lambda u,v:rng.randrange(q))
    def wide(i,j):return Matrix(i,j,lambda u,v:rng.randrange(4)-rng.randrange(4))
    def cbd():return rng.getrandbits(16).bit_count()-rng.getrandbits(16).bit_count()
    A0=uniform(n,a);S=wide(a,d);A=A0.row_join((G-A0*S)%q)
    u=uniform(n,1);Ai=[uniform(n,d) for _ in range(p)]
    v=[1,1,0];C=Ai[0]+Ai[1]
    T=(-S).col_join(zeros(d,d))
    basis,point=right_basis(A0.row_join(C),e,r,-1,T,u)
    sigma=1<<20
    y=klein(basis,point,sigma,rng)
    key=y[:a,:].col_join(y[a+d:,:]).col_join(y[a:a+d,:])
    assert all(int(x)%q==0 for x in A.row_join(C)*key-u)
    for msg in [0,1]:
        s=Matrix([cbd()]);x=Matrix([cbd() for _ in range(m)])
        c0=A.T*s+x;w=[0,0,1]
        ct=[(B+wi*G).T*s+wide(m,d).T*x for B,wi in zip(Ai,w)]
        z=int((u.T*s)[0])+cbd()+msg*(q//2)-int(key.dot(c0.col_join(ct[0]+ct[1])))
        assert (abs((z+q//2)%q-q//2)>=q//4)==msg
    # In the selective simulation, rejection score two is a nonunit.
    Rs=[wide(m,d) for _ in range(p)];w=[1,1,0]
    sim=[A*R-wi*G for R,wi in zip(Rs,w)]
    basis,point=right_basis(A,e,r,2,Rs[0]+Rs[1],u)
    y=klein(basis,point,sigma,rng)
    assert all(int(x)%q==0 for x in A.row_join(sim[0]+sim[1])*y-u)
    print('both message bits and even-score simulated key passed')
if __name__=='__main__':smoke()

~~~
