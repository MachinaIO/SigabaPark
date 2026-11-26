---
title: A split-witness affine predicate for Boolean quadratic systems over the BN254 scalar field
refs: [definition:WE_CircuitSAT, theorem:AdvancedEncryption.WE.IPE.affine_key_offset, theorem:AdvancedEncryption.WE.IPE.subgroup_score_gcd, theorem:AdvancedEncryption.WE.IPE.bn254_scaled_lwe_strength_640]
tags: [witness-encryption, predicate-encryption, lwe, compiler]
---

[Praxis, Section 4.1 and Table 4](https://eprint.iacr.org/2026/2971) motivates a direct interface for Boolean unknowns in prime-field quadratic equations. Its table has 391,693 unknowns and 1,694 constraints. Here is a classical-data lattice candidate for smaller domains. It reuses the selective AFV table of [PR 96](https://github.com/MachinaIO/SigabaPark/pull/96). The table remains exponential. The following compiler and checks give neither a WE Submission proof nor a QPT hardness certificate.

Choose independent uniform public field weights h_j after fixing the instance. Aggregate the equations into L(x)+R(y)+sum_j C_j(x)y_j by separating monomials entirely on each side and collecting cross terms by the right variable. For the BN254 scalar prime P set D=2^259 and q=DP. Use w=D(L,C_1,...,C_r), v=(1,y_1,...,y_r), and key offset b=D R(y) with canonical field lifts. Generate the short key for [A | sum v_i A_i - b G]. The ciphertext stays (A^T s+x_noise, (A_i+w_i G)^T s+R_i^T x_noise, scalar). The difference in the combined matrix is precisely the affine score times G. Every real witness has zero score. For each invalid pair the field hash vanishes for exactly one choice of the weight of a nonzero equation when the remaining weights are fixed. A union bound costs CK/P over C ciphertext addresses and K key addresses regardless of their dependence. With 128 total Boolean variables the bound is below 2^-125. It is vacuous for unrestricted enumeration at the size of Table 4. Existence of a spurious zero precludes the all-rejecting simulation. Repeating encryptions independently introduces a witness-consistency problem.

Every other score z has gcd(z,q)=D. After programming A_i=A R_i-w_i*G, the combined right block is A(sum v_i R_i)-zG. The basis of PR 96 uses an odd top minor modulo D and radix expansion modulo q/D=P with invertible z/D. Rank failure of uniform A modulo two is at most 2^(n-m). Real setup uses the unit gadget multiplier and arbitrary combined right block. Use the full m base coordinates. Dropping the pivots by the original PR 97 formula leaves an uncancelled offset term when b is nonzero.

For a uniform n by a hash matrix modulo q and independent entries uniform in [0,2^t), assume 2^t<P. The expected conditional chi-square divergence from uniform equals the sum over nontrivial divisors d of q of J_n(d) times the probability that two source columns coincide modulo d, with J_n the Jordan totient. Indeed the image of each row on a fixed difference is the ideal of its common gcd g with q, and g^n=sum_(d|g) J_n(d). The dyadic divisor 2^j has probability 2^(-a min(j,t)); every divisor containing P has probability 2^(-at). For a>=n the result is at most (259+1) times 2^max(n-a,n ceil(log2 q)-at). Conditioning on leakage of at most J values costs a factor J by bounding the maximum class probability for each projection and summing over leakage values. Apply this after fixing the independent subtractive mask. This supplies the setup and challenge hash switches of PR 96.

The parameter sweep below uses the two-width sizing rules of [PR 98](https://github.com/MachinaIO/SigabaPark/pull/98), the mixed-modulus hash slack and full base blocks. Round a residue stochastically between adjacent points j q/2^h on the circle, including wraparound. The decoded rational has error of mean zero in the local lift and error interval of length q/2^h. The scalar uses nearest rounding. Finite coins can approximate a draw from M possibilities by floor(M U/2^k), uniform k-bit U, with TV at most M/2^k. Allow 512 excess bits for each such draw and charge the number of calls. In the 128-variable row the number of residue and rounding draws for honest encryption is below 2^100 when exact dyadic mask draws are excluded (C p m d < 2^106 even if those draws are counted separately). Mask entries already have an exact dyadic source.

For dense 128-variable systems the best swept row has left/right 62/66, 67 attributes, n=131072, m=582339, d=262144, radix exponent 257, setup and mask exponents 210 and 116, Gaussian width exponents 486 and 263, and ciphertext widths 509 and 288. The static key and ciphertext lengths are 358199298 and 5354741181 bits per entry, giving 51124828147068745446793936896 bits per message bit before framing and hash weights. No large table was materialized. The registry bound of 640 concerns its estimator. End-to-end quantum security needs a corresponding quantum assumption, explicit reductions and machine clocks.

The NAND prototype also compiles polynomial expansions in the Boolean quotient ring up to a size cap. A one-sided wire is evaluated locally. A cut wire becomes a fresh guessed bit with residual actual minus guessed. Every residual on Boolean assignments is 0 or ±1. A witness trace gives consistent guesses, and induction recovers the trace whenever all residuals vanish. Sample independent H-bit coefficients and aggregate modulo the full dyadic q. If a residual is odd, the low H bits of the aggregate are uniform. Thus the probability some invalid address has gcd at least 2^H is at most CK/2^H for H<=log2(q). Choose H with room for this bound and the simulated basis width, otherwise skip this mode. These guesses can be expensive: the paired, parity and overlapping 128-input controls at cap 8 needed 0 guesses and 64, 2 and 129 attributes, while the overlap control at cap 2 needed 256 guesses. This optional compiler does not change the exponential worst case.

The three listings are independent. The first two use Python, and the third uses SageMath and SymPy for small exact coset and rounded decryption checks.

~~~python
from collections import Counter
from itertools import product
from random import Random
from math import gcd

P=21888242871839275222246405745257275088548364400416034343698204186575808495617
ONE={(0,0):1}
def plus(a,b,k=1):
    out=dict(a)
    for xy,z in b.items():
        val=out.get(xy,0)+k*z
        if val:out[xy]=val
        else:out.pop(xy,None)
    return out
def multiply(a,b):
    c=Counter()
    for (i,j),s in a.items():
        for (k,l),t in b.items():c[i|k,j|l]+=s*t
    return {k:v for k,v in c.items() if v}
def bit_poly(index,side):return {(1<<index,0) if side==0 else (0,1<<index):1}
def value(poly,l,r):
    return sum(v for (a,b),v in poly.items() if (a&l)==a and (b&r)==b)
def roles(poly):
    return {s for pair in poly for s in (0,1) if pair[s]}
def aggregate(rows,h,mod):
    poly={}
    for row,w in zip(rows,h,strict=True):poly=plus(poly,row,w)
    return {k:v%mod for k,v in poly.items() if v%mod}
def encode(poly,l,r,mod,scale=1):
    # The right-only offset enters the key's matrix at generation.
    terms={};offset=0
    for (a,b),c in poly.items():
        if not a:
            if (b&r)==b:offset+=c
        else:
            terms.setdefault(b,0)
            if (a&l)==a:terms[b]+=c
    ordered=sorted(terms)
    return ([scale*(terms[b]%mod) for b in ordered],
            [int(b&r==b) for b in ordered],scale*(offset%mod))

def compile_nand(n,gates,left,cap):
    # Normalize the core's unset wire convention and discard the dead cone.
    norm=[tuple(a if 0<=a<=n+i else 0 for a in g) for i,g in enumerate(gates)]
    output=n+len(gates) if gates else 0; live={output}
    for wire in range(output,n,-1):
        if wire in live:live.update(norm[wire-n-1])
    fixed={0:1}
    if output==0:return [],[],[],[],set(),fixed,False
    fixed[output]=1
    # Every remaining truth-table tuple respects aliases and current fixed bits.
    while True:
        old=len(fixed)
        for z in sorted(live):
            if z<=n:continue
            a,b=norm[z-n-1];slots=(a,b,z)
            ok=[]
            for i,j in product((0,1),repeat=2):
                vals=(i,j,1-i*j);d=dict(zip(slots,vals))
                if all(d[k]==v and fixed.get(k,v)==v for k,v in zip(slots,vals)):ok.append(d)
            if not ok:return [],[],[],[],live,fixed,True
            for k in slots:
                possible={d[k] for d in ok}
                if len(possible)==1:fixed[k]=possible.pop()
        if old==len(fixed):break
    poly={0:ONE};owners={};ops=[];guesses=[];rows=[]
    free=[v for v in sorted(live) if 1<=v<=n and v not in fixed]
    loads=[sum((v in left)==(s==0) for v in free) for s in (0,1)]
    for v in sorted(live):
        if v==0:continue
        if v<=n:
            if v in fixed:poly[v]=ONE if fixed[v] else {}
            else:
                owners[v]=int(v not in left);poly[v]=bit_poly(v,owners[v])
            continue
        a,b=norm[v-n-1];u,t=poly[a],poly[b];used=roles(u)|roles(t)
        if v not in fixed and len(used)==1:
            s=next(iter(used));ops.append((v,s,u,t));poly[v]=bit_poly(v,s);continue
        actual=plus(ONE,multiply(u,t),-1)
        if v in fixed:
            forced=ONE if fixed[v] else {}
            eq=plus(actual,forced,-1)
            if eq:rows.append(eq)
            poly[v]=forced
        elif len(actual)<=cap:poly[v]=actual
        else:
            s=min((0,1),key=lambda j:(loads[j],j));loads[s]+=1
            guesses.append((v,s));poly[v]=bit_poly(v,s);rows.append(plus(actual,poly[v],-1))
    return rows,ops,guesses,free,live,fixed,False

def local_bits(word,guess,plan,left):
    rows,ops,guesses,free,live,fixed,conflict=plan
    masks=[0,0]
    for v in free:
        if word>>(v-1)&1:masks[int(v not in left)]|=1<<v
    for j,(v,s) in enumerate(guesses):
        if guess>>j&1:masks[s]|=1<<v
    for v,s,u,t in ops:
        a=value(u,*masks);b=value(t,*masks)
        assert a in (0,1) and b in (0,1)
        if not a*b:masks[s]|=1<<v
    return masks

def run_raw(n,gates,word):
    wire=[1]+[(word>>i)&1 for i in range(n)]
    for a,b in gates:
        get=lambda j:wire[j] if 0<=j<len(wire) else 1
        wire.append(1-get(a)*get(b))
    return wire if gates else wire+[1]

def check_small():
    rng=Random(417);cases=0;gmax=0
    for n in (0,1,128):
        plan=compile_nand(n,[],set(),2)
        assert plan[:4]==([],[],[],[]) and not plan[-1] and run_raw(n,[],0)[-1]==1
    for _ in range(160):
        n=rng.randint(2,7);gates=[tuple(rng.randrange(n+i+3) for _ in (0,1)) for i in range(rng.randint(1,15))]
        left=set(range(1,n//2+1));plan=compile_nand(n,gates,left,rng.randint(1,3))
        rows,ops,guesses,free,live,fixed,conflict=plan;gmax=max(gmax,len(guesses))
        h=[rng.randrange(1<<20) for row in rows];F=aggregate(rows,h,1<<40)
        for word in range(1<<n):
            wire=run_raw(n,gates,word)
            if conflict or any(v<=n and wire[v]!=z for v,z in fixed.items()):
                assert not wire[-1];continue
            exists=False
            for guess in range(1<<len(guesses)):
                masks=local_bits(word,guess,plan,left);res=[value(f,*masks) for f in rows]
                assert set(res)<={-1,0,1}
                true=not any(res);exists|=true
                w,v,b=encode(F,*masks,1<<40)
                assert (b+sum(i*j for i,j in zip(v,w))-sum(z*t for z,t in zip(h,res)))%(1<<40)==0
                if true:assert all((guess>>k&1)==wire[a] for k,(a,s) in enumerate(guesses))
                cases+=1
            assert exists==bool(wire[-1])
    print('integer residual/score and existential checks',cases,'max guesses',gmax)

def check_field():
    rng=Random(712);tests=0
    for prime in (3,5,7):
        n=5;left={1,2};D=16;mod=D*prime
        rows=[]
        for j in range(3):
            f={}
            for i in range(n+1):
                for k in range(i,n+1):
                    inds={i,k}-{0};a=sum(1<<u for u in inds if u in left);b=sum(1<<u for u in inds-left)
                    f=plus(f,{(a,b):rng.randrange(prime)})
            rows.append(f)
        for word in range(1<<n):
            mask=word<<1;l=mask&6;r=mask&~6;res=[value(f,l,r)%prime for f in rows];bad=0
            for h in product(range(prime),repeat=len(rows)):
                f=aggregate(rows,h,prime);w,v,b=encode(f,l,r,prime,D)
                score=(b+sum(i*j for i,j in zip(v,w)))%mod
                assert score==D*(sum(i*j for i,j in zip(h,res))%prime)
                if score:assert gcd(score,mod)==D
                else:bad+=1
                tests+=1
            assert bad==(prime**(len(rows)-1) if any(res) else prime**len(rows))
    print('field hash, gcd and exact fiber tests',tests)

def controls():
    # Accumulate constraints via NANDs implementing conjunction.
    n=128;left=set(range(1,65))
    for typ in ('paired','parity','overlap'):
        gates=[]
        def nand(a,b):
            gates.append((a,b));return n+len(gates)
        def conj(a,b):
            u=nand(a,b);return nand(u,u)
        def xor(a,b):
            u=nand(a,b);v=nand(a,u);w=nand(b,u);return nand(v,w)
        acc=0
        if typ=='paired':
            for i in range(1,65):acc=conj(acc,nand(i,64+i))
        elif typ=='parity':
            a,b=1,65
            for i in range(2,65):a=xor(a,i);b=xor(b,i+64)
            acc=xor(a,b)
        else:
            for i in range(1,65):
                a=xor(i,65+i%64);b=xor(64+i,1+i%64)
                acc=conj(acc,nand(a,b))
        inv=nand(acc,acc)
        while len(gates)<4095:nand(0,0)
        nand(inv,inv)
        for cap in (2,8,32):
            plan=compile_nand(n,gates,left,cap)
            rows,ops,guesses,free,live,fixed,conflict=plan;assert not conflict
            h=[Random(799+j).getrandbits(400) for j in range(len(rows))]
            f=aggregate(rows,h,1<<512);w,_,_=encode(f,0,0,1<<512)
            l=sum(v in left for v in free)+sum(s==0 for _,s in guesses)
            r=len(free)+len(guesses)-l
            for word in [0,(1<<128)-1]+[Random(92+j).getrandbits(128) for j in range(20)]:
                raw=run_raw(n,gates,word)
                if any(raw[v]!=z for v,z in fixed.items()):assert not raw[-1];continue
                guess=sum(raw[v]<<i for i,(v,_) in enumerate(guesses))
                assert (not any(value(row,*local_bits(word,guess,plan,left)) for row in rows))==bool(raw[-1])
            print(typ,cap,'free/guess/L/R/constraints/p',len(free),len(guesses),l,r,len(rows),len(w))
if __name__=='__main__':check_small();check_field();controls()
~~~

~~~python
from math import isqrt
from itertools import product

def ceildiv(x,y):return (x+y-1)//y
def ceilroot(x):
    r=isqrt(x)
    return r+(r*r<x)
def calc(p,K,C,t,r,V,score_cap):
    n=1<<17;e=513;d=n*ceildiv(e,r);M=1<<21
    slack=e+(e-1).bit_length()+2*(384+(p*d).bit_length())
    setup_slack=(e-1).bit_length()+2*(384+d.bit_length())
    a=max(n+setup_slack,ceildiv(n*e+setup_slack,t));m=a+d
    t_enc=ceildiv(n*e+slack,m)
    if m<n+slack or (1<<max(t,t_enc))>=P:return None
    if m+1>M:return None
    lg=lambda x:(x-1).bit_length()
    s=r+9+max(t+ceildiv(lg(a+d+400),2),
              t_enc+ceildiv(lg(V*(m+d+128+400)),2))
    if 16*score_cap>(1<<s):return None
    L=m+d; J=m; sg=r+6
    Y2=256*(1<<(2*s))*L; G2=256*(1<<(2*sg))*L
    # Condition on the sampled key. Three errors: base noise, mask noise, wire rounding.
    # For each, enforce 2 exp(-2 threshold^2 / sum widths^2) <= 2^-159
    # using exponent >=160 and e>=2 as the natural exponential base.
    q=P<<259
    lim=q//16
    if 2*lim**2 < 160*32**2*(1+Y2):return None
    if 2*lim**2 < 160*(2<<t_enc)**2*256*m*V*G2:return None
    half_log=lambda x:ceildiv(lg(x),2)
    ha=min(e,half_log(81920*Y2)); hg=min(e,half_log(20480*V*G2))
    def best_slot(length,exponent):
        def slot(b):return length*(b+1)+(32*(1<<exponent)*ceilroot(length*L))//(1<<b)
        return min((slot(b),b) for b in range(exponent+2,exponent+12))
    ka,ba=best_slot(J,s);kg,bg=best_slot(d,sg)
    key=ka+kg;ct=6+J*ha+p*d*hg
    return (key*K+ct*C,r,t,t_enc,s,sg,ba,bg,ha,hg,m,d,key,ct)


P=21888242871839275222246405745257275088548364400416034343698204186575808495617
best=None
for left in range(56,69):
    right=128-left
    p=right+1
    for k in range(1,33):
        for t in range(8,254):
            row=calc(p,1<<right,1<<left,t,ceildiv(513,k),p,1<<259)
            if row and (best is None or row[0]<best[0][0]):best=(row,left,p)
print(best)
~~~

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

def right_basis(A,q,r,z,R,u):
    n,m=A.shape;e=(q-1).bit_length();G=gadget(n,e,r);d=G.cols;k=d//n;b=2**r
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


def mixed_test():
    for q,t,a in [(12,1,2),(20,2,2),(24,1,2)]:
        D=q&-q;P=q//D
        sources=list(product(range(1<<t),repeat=a))
        num=0
        for h in product(range(q),repeat=a):
            cnt=Counter(sum(i*j for i,j in zip(h,u))%q for u in sources)
            num+=sum(v*v for v in cnt.values())
        measured=q*Fraction(num,q**a*len(sources)**2)-1
        expected=sum(Fraction(1<<(j-1),1<<(a*min(t,j))) for j in range(1,D.bit_length()))
        expected+=Fraction(q-D,1<<(a*t))
        assert expected==measured
    D=1024;P=(1<<61)-1;q=D*P;r=9;n=1;a=4;G=gadget(n,(q-1).bit_length(),r);d=G.cols;m=a+d
    rng=Random(198)
    uniform=lambda i,j:Matrix(i,j,lambda u,v:rng.randrange(q))
    wide=lambda i,j:Matrix(i,j,lambda u,v:rng.randrange(4)-rng.randrange(4))
    cbd=lambda:rng.getrandbits(16).bit_count()-rng.getrandbits(16).bit_count()
    A0=uniform(n,a);S=wide(a,d);A=A0.row_join((G-A0*S)%q)
    u=uniform(n,1);Ai=[uniform(n,d) for _ in range(2)];b=5*D;C=Ai[0]+Ai[1]-b*G
    B,point=right_basis(A0.row_join(C),q,r,-1,(-S).col_join(zeros(d,d)),u)
    assert abs(B.det())==q**n
    y=klein(B,point,1<<22,rng)
    key=y[:a,:].col_join(y[a+d:,:]).col_join(y[a:a+d,:])
    assert all(int(j)%q==0 for j in A.row_join(C)*key-u)
    def rounded(v,h):
        i,rem=divmod((v%q)*(1<<h),q)
        return Fraction(((i+(rng.randrange(q)<rem))%(1<<h))*q,1<<h)
    for msg in [0,1]:
        s=Matrix([cbd()]);x=Matrix([cbd() for _ in range(m)])
        c0=A.T*s+x;w=[-2*D,-3*D]
        ct=[(M+wi*G).T*s+wide(m,d).T*x for M,wi in zip(Ai,w)]
        obs=[rounded(int(j),60) for j in c0]+[rounded(int(j),60)+rounded(int(k),60) for j,k in zip(*ct)]
        scalar=int((u.T*s)[0])+cbd()+msg*(q//2)
        scalar=Fraction(((2*(scalar%q)*64+q)//(2*q)%64)*q,64)
        residual=scalar-sum(int(k)*j for k,j in zip(key,obs))
        assert (abs((residual+q//2)%q-q//2)>=q//4)==msg
    Rs=[wide(m,d) for _ in range(2)];w=[-2*D,-2*D]
    sim=[A*R-wi*G for R,wi in zip(Rs,w)]
    F=A.row_join(sim[0]+sim[1]-b*G)
    B,point=right_basis(A,q,r,D,Rs[0]+Rs[1],u)
    assert abs(B.det())==q and all(int(j)%q==0 for j in F*B)
    y=klein(B,point,1<<22,rng)
    assert all(int(j)%q==0 for j in F*y-u)
    print('3 exact mixed collision sums, 2 rounded decryptions, 2 determinants and real/simulated cosets passed')
if __name__=='__main__':mixed_test()
~~~
