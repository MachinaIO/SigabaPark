---
title: Carry-first radix gadget bases for narrower witness-encryption transitions
refs: [definition:WE_CircuitSAT, note:pq-we-clocked-preimage, note:pq-we-self-consistent-modulus, note:pq-we-packed-columns]
tags: [witness-encryption, sampling, complexity]
---

The [MP12 gadget trapdoor](https://eprint.iacr.org/2011/501.pdf) permits several choices of basis. The following ordering improves the deterministic public Gram-Schmidt bound for the binary trapdoor matrix R in our clocked implementation. A power-of-two radix lets the compiler trade the number of gadget columns against smoothing width. Both changes affect the honest encoder and the selected modulus. Security under the full VWW assumptions at the revised parameters still requires analysis.

**Construction.** For syndrome rank N=nw, use radix r=2^a, k=ceil(log2 q), l=ceil(k/a), ell=Nl, and m=h+ell. In each syndrome block encode powers 1,r,...,r^(l-1). Use the same shear (u,t) -> (u+Rt,t) and public A=[U | G-UR]. Allocate h=Nk+2(b_key+ceil(log2 ell)); shortening the radix representation does not shorten the entropy requirement Nk. The binary-column collision argument from the preceding setup proof continues to apply. A digit expansion lifts each syndrome. In each block the first l-1 relations are r e_i-e_(i+1); the final relation is the radix digit vector of q, or r e_last when q=r^l. They generate the full gadget kernel since eliminating successive coordinates leaves exactly the relation q e_first=0. Place the sheared gadget relations first, in that order within each block, then the h sheared corrected unit columns. This is a full kernel basis by elimination of the top input coordinates before the shear.

**Projection bound.** Set V=r²(h+1)+1. A sheared carry has squared norm at most V, because every entry of r R_i-R_(i+1) has absolute value at most r. For the last relation v of a block, the digit-weighted sum of its lower coordinates is q. Its difference from (q/r^(l-1)) e_last lies in the real span of the preceding carries: those independent carries span exactly the kernel of the digit-weight functional. After shearing, the Gram-Schmidt residual therefore has norm no larger than (q/r^(l-1))sqrt(h+1) <= r sqrt(h+1). This also covers a single digit and exact powers of the radix. Once all gadget columns have been processed, their span contains (Rt,t) for every real t. Each remaining basis column differs from a vector in that span by (e_j,0); its Gram-Schmidt residual has norm at most one. These are pointwise bounds for every binary R. For smoothing multiplier T from the earlier planner, public sigma²=V T suffices. No basis-dependent width or extra ciphertext metadata is required.

**Costs.** Recompute the modulus with this width and m, and apply the packed-column code to the new public 1-norm bound. For each fixed a the noise bound is nondecreasing in the prime-power exponent, so the previous monotone search still finds the least exponent meeting its certificate. Evaluating several public radix choices adds no cryptographic assumption. The search below compares a from 1 through 16; it does not certify a global optimum across all radices or constructions. For fixed a the previous polynomial-time bounds continue to hold. This improvement changes the Gaussian parameter; postprocessing security for the packing alone cannot justify this distributional change.

**Eight-level control.** At w=6, n=4, p=7, lambda=32, S=8 and E=16, the previous packed construction requires 80240838912 payload bits per message bit. Carry-first order alone at radix two gives 21212356140 bits. Radix eight gives 11940844760 bits with q=7^74 and m=6770. The upper count of sampled preimage columns drops from 196308 to 94780. Full-root dense decryption uses 1283321200 scalar multiply-adds for the seven matrix products, down from 5505261552. These are operation counts and payload bounds for an accounting control. In particular n=4 does not instantiate the previous conservative nonzero-message failure guarantee at lambda=32. At H=32 the same radix search selects radix sixteen and reduces packed payload from 9552228211712 to 1231154532508 bits. For the same eight levels with n=592, meeting the prior conservative sufficient tensor-survival dimension at lambda=32, the planner instead selects radix 32 and gives 579646206906272 bits (about 72.46 decimal TB per message bit), m=1296592, and 18152288 preimage columns. This uses the specified S,E caps and the prior independent width-two tensor-factor law for the valid-path bound; lambda here budgets correctness, not quantum message security. Full setup and sampling at these sizes have not been timed.

**Small exact checks.** For q in {2,3,4,7,8,13,16,17,32,65,127,257} and each a=1,...,4, all 48 bases passed the rational Gram-Schmidt bound (including the bound of one on every corrected unit column), zero syndrome on every basis column, and reconstruction of a sampled target. These checks include composite q and q at and adjacent to radix powers.

The first listing uses dot, orthogonalize and preimage from the clocked preimage note. The second uses the previous planner's ceil_log2 and sqrt_up and the packed-column layout. The key and per-column precision budgets below allow separate setup and smoothing parameters.

~~~python
# Uses the scalar sampler, orthogonalize and preimage from the clocked preimage note.
def radix_setup(n,q,b,a,bits):
    k=(q-1).bit_length()
    digits=(k+a-1)//a
    base=1<<a
    ell=n*digits
    h=n*k+2*(b+(ell-1).bit_length())
    precision=k+(n*h-1).bit_length()+b+1
    U=[[bits(precision)%q for _ in range(h)] for _ in range(n)]
    R=[[bits(1) for _ in range(ell)] for _ in range(h)]
    def expand(y):
        return [((v%q)>>(j*a))&(base-1) for v in y for j in range(digits)]
    def shear(u,t):
        return [v+dot(row,t) for v,row in zip(u,R,strict=True)]+t
    def lift(y):
        return shear([0]*h,expand(y))
    cols=[]
    for i in range(n):
        for j in range(digits):
            t=[0]*ell
            if j+1<digits:
                t[i*digits+j]=base
                t[i*digits+j+1]=-1
            elif q==base**digits:
                t[i*digits+j]=base
            else:
                for l in range(digits):
                    t[i*digits+l]=(q>>(l*a))&(base-1)
            cols.append(shear([0]*h,t))
    for j in range(h):
        cols.append(shear([int(l==j) for l in range(h)],expand([-row[j] for row in U])))
    A=[row+[((base**(j%digits) if i==j//digits else 0)-
             sum(row[l]*R[l][j] for l in range(h)))%q for j in range(ell)]
       for i,row in enumerate(U)]
    return A,cols,lift

def radix_quality(h,a):
    return (1<<(2*a))*(h+1)+1

def prepare_radix(n,q,key_bits,pre_bits,a,bits):
    A,cols,lift=radix_setup(n,q,key_bits,a,bits)
    m=len(cols)
    ell=n*(((q-1).bit_length()+a-1)//a)
    T=pre_bits+(m-1).bit_length()+4
    sigma2=radix_quality(m-ell,a)*T
    dirs=orthogonalize(cols)
    def draw(y):
        return preimage(cols,dirs,lift(y),sigma2,T-3,bits)
    return A,draw
~~~

~~~python
def account(H,w,n,q,lam,S,E,a=1):
    assert min(H,w,n,lam,S,E)>0 and q>=2
    k=ceil_log2(q)
    rank=n*w
    ell=rank*((k+a-1)//a)
    # Provisional setup precision. Bound column error separately after m is known.
    key_bits=lam+ceil_log2(H)+3
    h=rank*k+2*(key_bits+ceil_log2(ell))
    m=h+ell
    Q=2*(H-1)*m
    pre_bits=lam+ceil_log2(max(1,Q))+3
    T=pre_bits+ceil_log2(m)+4
    sigma2=((1<<(2*a))*(h+1)+1)*T
    scalar_bits=T-3
    t=isqrt((scalar_bits+12)//4)+1
    # sqrt(m)*sqrt(m) times max projected error bounds column 1-norm.
    C=m*(2*t+1)*sqrt_up(sigma2)
    L=rank*S
    B=E
    row=w
    for _ in range(1,H):
        row*=L
        B=C*B+row*E
    payload=(2*n*m+2*(H-1)*m*m)*k
    return dict(k=k,m=m,C=C,B=B,payload=payload,Q=Q,sigma2=sigma2,
                fit=q>=16*(B+1))

def select(H,w,n,p,lam,S,E,a=1):
    # p is a supplied prime valid for the frontend; q=p^j.
    j=1
    while True:
        q=p**j
        cost=account(H,w,n,q,lam,S,E,a)
        if cost['fit']:
            return j,q,cost
        needed=16*(cost['B']+1)
        lo,hi=j,needed.bit_length()
        while hi-lo>1:
            mid=(lo+hi)//2
            if p**mid>=needed:
                hi=mid
            else:
                lo=mid
        j=hi

def compare_radices(H,w,n,p,lam,S,E):
    rows=[]
    for a in range(1,17):
        j,q,c=select(H,w,n,p,lam,S,E,a)
        m=c['m']
        cap,_,_=layout(m,q,c['C'])
        payload=2*n*m*c['k']+2*(H-1)*m*cap
        rows.append((payload,a,j,m,c['Q'],(H-1)*n*m*m))
    return min(rows)
~~~
