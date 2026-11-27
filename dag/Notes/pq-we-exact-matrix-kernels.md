---
title: Exact CPU matrix kernels for VWW encryption targets and witness evaluation
refs: [definition:WE_CircuitSAT, note:pq-we-vww-lossless-packing, note:pq-we-compiler-transport]
tags: [witness-encryption, implementation, complexity]
---

The published tensor encoder and decoder use products of large residues by short signed integers. This note gives one exact arithmetic kernel for both operations, with a fallback for arbitrary residues. It retains both root branches and the full witness-selected path of [VWW Construction 6.2](https://ntt-research.com/wp-content/uploads/2023/01/Witness-encryption-and-null-iO-from-evasive-LWE.pdf). The matrix procedure changes neither the encryption law for common coins nor any decryption result. A codec such as the linked lossless format can supply its decoded integer arrays. The benchmark below starts with decoded arrays.

**Arithmetic guarantee.** For a tile of right-hand columns, center their residues modulo q and let L be the maximum column 1-norm. Split each canonical entry of the left matrix into base 2^b digits, using the largest b<=ceil(log2 q) with (2^b-1)L <= 2^53. On a zero tile return zero. If even b=1 exceeds this bound use ordinary unbounded-integer matrix multiplication and reduce once per output. Otherwise each digit and each right coefficient is exactly representable in binary64. Every scalar product and every partial sum of any subset of a dot product has absolute value at most 2^53. Thus a classical binary64 GEMM using ordinary products, adds or fused multiply-adds and conventional blocked accumulation returns each integer digit-plane dot exactly. This argument requires full binary64 precision and classical dot products. Algorithms that perform extra linear combinations (such as Strassen) or reduced-precision tensor operations need their own bounds. Convert the dots back to integers, reconstruct by Horner shifts, then reduce modulo q. Signed intermediate results and composite moduli are covered. Stacking the digit planes as matrix rows uses one GEMM per tile, and consecutive tiles with the same b reuse the expanded left matrix. Horner and final reduction use unbounded integers. The digit count is at most ceil(log2 q), keeping the bit clock polynomial. This is an implementation speedup without a reduction in the underlying scalar product count.

**Both honest algorithms.** The witness decoder applies the kernel successively to its selected blocks. For Enc, split the public matrix A into n-row blocks A_j. Stack the transposes of blocks used by the binary transition M. One multiplication by the small S-transpose yields all transposes of S A_j. Sum selected blocks and add the original E modulo q to form exactly (M tensor S) A + E. Consequently this computation can be followed by the same preimage sampler with the same target and coins. No new security or noise assumption enters the arithmetic. The measurements cover neither trapdoor generation nor column sampling.

**Single-core measurements.** AMD Ryzen 9 7950X3D, NumPy 2.5.3, OpenBLAS 0.3.34.106.0, OPENBLAS_NUM_THREADS=1. Wall-clock median of seven repetitions after an untimed equality check. The baseline uses Python integer arrays with NumPy matrix multiplication and reduces once per output matrix. For encryption the baseline already factors the tensor product. Both measurements include conversions performed by the new kernel and omit instance generation. Ciphertexts and secret factors for these arithmetic comparisons are synthetic; the times do not measure a full encryption or security-matched parameter set.

| Operation | Modulus | Integer baseline (ms) | Exact digit-plane kernel (ms) |
| --- | --- | ---: | ---: |
| Four-level witness path, 8 retained rows, width 384, final width 32 | 2^128-159 | 89.87 | 58.92 |
| Same dimensions | 7^81 | 96.97 | 63.50 |
| One factored encryption target, n=48, w=4, 96 columns | 7^81 | 33.33 | 16.41 |

Tests compared all eight paths in three-level chains across five moduli, six coefficient ranges and three tile sizes, 720 exact path equalities in total. A further 108 encryption targets were compared directly with explicit Kronecker products. Inputs exercise zero tiles, negative values, large representatives and wide-coefficient fallback. The benchmark is a comparison to one specific software baseline; there is no timing claim against optimized native multiprecision or GPU code.

Save the first listing as exact_eval.py. Run each of the next two listings as a separate Python process with OPENBLAS_NUM_THREADS=1.

~~~python
import numpy as np

def integers(values):
    return np.frompyfunc(int,1,1)(np.asarray(values,dtype=object))

def product_mod(rows,block,q,tile=128):
    """Rows times a signed transition block; return canonical residues."""
    if q<2 or tile<1:
        raise ValueError("invalid public parameters")
    X=integers(rows)%q
    D=integers(block)
    if X.ndim!=2 or D.ndim!=2 or X.shape[1]!=D.shape[0] or D.shape[0]==0:
        raise ValueError("incompatible matrix dimensions")
    # Choose centered representatives even for a transmitted raw residue block.
    D=D%q
    D=np.where(2*D>=q,D-q,D)
    out=np.empty((len(X),D.shape[1]),dtype=object)
    k=(q-1).bit_length()
    cached_b=None
    for start in range(0,D.shape[1],tile):
        T=D[:,start:start+tile]
        norm=int(np.max(np.abs(T).sum(axis=0)))
        if not norm:
            out[:,start:start+tile]=0
            continue
        b=min(k,((1<<53)//norm+1).bit_length()-1)
        if b==0:
            out[:,start:start+tile]=(X@T)%q
            continue
        # Pack the digit planes as extra matrix rows for a single CPU DGEMM.
        planes=(k+b-1)//b
        if b!=cached_b:
            mask=(1<<b)-1
            digits=np.concatenate([((X>>(b*i))&mask).astype(np.float64)
                                   for i in range(planes)])
            cached_b=b
        dots=(digits@T.astype(np.float64)).reshape(planes,len(X),T.shape[1])
        acc=np.zeros((len(X),T.shape[1]),dtype=object)
        for d in dots[::-1]:
            acc=(acc<<b)+d.astype(np.int64).astype(object)
        out[:,start:start+tile]=acc%q
    return out

def evaluate(root_pairs,transitions,witness_bits,q,tile=128):
    if len(witness_bits)!=1+len(transitions):
        raise ValueError("one branch choice is required per level")
    x=integers(root_pairs[witness_bits[0]])%q
    for bit,pair in zip(witness_bits[1:],transitions,strict=True):
        x=product_mod(x,pair[bit],q,tile)
    return x

def tensor_target(M,S,A,E,q,tile=128):
    """Compute (M tensor S) A + E mod q, with binary M and square S."""
    M=np.asarray(M)
    S=integers(S)
    A=integers(A)
    w,n=M.shape[0],S.shape[0]
    if (M.shape!=(w,w) or S.shape!=(n,n) or not np.all((M==0)|(M==1))
            or A.ndim!=2 or A.shape[0]!=w*n):
        raise ValueError("invalid tensor dimensions")
    E=integers(E)
    if E.shape!=A.shape:
        raise ValueError("invalid noise shape")
    used=np.flatnonzero(M.any(axis=0))
    result=E.reshape(w,n,-1).copy()
    if len(used):
        blocks=A.reshape(w,n,-1)[used]
        # Stack matrix transposes. Each group of rows uses the same small S.
        stacked=blocks.transpose(0,2,1).reshape(-1,n)
        products=product_mod(stacked,S.T,q,tile).reshape(len(used),-1,n).transpose(0,2,1)
        for j,B in zip(used,products):
            for i in np.flatnonzero(M[:,j]):
                result[i]+=B
    return result.reshape(E.shape)%q
~~~
~~~python
from itertools import product
from random import Random
from time import perf_counter
from statistics import median
import runpy,numpy as np
g=runpy.run_path('exact_eval.py')
r=Random(101)
def matrix(a,b,gen):
    return np.array([[gen() for _ in range(b)] for _ in range(a)],dtype=object)
cnt=0
for q in (2,7,2**64,7**81,2**128-159):
    for span in (0,1,127,2**52,2**54,2*q):
        for tile in (1,4,16):
            roots=[matrix(3,8,lambda:r.randrange(-q,q)) for _ in range(2)]
            trans=[[matrix(k,t,lambda:r.randint(-span,span)) for _ in range(2)] for k,t in [(8,9),(9,5)]]
            for path in product(range(2),repeat=3):
                x=roots[path[0]]%q
                for bit,pair in zip(path[1:],trans):
                    x=(x@pair[bit])%q
                assert np.array_equal(x,g['evaluate'](roots,trans,path,q,tile))
                cnt+=1
print('paths',cnt)
for q in (2**128-159,7**81):
    root=[matrix(8,384,lambda:r.randrange(q)) for _ in range(2)]
    trans=[[matrix(384,t,lambda:r.randrange(-1024,1025)) for _ in range(2)] for t in (384,384,32)]
    path=[1,0,1,0]
    def native():
        x=root[path[0]]%q
        for bit,pair in zip(path[1:],trans):
            x=(x@pair[bit])%q
        return x
    def exact():
        return g['evaluate'](root,trans,path,q)
    assert np.array_equal(native(),exact())
    ts=[[],[]]
    for _ in range(7):
        for i,fn in enumerate((native,exact)):
            t=perf_counter();fn();ts[i].append(perf_counter()-t)
    print(q.bit_length(),*(round(1000*median(x),2) for x in ts),flush=True)
~~~
~~~python
import runpy,numpy as np
from random import Random
from time import perf_counter
from statistics import median
r=Random(512)
g=runpy.run_path('exact_eval.py')
def mat(h,w,gen):
    return np.array([[gen() for _ in range(w)] for _ in range(h)],dtype=object)
cases=0
for q in (8,13,7**81):
 for n in (1,3,4):
    for w in (1,2,4):
        for bound in (2,2*q):
            S=mat(n,n,lambda:r.randint(-bound,bound));A=mat(n*w,7,lambda:r.randrange(q));E=mat(n*w,7,lambda:r.randint(-7,7))
            for M in (np.zeros((w,w),int),mat(w,w,lambda:r.randrange(2))):
                Y=g['tensor_target'](M,S,A,E,q)
                assert np.array_equal(Y,(np.kron(M,S)@A+E)%q)
                cases+=1
print('targets',cases)
q=7**81;n=48;w=4;t=96
M=np.array([[1,0,0,1],[1,1,0,0],[0,1,1,0],[0,0,1,1]])
S=mat(n,n,lambda:r.randint(-8,8));A=mat(w*n,t,lambda:r.randrange(q));E=mat(w*n,t,lambda:r.randint(-16,16))
def base():
    B=[S@a for a in A.reshape(w,n,t)]
    return np.concatenate([sum(B[j] for j in np.flatnonzero(row)) for row in M]).__add__(E)%q
def exact():
    return g['tensor_target'](M,S,A,E,q)
assert np.array_equal(base(),exact())
for fn in (base,exact):
    times=[]
    for _ in range(7):
        t0=perf_counter();fn();times.append(perf_counter()-t0)
    print(round(median(times)*1000,2))
~~~
