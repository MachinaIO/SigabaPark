---
title: Sampling projected AFV sign noise with a finite random-bit budget
refs: [definition:WE_CircuitSAT, theorem:AdvancedEncryption.WE.SignNoise.exact_bit_floor, theorem:AdvancedEncryption.WE.SignNoise.ambiguous_prefix_count]
tags: [witness-encryption, predicate-encryption, lwe, cost]
---

PR #88 compiles split-witness incompatibility to a binary inner-product predicate and keeps one gadget digit per coordinate in the AFV encryption scheme. For p retained coordinates and AFV matrix width m, an encryption still specifies p independent m-by-m sign matrices. This note removes the need to generate most of their sign bits on noise profiles with repeated magnitudes. It gives an exact variable-length sampler, an explicit bounded-clock variant with a table-wide statistical error budget, and a lower bound distinguishing the two. It changes the noise-generation step of [AFV Section 4.1](https://theory.stanford.edu/~dfreeman/papers/FuncEnc.pdf); the ordinary decision-LWE premise and the quantitative security gaps of #88 still apply.

**Conditional distribution.** Fix the centered base error vector x used in this one AFV ciphertext. The sign matrices occur in encryption only through D=pm scalar coordinates of their products R_i^T x. Conditional on x, these are independent copies of the sum of m independent signs times x_j. Discard zeros, group equal absolute magnitudes a, and split each group into chunks of c≤W equal entries. Draw independent K~Binomial(c,1/2) for each chunk and each scalar; add a(2K-c). This recovers exactly the original joint law, including dependence on the base ciphertext through the common x. Fresh chunk draws are essential. Sampling each output from an unconditional marginal would not preserve the joint ciphertext. Reducing the resulting signed integers modulo q preserves the coupling.

**A limit on exact worst-case savings.** Take x all ones and q>2m. All D scalar outputs attaining +m has probability 2^(-mD), since every sign is then positive. Under a b-bit fair tape every event has probability an integer multiple of 2^-b; even an adaptive sampler bounded by b bits can be padded to exactly b. Matching this one atom requires b≥mD. The Lean theorem exact_bit_floor proves the finite counting statement for positive-sign counts. It is a lower bound for the exact conditional noise kernel on this input, not for AFV ciphertext generation by every possible method. Exact average-case savings and statistically close bounded worst-case savings are both possible.

**Prefix sampler.** For each chunk length c, place intervals of integer lengths choose(c,k) in [0,2^c). Start with b_c=min(c,ceil(log2 c)+s) independent bits, for an integer slack s≥0. When b_c=c one can return an exact popcount. Otherwise the initial prefix identifies an equal-width dyadic cell. If it lies within one outcome interval, return its label. If a CDF boundary is strictly inside, read another fair bit and refine until the cell is contained. No draw uses more than c bits. Coupling with a uniform c-bit integer (the unread suffix may be discarded) proves exactness. All chunk distributions and decision tables depend only on c, allowing reuse across every WE entry. In the reference native kernel the hot path is a lookup and a traversal of the precomputed binary tree. Public sign statistics are not required; the histogram of the secret base error and the consumed bit count are internal values.

**Uniform reservoir bound.** Let E be the number of extra bits of one refinable draw. An ambiguous prefix of length b_c+j must contain an interior boundary, so there are at most c such prefixes among 2^(b_c+j). This is the finite counting lemma ambiguous_prefix_count. Thus Pr[E>j]≤2^(-s-j). Conditional on x, take independent exact draws as the comparison experiment. At z=sqrt(2), the tail-sum identity gives

    E[z^E] = 1+(z-1) sum_(j>=0) z^j Pr[E>j] ≤ 1+sqrt(2)·2^-s.

For N refinable draws, multiplication and Markov give Pr[sum E > B]≤2^(-B/2 + 3N·2^-s), using sqrt(2)/ln(2)<3. Include all D scalar outputs in N. Reserve the exact first-prefix cost A=sum b_c over all draws, plus B=2 tau+6 ceil(N/2^s) bits. Abort the complete encryption with a fixed failure result before exceeding A+B. This couples to the exact sampler except with probability ≤2^-tau per ciphertext for every allowed x. The pseudorandom engines in the test code are for measurements only; the construction uses independent fair bits. With a word refill implementation there may be up to one partially consumed word; track or charge it separately.

**Uniform support and the whole WE table.** A bound based only on an observed histogram does not reduce the registered worst-case clock. One way to obtain a public bound is to abort on any |x_j|>T. In AFV Definition 3.6 the rounded pre-modular Gaussian has standard deviation sd=q alpha/sqrt(2 pi) before rounding. For a public attribute-entry cap C, use

    T = ceil(1/2 + sd sqrt(2 ln(2mC·2^133))),   tau = 133 + ceil(log2 C).

The centered modular magnitude is at most the unwrapped rounded magnitude. A Gaussian tail and a union bound over mC entries bound the large-magnitude event by 2^-133. A union bound over C reservoirs contributes at most another 2^-133. Under these caps the complete WE ciphertext distribution for each bit is within TV distance 2^-132 of the original, including an abort symbol if used. An experiment or quantum measurement on that classical output cannot enlarge the distance. A distinguishing gap increases by at most 2·2^-132, and the correctness failure by at most 2^-132. Leave explicit margins in the original proof: for example ideal correctness error ≤2^-129 suffices; an ideal squared-advantage bound at 130 bits rather than 128 leaves margin for this change for adversary costs at least one. Finite approximation of AFV's own Gaussians needs its own budget. This argument does not turn asymptotic AFV security into a concrete parameter guarantee.

There are at most H=floor(m/W)+T nonempty chunks per scalar (full chunks plus at most one remainder per magnitude). Hence the first-prefix total is at most D H (ceil(log2 W)+s) and N≤DH. For the public cap C=41,923,871,289,682 from #88 and the illustrative values p=117, m=2^19, W=1024, s=2, sd=64, these formulas give T=1062, H=1574, D=61,341,696 and tau=179. The ceiling on conditional sign-noise fair bits per AFV entry is **1,303,449,698,662**, versus **32,160,715,112,448** explicit matrix sign bits, a factor 24.67. This arithmetic is not an AFV parameter selection. It excludes all other encryption coins, public matrix products, trapdoor/key costs and ciphertext bytes. If the certified bound is unfavorable the public parameter choice can retain the original kernel.

**Costs of implementing it.** At a finest prefix depth at most c cells can be ambiguous; over all depths the refinement tree has O(c²) interior nodes. Its coarse table uses at most 2^(ceil(log2 c)+s) slots for c>b_c. For all chunk sizes through W the total preprocessing and storage are finite; storing all trees costs O(W³+2^s W²) words. Counts and widths also determine their bit lengths. Charge table construction or its hardwired description and the tape cost of lookups. The reference computes binomial integers exactly and stores only fixed-width pointers in the native decision tables. The bound on output-side work is one initial lookup or popcount per draw and at most B refinement bits/steps, plus chunk arithmetic, indexing, sorting/grouping and the base vector. It does not claim a RAM lookup costs one step on the registered tapes.

**Native kernel measurements.** The following local x86-64 benchmark uses W=256, s=2, 4,096 scalar outputs, five repetitions per row, and reports median kernel time. It excludes precomputation, file load, grouping, AFV public-matrix products, and cryptographic entropy-source costs. A comparison with exact grouped popcount already omits zero coordinates. A second exact baseline bit-slices the magnitudes and contracts each random sign word with those planes. Bit counts below are consumed pseudorandom stream bits on the last of the five runs. The capped prefix kernel completed every run. The Python checker below also shows that per-draw interpreter overhead can reverse the native result. The benchmarks use synthetic rounded Gaussian profiles and are not encryption benchmarks.

| m | sd | Exact grouped bits | Prefix bits | Grouped ms | Prefix ms | Bit-plane ms |
|---:|---:|---:|---:|---:|---:|---:|
| 4096 | 2 | 13529088 | 659059 | 0.41 | 0.19 | 0.83 |
| 16384 | 8 | 63848448 | 3028730 | 1.89 | 0.86 | 4.02 |
| 65536 | 64 | 266653696 | 14641765 | 8.47 | 4.62 | 20.63 |
| 4096 | 1024 | 16760832 | 16430156 | 12.36 | 11.51 | 1.68 |

The high-diversity row favors the bit-plane kernel. In the three rows with repeated magnitudes, the prefix kernel took about 1.8–2.2 times less time than grouped popcount and consumed about 18–21 times fewer bits. The W=256 native tables occupy about 30 MiB (around 15 ms to load in this run). Neither that size nor those timings apply to the W=1024 arithmetic example.

**Reproduction.** The first Python program exhausts small fair tapes and compares the complete signed-sum histogram to enumeration; it also recomputes the diagnostic bounds. For the native experiment save the next two listings as make_tables.py and bench.cpp. Use a little-endian x86-64 machine, run python3 make_tables.py tables.bin, compile with g++ -O3 -std=c++17 -mpopcnt bench.cpp -o bench, then run ./bench tables.bin. The native executable independently exhausts tapes through c=13.

### Distribution and budget checks

~~~python
from bisect import bisect_right
from collections import Counter
from functools import lru_cache
from itertools import product
from math import ceil, comb, log, log2, sqrt
from random import Random
from statistics import median
from time import perf_counter

class BudgetExceeded(Exception):
    pass

@lru_cache(None)
def sampler_table(c,slack):
    b=min(c,(c-1).bit_length()+slack)
    if b==c:return b,None,None
    total=0;ends=[]
    for k in range(c):
        total+=comb(c,k)
        ends.append(total)
    shift=c-b
    coarse=[]
    for u in range(1<<b):
        lo=u<<shift
        i=bisect_right(ends,lo)
        coarse.append(i if i==c or ends[i]>=lo+(1<<shift) else -1)
    return b,ends,coarse

class Bits:
    def __init__(self,seed,limit=None):
        self.rng=Random(seed);self.count=0;self.limit=limit
    def take(self,n):
        if self.limit is not None and self.count+n>self.limit:raise BudgetExceeded
        self.count+=n
        return self.rng.getrandbits(n)

def bin_draw(c,slack,take):
    b,ends,coarse=sampler_table(c,slack)
    u=take(b)
    if b==c:return u.bit_count()
    k=coarse[u]
    rem=c-b
    while k<0:
        u=(u<<1)|take(1);rem-=1
        lo=u<<rem
        i=bisect_right(ends,lo)
        k=i if i==c or ends[i]>=lo+(1<<rem) else -1
    return k

def chunks(x,width):
    plan=[]
    for a,multiplicity in sorted(Counter(abs(v) for v in x if v).items()):
        full,tail=divmod(multiplicity,width)
        if full:plan.append((a,width,full))
        if tail:plan.append((a,tail,1))
    return plan

def draw(plan,D,width,slack,seed,method,tau=180):
    first=0;refinable=0
    for a,c,t in plan:
        b=min(c,(c-1).bit_length()+slack)
        first+=D*t*b
        if b<c:refinable+=D*t
    extra=2*tau+6*((refinable+(1<<slack)-1)>>slack)
    bits=Bits(seed,first+extra if method=='bounded' else None)
    out=[0]*D
    for a,c,t in plan:
        for _ in range(t):
            for j in range(D):
                k=bits.take(c).bit_count() if method=='popcount' else bin_draw(c,slack,bits.take)
                out[j]+=a*(2*k-c)
    return out,bits.count,first+extra

# Exhaust every uniformly random tape for each small block; read its MSBs in order.
for c in range(1,14):
    for slack in (0,2):
        hist=Counter()
        for tape in range(1<<c):
            state=[c]
            def take(n):
                state[0]-=n
                assert state[0]>=0
                return (tape>>state[0])&((1<<n)-1)
            hist[bin_draw(c,slack,take)]+=1
        assert [hist[k] for k in range(c+1)]==[comb(c,k) for k in range(c+1)]
x=[-3,0,1,1,-3,2,-1]
direct=Counter(sum(s*v for s,v in zip(signs,x)) for signs in product((-1,1),repeat=len(x)))
dist=Counter({0:1})
for a,c,t in chunks(x,2):
    for _ in range(t):
        tmp=Counter()
        for total,freq in dist.items():
            for k in range(c+1):tmp[total+a*(2*k-c)]+=freq*comb(c,k)
        dist=tmp
assert direct==Counter({v:f*(1<<x.count(0)) for v,f in dist.items()})

# Diagnostic workload only.  D=512 is a sample of columns, not a full encrypted table.
for m,sigma in [(4096,2),(16384,8),(65536,64),(4096,1024)]:
    r=Random(890)
    x=[round(r.gauss(0,sigma)) for _ in range(m)]
    plan=chunks(x,256);slack=2;D=512
    start=perf_counter()
    for _,c,_ in plan:sampler_table(c,slack)
    build=perf_counter()-start
    data=[]
    for mode in ('popcount','bounded'):
        times=[]
        for repeat in range(3):
            start=perf_counter()
            out,coins,cap=draw(plan,D,256,slack,8900+repeat,mode)
            times.append(perf_counter()-start)
        data.append((coins,round(1000*median(times),2)))
    print(m,sigma,len(plan),'cache setup ms',round(1000*build,2),'bits and ms',data,'cap',cap)

# Illustrative parameter arithmetic; no hardness estimate or complete AFV instantiation.
C=41923871289682;p=117;m=1<<19;W=1024;slack=2;sd=64
tau=133+(C-1).bit_length()
T=ceil(0.5+sd*sqrt(2*(log(2*m*C)+133*log(2))))
D=p*m;H=m//W+T
J=D*H
bound=J*((W-1).bit_length()+slack)+2*tau+6*((J+(1<<slack)-1)>>slack)
print('tau,T,H,D',tau,T,H,D)
print('fresh bits per CT: sign matrices',D*m,'bounded',bound,'ratio',round(D*m/bound,2))
~~~

### Decision-table generator

~~~python
from bisect import bisect_right
from math import comb
from struct import pack
from array import array
from sys import argv,byteorder
assert byteorder=='little' and array('i').itemsize==4
with open(argv[1],'wb') as f:
    for c in range(1,257):
        b=min(c,(c-1).bit_length()+2)
        ends=[];s=0
        for j in range(c):
            s+=comb(c,j);ends.append(s)
        children=array('i')
        def make(lo,rem):
            i=bisect_right(ends,lo)
            if i==c or ends[i]>=lo+(1<<rem):return ~i
            a=make(lo,rem-1);d=make(lo+(1<<(rem-1)),rem-1)
            children.extend((a,d));return len(children)//2-1
        pref=array('i',(make(u<<(c-b),c-b) for u in range(1<<b))) if b<c else array('i')
        f.write(pack('<iii',b,len(pref),len(children)))
        pref.tofile(f);children.tofile(f)
~~~

### Native comparison

~~~cpp
#include <fstream>
#include <stdexcept>
#include <algorithm>
#include <array>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <map>
#include <random>
#include <utility>
#include <vector>

using namespace std;
using Clock=chrono::steady_clock;
struct Source {
    mt19937_64 gen;
    uint64_t buf=0, bits=0, limit;
    unsigned avail=0;
    Source(uint64_t seed,uint64_t cap=UINT64_MAX):gen(seed),limit(cap){}
    uint64_t take(unsigned n){
        if(n>limit-bits)throw overflow_error("fair-bit reservoir");
        bits+=n;
        if(n==0)return 0;
        if(n==64 && !avail)return gen();
        if(n>avail){
            unsigned missing=n-avail;
            uint64_t w=gen(),ret=buf|(w<<avail);
            buf=w>>missing;avail=64-missing;
            return n==64?ret:ret&((1ULL<<n)-1);
        }
        uint64_t ret=buf&((1ULL<<n)-1);
        buf>>=n;avail-=n;return ret;
    }
    int pop(int c){
        int k=0;
        while(c>=64){k+=__builtin_popcountll(take(64));c-=64;}
        return k+__builtin_popcountll(take(c));
    }
};
struct Bin {
    int c,b;
    vector<int> prefix;
    vector<array<int,2>> children;
    Bin(int n,ifstream& f):c(n){
        int entries,ints;
        f.read(reinterpret_cast<char*>(&b),4);
        f.read(reinterpret_cast<char*>(&entries),4); f.read(reinterpret_cast<char*>(&ints),4);
        prefix.resize(entries); children.resize(ints/2);
        f.read(reinterpret_cast<char*>(prefix.data()),4*entries);
        f.read(reinterpret_cast<char*>(children.data()),4*ints);
        if(!f)throw runtime_error("invalid table file");
    }
    template <class Stream> int lookup(Stream& s)const{
        if(b==c)return s.pop(c);
        int node=prefix[s.take(b)];
        while(node>=0)node=children[node][s.take(1)];
        return ~node;
    }
};
struct Group {int a,c,t;};
uint64_t hashout(const vector<int64_t>& o){
    uint64_t h=0;
    for(auto x:o)h=h*1000003+uint64_t(x);
    return h;
}
struct Tape {
    uint64_t tape;
    int rem;
    uint64_t take(unsigned n) {
        if(int(n)>rem)throw runtime_error("too many fair bits");
        rem-=n;return (tape>>rem)&((1ULL<<n)-1);
    }
    int pop(int c){return __builtin_popcountll(take(c));}
};
int main(int argc,char** argv){
    if(argc!=2)return 1;
    const int D=4096,W=256;
    map<int,Bin> tables;
    auto load=Clock::now();
    ifstream file(argv[1],ios::binary);
    for(int c=1;c<=W;++c)tables.try_emplace(c,c,file);
    cerr<<"table load ms "<<chrono::duration<double,milli>(Clock::now()-load).count()<<endl;
    for(int c=1;c<=13;++c){
        vector<int> hist(c+1);
        for(int tape=0;tape<(1<<c);++tape){
            Tape t{uint64_t(tape),c};++hist[tables.at(c).lookup(t)];
        }
        int choose=1;
        for(int k=0;k<=c;++k){
            if(hist[k]!=choose)throw runtime_error("incorrect exact distribution");
            choose=choose*(c-k)/(k+1);
        }
    }
    for(auto [m,sd]:vector<pair<int,int>>{{4096,2},{16384,8},{65536,64},{4096,1024}}){
        mt19937_64 src(890);
        normal_distribution<double> norm(0,sd);map<int,int> mult;
        for(int i=0;i<m;++i){int a=abs(int(llround(norm(src))));if(a)++mult[a];}
        vector<Group> plan;
        auto init=Clock::now();
        for(auto [a,c]:mult){
            if(c/W)plan.push_back({a,W,c/W});
            if(c%W)plan.push_back({a,c%W,1});
        }

        uint64_t first=0,refine=0;
        int maximum=mult.rbegin()->first;
        int levels=0;while((1<<levels)<=maximum)++levels;
        vector<vector<uint64_t>> planes((m+63)/64,vector<uint64_t>(levels));
        int slot=0;int64_t l1=0;
        for(auto [a,count]:mult)for(int h=0;h<count;++h,++slot){
            l1+=a;
            for(int j=0;j<levels;++j)if((a>>j)&1)planes[slot/64][j]|=1ULL<<(slot%64);
        }
        for(auto g:plan){
            auto& tab=tables.at(g.c);
            first+=uint64_t(D)*g.t*tab.b;
            if(tab.b<g.c)refine+=uint64_t(D)*g.t;
        }
        uint64_t cap=first+360+6*((refine+3)/4);
        double setup=chrono::duration<double,milli>(Clock::now()-init).count();
        cout<<m<<" "<<sd<<" setup_ms="<<setup;
        for(int mode=0;mode<3;++mode){
            vector<double> ts;uint64_t coins=0,digest=0;
            for(int rep=0;rep<5;++rep){
                Source s(891+rep,mode==1?cap:UINT64_MAX);vector<int64_t> out(D);
                auto start=Clock::now();
                if(mode==2){
                    for(auto& v:out){
                        int64_t pos=0;
                        for(size_t block=0;block<planes.size();++block){
                            auto signs=s.take(min(64,m-int(64*block)));
                            for(int j=0;j<levels;++j)pos+=int64_t(__builtin_popcountll(signs&planes[block][j]))<<j;
                        }
                        v=2*pos-l1;
                    }
                }else for(auto g:plan){
                    auto& tab=tables.at(g.c);
                    for(int t=0;t<g.t;++t)for(auto& v:out){
                        int k=mode?tab.lookup(s):s.pop(g.c);
                        v+=g.a*(2*k-g.c);
                    }
                }
                ts.push_back(chrono::duration<double,milli>(Clock::now()-start).count());
                coins=s.bits;digest^=hashout(out);
            }
            sort(ts.begin(),ts.end());
            cout<<(mode==1?" prefix":mode==2?" bitplane":" pop")<<"_ms="<<ts[2]<<" bits="<<coins<<" digest="<<digest;
        }
        cout<<endl;
    }
}
~~~

## What happens if the sign matrices share factors as in Praxis?

[Praxis, Section 2.5 and Figure 5](https://eprint.iacr.org/2026/2971) stores factors on the vertices of a bipartite grid and pairs them to recover virtual cells. For 6,912 copies its example takes 528 group elements per unknown in place of 41,472. Its security argument accommodates the shared hidden scalars and tie masks. Consider using the same layout for AFV's independent signs. The following conditional calculation quantifies exactly where the analogy fails.

Represent the desired output columns by edges of a finite simple bipartite graph with v incident vertices, e edges and k connected components. For each base coordinate j, independently sample one fair sign at every vertex and give edge uv the product of its endpoint signs. For a forest, fixing one root sign per component gives a bijection from the remaining vertex signs to the edge signs. The construction is exact, and still needs e independent bits per j. For a graph with cycles, the edge signs form a binary subspace of codimension b=e-v+k after identifying minus with one: signs multiply to one around every cycle, and every assignment on a spanning forest extends uniquely.

These dependencies can survive summing the coordinates. Fix integer x with at least one odd entry and q>2 sum_j |x_j|, so the centered lift of each projected scalar Y_e is exact. Put S=sum_j x_j. The bit (S-Y_e)/2 modulo two is the parity of the negative signs on the odd coordinates. In the original encryption these e bits are independent and fair. In the shared version their vector belongs to the same subspace, since it is a sum of vectors from that subspace. Thus conditional TV distance of the projected noise vectors is at least 1-2^(-b). Even one 2-by-2 rectangle gives 1/2. The event can be evaluated on conditional noise; it gives no attack on the public ciphertext and makes no claim about the frequency of eligible x under a concrete AFV parameter set. It rules out justifying this reuse by a pointwise distribution-preserving argument. The sampler below shares public tables and keeps fresh independent draws for each edge.

## A smaller reservoir using binomial generating trees

For a chunk of size c, write each integer weight binom(c,i) in binary. Put one leaf labelled i at depth j for each set bit at position c-j. The dyadic masses sum to one. At each depth double the surviving index, add the next fair bit, and assign the first indices to that depth's leaves. Subtract their count if the draw continues. Kraft equality ensures all paths terminate by c, and each label receives exactly its binomial mass. This is the discrete distribution generating tree of Knuth and Yao; see also [Saad et al.](https://arxiv.org/abs/2003.03830).

Let z=65/64. With n_j leaves at depth j, the length L has moment M_c=E[z^L]=sum_j n_j (65/128)^j. The code below uses outward rounding after each Horner step and computes integers h(c) satisfying M_c^32 <= z^h(c). To charge partial chunks separately, choose integers d and a >= 0 satisfying h(W)<=d and W h(c)<=dc+a for 1<=c<W. At most T magnitudes have a partial chunk. Thus per output the sum of h(c) over all chunks is at most (dm+Ta)/W. Conditional independence and Markov's inequality give a reservoir of ceil(D(dm+Ta)/(32W))+t bits with overflow probability at most z^(-t). For tau=179, t=8003 gives z^(-t)<=2^-179.

At W=1024 the certified pair is (d,a)=(230,164572). With the same illustrative public caps the reservoir is **552,917,117,891 fair bits per AFV entry**, a factor **58.17** below explicit signs. At W=256 it is 1,060,130,920,259 bits. The table-wide statistical budget is unchanged. These are uniform analytical bounds. Native timings above cover the CDF sampler only. The listing computes the certificate and exhaustively verifies the label distribution for c up to 13.

~~~python
from math import comb
from collections import Counter
from functools import lru_cache

def coeffs(c):
    v=1
    for k in range(c+1):
        yield v
        v=v*(c-k)//(k+1)

def populations(c):
    # Count the ones in each column of binomial coefficients simultaneously.
    planes=[]
    for carry in coeffs(c):
        for i,plane in enumerate(planes):
            planes[i]=plane^carry
            carry&=plane
            if not carry:break
        if carry:planes.append(carry)
    return [sum(((x>>b)&1)<<i for i,x in enumerate(planes)) for b in range(c)]

@lru_cache(None)
def labels(c):
    weights=list(coeffs(c))
    return [[i for i,v in enumerate(weights) if (v>>(c-d))&1] for d in range(1,c+1)]

def sample(c,bit):
    j=0
    for row in labels(c):
        j=2*j+bit()
        if j<len(row):return row[j]
        j-=len(row)
    raise AssertionError

def moment_cap(c):
    scale=1<<80;bound=0
    for count in populations(c):
        bound=(65*(bound+count*scale)+127)//128
    return bound

def units(bound):
    # Smallest h giving (bound/2^80)^32 <= (65/64)^h.
    a=bound**32
    den=(1<<80)**32
    lo=-1;hi=40000
    while hi-lo>1:
        j=(lo+hi)//2
        if a*(64**j)<=den*(65**j):hi=j
        else:lo=j
    return hi

for c in range(1,14):
    h=Counter()
    for tape in range(1<<c):
        bits=iter((tape>>j)&1 for j in range(c))
        h[sample(c,lambda:next(bits))]+=1
    assert [h[j] for j in range(c+1)]==list(coeffs(c))
    assert populations(c)==[len(row) for row in reversed(labels(c))]

def excess(tau):
    z=0;a=1;b=1<<tau
    while a<b:a*=65;b*=64;z+=1
    return z

C=41923871289682;m=1<<19;p=117;D=p*m;T=1062;W=1024
maxv,maxc=max((moment_cap(c),c) for c in range(1,W+1))
h=units(maxv);tau=133+(C-1).bit_length()
N=D*(m//W+T)
B=(N*h+31)//32+excess(tau)
print('max moment, c, h/32, extra and capped bits:',maxv,maxc,h,excess(tau),B)
print('baseline ratio',round(D*m/B,2))

from bisect import bisect_left
# Precompute the largest permitted integer moment bound for each h.
# Taking a 32nd root is unnecessary: compare the 32nd powers.
cutoff=[((1<<80)**32*65**j)//64**j for j in range(h+1)]
cost=[0]+[bisect_left(cutoff,moment_cap(c)**32) for c in range(1,W+1)]
assert max(cost) <= h and cutoff[-1] >= maxv**32
for width in (64,128,256,512,1024):
    best=None
    for d in range(cost[width],cost[width]+513):
        overhead=max([0]+[width*cost[c]-d*c for c in range(1,width)])
        value=d*m+T*overhead
        cand=value,d,overhead
        if best is None or cand<best:best=cand
    value,d,overhead=best
    cap=(D*value+32*width-1)//(32*width)+excess(tau)
    print('W,d,overhead,cap,ratio:',width,d,overhead,cap,round(D*m/cap,2))
~~~
