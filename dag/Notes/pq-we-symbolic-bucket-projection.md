---
title: A bounded symbolic NAND compiler for existential private-tail projection
refs: [definition:WE_CircuitSAT_Capped, theorem:AdvancedEncryption.WE.SymbolicBucket.step, theorem:AdvancedEncryption.WE.SymbolicBucket.cut_image, note:pq-we-cut-width-compiler]
tags: [witness-encryption, circuit-sat, compiler, cost]
---

The existential projection of [PR 148](https://github.com/MachinaIO/SigabaPark/pull/148) replaces the private computation on the tail by P(p)=exists u phi(p,u). Here the front p remains symbolic. A compiler taking a public raw circuit and a fixed tail produces an ordinary NAND list on p, with the two concrete algorithms below. The supplied Python is a reference implementation, not a certified Turing-machine clock.

**Raw format and baseline.** For gate j replace each operand >=n+1+j by wire zero, the true constant. Read wire 0 as true, input wires 1 through n in order, and the last gate as output. These are the registered semantics even for a self-reference. Traverse gates backwards from the output to remove dead code. In gate order record the set S_j of tail inputs on which its operands structurally depend. A baseline memoizes a gate per assignment to S_j, projecting this index into each predecessor's table. The final OR of all output entries represents exactly the cofactor existential. Before simplification the NAND copy count is sum_j 2^|S_j| over live gates, plus at most 3(2^|S_out|-1) NANDs for a binary OR tree. Induction on the normalized gate order proves correctness; each access restricts the same tail assignment. This is an explicit finite fallback for any registered circuit, including where it is much too expensive.

**Symbolic bucket elimination.** Compute front-only live gates as shared front terms. For other gates introduce an existential output bit z_j. Make the factor z_j ↔ NAND(a,b) and require the output bit to be true. For fixed complete inputs all z_j have exactly one assignment satisfying the gate factors, by induction on j. A local factor table is indexed by its distinct tail/intermediate variables only. Each entry is a Boolean term in the front inputs. Repeated wire reads use the same index, true and front-only gates enter the expression directly, and frontier inputs are never jointly enumerated.

Choose a public order. To eliminate v, gather all incident factors, conjoin all their tables on each complete assignment to their scope union, and OR the two slices for v. Keep the other factors. The Lean node step proves this step for an arbitrary front evaluation and NAND-DAG realization. It includes the two-NAND definition of binary AND and the three-NAND OR. The nonincident condition holds because their tables do not read v. The conjunction of the new factors represents exactly the existential of the previous conjunction for *every* remaining assignment. Repetition and the initial functional gate equations prove the paper-level correctness of the full reference compiler. Existentially projecting the factors independently would be wrong when, for example, the incident constraints require opposite values of v.

The listing uses hash-consed AND nodes and signed edges, simplifies constants/equalities/complements, and materializes shared NANDs and required inversions only when emitting the reachable answer. Its final circuit returns the required wire even when that wire was an input or constant. The Lean step verifies the Boolean operation, not a refinement proof for Python dictionaries or for the full compiler. The cut-width note enumerates a circuit-order cut for its particular branching-program or clause representation. Here the enumerated objects are assignments to the *eliminated-variable factor scopes*, and table entries are ordinary front-input circuits. A large front state space is not multiplied into each table.

**Width and construction costs.** Take W to count the eliminated variable itself in the joined scope. An initial live gate factor has at most eight entries. For an elimination with k<=W joined variables and d incident factors, the reference performs d·2^k factor reads, 2^k slice assignments, at most d·2^k AND constructions and 2^(k-1) OR constructions. It writes 2^(k-1) new entries. Forming an index by gathering source coordinates costs at most W bit extractions per read when W>=3. For F<=4097 original factors and E<=4224 eliminated variables, sum d<=F+E: each original or produced factor can be consumed only once. Thus reads are at most (F+E)·2^W on a passing run. Initial entries are at most 32770; accumulated new entries are bounded by E·2^(W-1). Also charge gate walks, scope union, the final conjunction, dictionary operations, circuit serialization, and front input remapping. Scanning all surviving factors costs at most O(E F W) scope-membership operations; an indexed implementation can instead maintain incident lists. A deterministic comparison list can replace hash tables at up to linear search per lookup, giving a finite worst-case even without constant-time hashing. If D distinct AND terms were created, reachable NAND emission uses at most two per internal term, one inversion per referenced negative front input/constant and two final gates. For a G-gate residual with n' inputs the registered unary gate-list encoding is at most G[6(n'+G)+3] bits; exactly 4a+2b+3 bits for an operand pair (a,b). These are symbol/bit counts, not a bound that treats an arbitrary-memory access as a single multi-tape step.

The local order used here sorts live existential variables by the last gate reading or defining them, ties by wire number. All choices use only phi. Verify a supplied alternative by checking for duplicates and missing live variables and recomputing the union widths, rather than trusting a claimed width. Abort before allocating the violating bucket. A cumulative cell cap also bounds sequential allocation on the small-width path. At a width failure, use the support-copy compiler if the *same* projected semantics are required, or retain the original private input dimensions and use the unprojected backend. For the latter the returned branch identifier and tail selection must be public functions of phi and recorded in the ciphertext. Neither fallback supplies a general small-cost bound. A worst-case finite correct fallback can always enumerate all assignments, at the known exponential price. Testing several candidate sets/orders costs their searches even if only one is used. The prover/witness never chooses a favorable mode after encryption.

**Fixtures.** The deterministic tests compare both compilers with brute-force tail enumeration on all 625 two-gate, two-input raw NAND lists (including self and forward reads), both front assignments, for 1,250 comparisons. In the 4096-gate chain fixture the logical predicate is psi(p) AND the conjunction of (u_i OR p_2), padded by pairs of inversions. Every tail can be set true, so its projection is psi(p). With psi=p_1 the following counts use the same public last-use ordering, W=9 and a cumulative cap of one million cells:

| Tail bits | Support-copy NANDs before final OR/simplification | Max joined scope | Initial + generated cells | Factor reads | Emitted NANDs | Raw/compiled unary bits |
|---:|---:|---:|---:|---:|---:|---:|
|12|16,547,896|3|24,595|32,804|2|53,463,176 / 714|
|13|33,046,589|3|24,591|32,800|2|53,460,678 / 708|
|64|69,728,692,598,622,105,108,796|3|24,699|33,012|2|53,294,020 / 402|

A front-only 500-NAND preamble in place of p_1 survives unchanged in size: for 13 tail bits the compiler produced 500 gates using 21,591 cells, 14,426 slice assignments and 28,800 factor reads, creating 537 symbolic AND terms in total. More generally any front-only predicate can occupy this position; exact projection does not imply that deciding SAT for the resulting front program is easy. Conversely, when its support is tiny, exhaustive SAT on that support gives a direct statement-specific shortcut: send the payload on a satisfiable statement and a fixed dummy bit on an unsatisfiable one. Certification or the tiny-support test must happen before branch selection; this shortcut has no worst-case generality.

In the adverse fixture distribute all 128 inputs cyclically among six cliques and put NAND(a,b) into the required conjunction for every distinct pair within a clique; pad to 4096. For the last 64 inputs as tail the stated order stops at wire 179, joined width 10, after 21,790 cumulative cells and 6,080 reads; the violating bucket was never expanded. More strongly, *every* choice of 64 tail variables puts at least 11 in some clique. Each such input pair occurs in a live factor. In ordinary syntactic scope elimination a pair initially co-occurring remains adjacent while neither endpoint is removed: eliminating a third variable from their factor puts both in the joined output scope. Hence the first eliminated tail variable of that clique has a joined scope of at least 11 regardless of order. This refutes a universal W=9 guarantee for this method even with adaptive public choice of those 64 bits. It does not rule out algebraic simplification, a different tail size, or a direct SAT shortcut (indeed all-zero satisfies the clique predicates). The two cliques of size 22 and four of size 21 require 1302 pair tests and 3906 NANDs including the conjunction, before padding.

**Small image variant.** If all tail dependence crosses a certified affine map A u + c(p) over GF(2), use a basis B for the image of A. Extend pivot columns with their known preimages; a rank-k matrix then supplies a surjection from tail assignments to k coordinates. The residual predicate can be ORed over the 2^k vectors c(p)+Bz, with XOR circuits, offsets, residual copies and the OR charged. Node cut_image proves the existential substitution given the pointwise factorization and surjection. It does not infer such a factorization from a raw nonlinear NAND list. A public certificate can verify affine rows, a pivot basis and its preimages, and structural separation from all remaining tail wires. An unsupported separation claim must take the fallback.

**The private path.** In the PR 148 rank-four field ledger with K=64, a 22-bit remaining private terminal and ideal 2z+1 word-return accounting from [PR 146](https://github.com/MachinaIO/SigabaPark/pull/146), the 12-tail-bit example leaves 4,194,304 bits after 4,290,772,992 charged fields. The concrete parse-first pipeline alone scans 53,463,176 input bits *before* generating the backend, already exceeding that margin for this fixture. This sequential-stage comparison is not a lower bound for all streaming machines. With 13 tail bits the fields are 3,753,902,080 and leave 541,065,216 bits. The 500-gate projected function plus a two-NAND payload AND yields a particular selected 502-gate ordinary endpoint in a straightforward padded [PR 145](https://github.com/MachinaIO/SigabaPark/pull/145) independent-label implementation. At w=129 its four-row cells and final decoding bit cost 259,033 bits per such generated garbling, 4,016 two-input-position pad evaluations to issue the rows and 1,004 to evaluate the selected path. For the two-gate residual, the corresponding four-gate endpoint uses 2,065 bits, 32 issuing pad computations and eight evaluating pad computations. These counts can be reduced with a different compilation of the final AND. They are charges for an explicit endpoint, not the price of every nested issuer and aggregator. For M actual copies charge M times the indicated issuance/generation cost; do not multiply a selected-path count by M or assume M=1 for the whole transcript. Include private parameter seeds or lookup keys, public selector metadata, control/terminal fields, other garblings, the other 14 direct base decryptions of rank four, input parsing, table construction, tape routing and code lengths. Add fields only when not already counted by the lower-bound ledger. The WE correctness wrapper also checks the original witness against phi if it promises the exact gated value on invalid witnesses. The remaining width, security-reduction and clock inequalities of the private FE backend are open. Neither the strict 2^32 optimization target nor the registered 2^100 cap has been certified for arbitrary circuits.

**Executable reference.** Run the following as Python 3. The example fixtures are public. No cryptographic setup or secret key enters the compiler.

~~~python
from itertools import product, combinations
class Limit(Exception): pass
class Terms:
    def __init__(self, front):
        self.front={w:i+2 for i,w in enumerate(front)}
        self.base=2+len(front);self.args=[];self.cache={}
    def both(self,a,b):
        if a==-1 or b==-1 or a==-b:return -1
        if a==1 or a==b:return b
        if b==1:return a
        k=tuple(sorted((a,b)))
        if k not in self.cache:
            self.cache[k]=self.base+len(self.args);self.args.append(k)
        return self.cache[k]
    def emit(self,z):
        n=len(self.front); g=[]; memo={1:0,**{a:a-1 for a in self.front.values()}}
        def ng(x,y):
            g.append((x,y));return n+len(g)
        todo=[(z,False)]
        while todo:
            r,ready=todo.pop()
            if r in memo:continue
            if -r in memo:
                memo[r]=ng(memo[-r],memo[-r]);continue
            a,b=self.args[abs(r)-self.base]
            if not ready:
                todo.extend([(r,True),(b,False),(a,False)]);continue
            memo[-abs(r)]=ng(memo[a],memo[b])
            if r>0:memo[r]=ng(memo[-r],memo[-r])
        out=memo[z]
        if not g or out!=n+len(g):
            inv=ng(out,out);ng(inv,inv)
        return g
def norm(n,g):
    return [(a if a<n+1+i else 0,b if b<n+1+i else 0) for i,(a,b) in enumerate(g)]
def cone(n,g):
    live={n+len(g)}
    for i in reversed(range(len(g))):
        if n+1+i in live:live.update(g[i])
    return live
def compile_(n,raw,U,order,W=9,tablecap=1000000):
    g=norm(n,raw);live=cone(n,g)
    P=[i for i in range(1,n+1) if i not in U];d=Terms(P)
    common={0:1,**d.front}
    for i,(a,b) in enumerate(g):
        y=n+i+1
        if y in live and a in common and b in common:common[y]=-d.both(common[a],common[b])
    exists=((set(U)|set(range(n+1,n+1+len(g))))&live)-set(common)
    if len(order)!=len(set(order)) or set(order)&exists!=exists:raise ValueError('incomplete order')
    fs=[]; stats=[0,0,0,0] # max joined scope, initial+produced cells, sliced assignments, joined factor reads
    def charge(k):
        if stats[1]+k>tablecap:raise Limit(('cells',stats[1],k))
        stats[1]+=k
    for i,(a,b) in enumerate(g):
        y=n+1+i
        if y not in live or y in common:continue
        s=tuple(sorted({a,b,y}&exists));charge(1<<len(s));vals=[]
        for mask in range(1<<len(s)):
            def read(x):
                if x in common:return common[x]
                return 1 if mask>>s.index(x)&1 else -1
            both=d.both(read(a),read(b))
            vals.append(-both if read(y)==1 else both)
        fs.append((s,vals))
    out=n+len(g)
    fs.append(((),[common[out]]) if out in common else ((out,),[-1,1]));charge(len(fs[-1][1]))
    for v in order:
        if v not in exists:continue
        take=[f for f in fs if v in f[0]]
        if not take:continue
        fs=[f for f in fs if v not in f[0]]
        s=(v,)+tuple(sorted(set().union(*(set(f[0]) for f in take))-{v}));k=len(s)
        stats[0]=max(stats[0],k)
        if k>W:raise Limit(('width',v,k,stats))
        charge(1<<(k-1));stat=[]
        pos=[[s.index(x) for x in f[0]] for f in take]
        for a in range(1<<k):
            r=1
            for (_,vals),pp in zip(take,pos):
                ix=sum(((a>>j)&1)<<i for i,j in enumerate(pp))
                r=d.both(r,vals[ix])
            if a&1:stat.append(-d.both(-lo,-r))
            else:lo=r
        stats[2]+=1<<k;stats[3]+=len(take)*(1<<k)
        fs.append((s[1:],stat))
    z=1
    for s,vals in fs:
        assert not s;z=d.both(z,vals[0])
    return d.emit(z),stats,len(d.args),len(live)
def run(n,g,x):
    w=[True]+list(x)
    for a,b in g:w.append(not ((w[a] if a<len(w) else True) and (w[b] if b<len(w) else True)))
    return w[-1]
def series(n,tail,pre=0,front=1):
    # p AND product_i(u_i OR p2). The independent tail bits always extend p.
    g=[];order=[];acc=front
    def ng(a,b):g.append((a,b));return n+len(g)
    if (len(tail)+pre)%2:ng(0,0) # dead parity padding for an even number of final inversions
    for i in range(pre):acc=ng(acc,1+(7*i+3)%60)
    for u in tail:
        a=ng(u,u);b=ng(2,2);r=ng(a,b);z=ng(acc,r);nxt=ng(z,z)
        order.extend([u,a,b,r])
        if acc>n:order.append(acc)
        order.append(z);acc=nxt
    while len(g)<4096:
        prev=acc;acc=ng(acc,acc)
        if prev>n:order.append(prev)
    order.append(acc); return g,order
def lastuse(n,raw,U):
    g=norm(n,raw);live=cone(n,g)
    expiry={v:0 for v in live if v in U or v>n}
    for i,(a,b) in enumerate(g):
        y=n+i+1
        if y not in live:continue
        expiry[y]=max(expiry[y],i)
        for x in (a,b):
            if x in expiry:expiry[x]=max(expiry[x],i)
    expiry[n+len(g)]=len(g)
    return sorted(expiry,key=lambda v:(expiry[v],v))
def cliques(n):
    g=[];acc=0
    def ng(a,b):g.append((a,b));return n+len(g)
    for j in range(6):
        group=[i for i in range(1,n+1) if (i-1)%6==j]
        for a,b in combinations(group,2):
            q=ng(a,b);z=ng(acc,q);acc=ng(z,z)
    while len(g)<4096:acc=ng(acc,acc)
    return g
def support_copy(n,raw,U):
    g=norm(n,raw);live=cone(n,g);P=[i for i in range(1,n+1) if i not in U];d=Terms(P)
    tables={0:((),[1])}
    for i in live & set(range(1,n+1)):
        tables[i]=((i,),[-1,1]) if i in U else ((),[d.front[i]])
    for idx,(a,b) in enumerate(g):
        y=n+idx+1
        if y not in live:continue
        sa,ta=tables[a];sb,tb=tables[b];s=tuple(sorted(set(sa)|set(sb)))
        def at(m,sub,vals):
            k=sum(((m>>s.index(v))&1)<<j for j,v in enumerate(sub));return vals[k]
        tables[y]=(s,[-d.both(at(m,sa,ta),at(m,sb,tb)) for m in range(1<<len(s))])
    root=-1
    for v in tables[n+len(g)][1]:root=-d.both(-root,-v)
    return d.emit(root)

if __name__=='__main__':
    for gates in product(product(range(5),repeat=2),repeat=2):
        U={2};proj,*_=compile_(2,gates,U,[2,3,4])
        cp=support_copy(2,gates,U)
        for p in (0,1):
            assert run(1,cp,[p])==run(1,proj,[p])
            assert run(1,proj,[p])==any(run(2,gates,[p,t]) for t in (0,1))
    for k in (12,13,64):
        U=set(range(129-k,129));g,o=series(128,sorted(U))
        pr,st,created,live=compile_(128,g,U,lastuse(128,g,U))
        print('series',k,len(pr),pr[:4],st,created,live,sum(4*a+2*b+3 for a,b in g),sum(4*a+2*b+3 for a,b in pr))
    U=set(range(116,129));g,_=series(128,sorted(U),pre=500)
    pr,st,created,live=compile_(128,g,U,lastuse(128,g,U));print('preamble',len(pr),st,created,live)
    for k in (12,13,64):
        U=set(range(129-k,129));g,_=series(128,sorted(U));live=cone(128,g)
        masks=[0]+[int(i in U)<<(i-1) for i in range(1,129)]
        for a,b in g:masks.append(masks[a]|masks[b])
        print('support',k,sum(1<<masks[y].bit_count() for y in live if y>128))
    g=cliques(128);U=set(range(65,129))
    try:compile_(128,g,U,lastuse(128,g,U))
    except Limit as e:print('cliques',e.args)

~~~
