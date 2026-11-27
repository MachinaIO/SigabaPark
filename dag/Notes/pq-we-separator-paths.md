---
title: Composing witness encryption across circuit separators with one-bit edge ciphertexts
refs: [definition:WE_CircuitSAT, theorem:AdvancedEncryption.WE.Separator.cut_flip, theorem:AdvancedEncryption.WE.Separator.functional_sink]
tags: [witness-encryption, circuit-sat, composition, complexity]
---

**Goal.** Replace encryption to a large verification circuit by encryption to smaller circuits, while allowing the same boundary value to be used by two adjacent pieces. This avoids listing all joint boundary assignments. The ciphertext is classical, has no setup, and the original witness determines the decryption path. Three composition rules trade local one-bit encryptions against each other. The first two inherit the local WE assumption. The third also uses a quantum-secure classical pseudorandom generator (PRG). The graph-difference sharing primitive is the familiar linear secret-sharing scheme for undirected connectivity. The use here concerns the directed witness-consistency interface, its certified cases, the choice of expression, and the explicit leaf reductions. For context on the distinction for general graphs see [Beimel and Pitassi, On Linear Secret Sharing for Connectivity in Directed Graphs](https://www.cs.bgu.ac.il/~beimel/Papers/BP.pdf).

**Circuit interface.** Partition the gate list of a NAND circuit into H nonempty consecutive bags. Boundaries and choices of algorithm depend on the public statement and parameters only. For each wire take the interval from the first bag defining or using it to the last bag using or defining it. Ignore constant-true reads, including reads of unavailable gates at their use site. The separator at a cut contains precisely the wires whose intervals cross that cut. In particular a variable shared by two distant bags travels across every intermediate cut. The exterior boundaries have one state each. Handle a circuit with no gates directly as true. At bag i and endpoint assignments a,b, form a local statement: the incoming boundary has value a, any wire in both boundaries agrees, newly occurring primary inputs on the outgoing boundary have the values in b, and computing the gates produces the required outgoing values. The last bag additionally requires the original output to be true. Its local witness consists of the other primary inputs used in the bag. Convert the check to NAND gates, hardwiring endpoints, comparing wires and taking the conjunction; size is polynomial in the bag and boundary descriptions. Stable numbering and bit packing are public. Witness evaluation of the original program produces a path and a local witness for every edge. Conversely, a path of satisfiable edges supplies a single consistent value for each shared variable by the interval property. Gluing its private local inputs and inducting over the gates yields an accepting original witness.

Let D_i denote the size of separator i, D_0=D_H=1. There are E=sum_i D_i D_(i+1) candidate transitions. An edge is live if its local statement admits a witness. The live graph has a directed s-to-t path exactly on YES. Enc never needs its live flags for cryptographic modes. Impose a polynomial public bound before allocating any D_i states. A boundary exceeding the budget can be omitted by merging bags. One bag always suffices with a general leaf backend. Count the time to parse and select cuts and build all requested statements. A bounded public decision pass may enumerate the private inputs when cheap, propagate reachable boundary states, and stop on budget exhaustion. A completed decision pass can output the bit masked by the YES flag and Dec can return the ciphertext bit. This gives an unconditional public shortcut for those instances.

**One-bit potentials.** For an undirected two-terminal network of leaf statements, choose independent uniform vertex bits p. Publish p_s, b xor p_t, and an independent WE encryption under each edge statement of the difference p_u xor p_v. Along a witness path Dec adds the differences and the two public bits. On a NO with s and t disconnected in the live undirected graph, fix any cut that separates them without crossing a live edge. Flipping all vertex bits on the target side is an involution on the encryption coins. It preserves both public bits when the message changes, and all edge plaintexts outside the cut. This is the first formal theorem. Hybridize only the crossing edges, each false, using one one-bit challenge per hybrid. If the simulated difference requires reversing the challenge orientation, complement the adversary output in that branch. The sum of the absolute leaf advantages bounds the composed advantage. For a fixed false statement the cut may be nonuniform advice; include its encoding, the simulator and all auxiliary encryption work in concrete costs. Correctness along a path of H edges costs at most H times the maximum single-leaf decryption error. Edge labels may repeat as statements; encrypt each occurrence with fresh randomness.

*Functional transitions.* The original layered graph can itself be used if the true transition relation has at most one successor per vertex. The target is a sink. Directed reachability of that sink is invariant across every live edge: a path beginning at a nontarget vertex with an outgoing edge must use its unique successor. The invariant also holds in reverse across the edge. Thus undirected connectivity to t implies directed reachability, as proved by the second formal theorem. Reversing the graph gives the corresponding predecessor rule at a source. Functionality is a statement about all local witnesses at the same incoming state. A syntactic sufficient certificate computes every outgoing bit from incoming wires and constants through the defining NANDs of the bag. Extra conditions on private inputs can still make an edge false. A bounded, checked refutation of two simultaneous valid transitions with the same incoming and different outgoing values also suffices. When using this mode require evidence independent of the secret live flags; a failed certification leaves the other modes available. There are E independent one-bit ciphertexts and H leaf decryptions. On unrestricted graphs the rule is unsound: among all 4096 subgraphs at widths (1,2,2,2,1), undirected connectivity falsely accepts 80. It agrees on all 972 forward-functional subgraphs.

*Arbitrary transitions by a formula.* For endpoints a,b of an interval [i,j], split at k. Put the D_k alternatives in parallel. Alternative d is the series composition of independent copies of the networks for (i,k,a,d) and (k,j,d,b), meeting at a fresh vertex. Distinct parallel alternatives share only their two terminals. An undirected simple path through this network chooses one alternative and traverses both of its series components. Induction proves equivalence to the original directed path condition for every assignment of leaf truth values. Repeated subproblems need distinct internal vertices in different occurrences. A true witness selects its known midpoint states recursively, using one leaf per bag, so Dec does not try every alternative.

For unit leaf costs, a subproblem spanning one bag costs 1. For larger intervals choose k minimizing D_k times the sum of its two subinterval costs. This dynamic program uses O(H³) arithmetic operations and O(H²) entries; saturate all costs at budget+1 before expanding the selected expression. For endpoint-specific positive costs use the corresponding sum over d with endpoint-specific subcosts. When D_i<=W for fixed W, balanced splitting gives at most (2W)^ceil(log2 H) leaves, polynomial in H. Growing W requires a size guard. At H=64 with all internal widths two, the cost is 4096 leaf encryptions versus 2^63 entire boundary strings. With one width 32 at cut 32 and width two elsewhere, balanced splitting takes 65536 calls; cost-based splitting takes 5344. At periodic widths 16 on multiples of 8, 1 on remaining multiples of 5, and 2 elsewhere, these counts are 1441792 and 1024. The program independently exhausts binary split trees on 81 small profiles to check the optimizer and saturation.

**Arbitrary directed transitions with one label per state.** To avoid formula blowup when E is moderate, choose an independent k-bit key K_v per state. Publicly release K_s. Expand K_u into one distinct k-bit pad per outgoing edge, using fresh slots of a secure length-expanding PRG. For each e=(u,v) publish a local WE encryption of K_v xor pad_e, bitwise with independent randomness if the backend accepts only bits. Publish the message xor one fresh output bit expanded from K_t. A recipient with an accepting witness follows the directed path, derives its current pad, decrypts the local payload and obtains the next key. This binds honest continuation to the selected boundary state. Security on a false statement follows from the next hybrid argument.

Fix the set R of reachable states. For each edge from R to its complement, replace its k encrypted payload bits by encryptions of zero; the edge statement is false. Now visit unreachable states in topological order, replacing each state's full expansion by independent uniform pad bits. For the switch at u, incoming ciphertexts from R no longer involve K_u. Incoming edges from earlier unreachable states already had independent random pads in their own slots. Reparametrize their masked plaintexts as independent uniform words; their joint distribution is independent of K_u, including correlations with every other published item because none of those pad slots is reused. The challenger can therefore supply a single generator challenge word for the outgoing expansion without revealing its seed. At the target the message mask becomes a fresh independent bit. Across both message experiments the security loss is at most twice the sum of the k times crossing-edge leaf advantages and the one-sample generator advantages over unreachable states. Advice and auxiliary work must again be counted. Classical challenge samples suffice for the hybrids with quantum distinguishers if both primitives are secure for that adversary model. The test's SHAKE implementation is only an executable interface example. A length-doubling generator can fill a binary tree truncated to a public power-of-two output capacity, with linear hybrid loss in the number of internal expansions. A path recipient can derive a single slot in logarithmic depth. No quantum oracle interface is required.

The directed mode uses kE independent one-bit leaf encryptions, kH selected decryptions and k+1 clear header bits before framing; correctness costs at most kH times the leaf error. At H=64, uniform width eight, k=128, it uses 509952 leaf encryptions versus 16777216 from midpoint expansion. The functional mode would take 3984 but requires its certificate. With constant or polynomial caps on E, emitted formula size, partition search, and private decision work, ciphertext length, Enc time, and Dec time are all polynomial in the statement length and security parameter whenever the leaf backend has those three bounds. For example, for the directed mode add k times the sum of single-edge ciphertext lengths, k times the sum of their encryption costs, and k times the sum of the selected leaf decryption costs to the respective framing, label generation and traversal budgets. Sequential access can scan the full ciphertext in polynomial time. Set leaf accuracy using the number of decryptions on one path, and security using the actual reductions. If measured costs favor a single monolithic invocation, the compiler can choose it from the outset. These counts quantify how many *smaller* problems are encrypted. They do not imply a byte or time speedup without leaf parameters. The general polynomial benchmark of [PR 99](https://github.com/MachinaIO/SigabaPark/pull/99) still relies on the VWW assumptions. An arbitrary NP leaf with polynomial costs and a quantum proof under the submitted registry remains open.

**Controls and reproduction.** The first Python listing checks all 4096 transition patterns, checks equality of the entire ciphertext histograms on 29 small NO instances, and runs both payload bits through 28 formula-path and 250 directed-label decryptions counting individual decryptions. The toy leaf evaluates its small witness set directly. The second listing verifies the NAND reduction on 1308 original witness traces, including forward reads. Two 128-input/4096-gate controls have 64 bags with at most one boundary wire and two private primary bits per bag. The public decision pass completes after 630 and 319 local evaluations respectively. The NO control forces the first bag output false and propagates conjunction to the required true final output. Each bag has some local satisfying entry; the boundary consistency matters. These controls should use the public decision shortcut. Their runtime does not measure full lattice encryption. The third listing reproduces the profile counts.

~~~python
"""Witness-table composition. Full edge truth is used only in tests and the toy leaf WE."""
from itertools import product
from collections import Counter
from random import Random

def edges(sizes):
    return [(i,a,b) for i,(l,r) in enumerate(zip(sizes,sizes[1:]))
            for a in range(l) for b in range(r)]

def direct(sizes):
    return [((i,a),(i+1,b),(i,a,b)) for i,a,b in edges(sizes)],(0,0),(len(sizes)-1,0)

def expand(sizes,split=None):
    # Independent occurrence of every recursive subproblem. Series components
    # share a single junction; parallel components share just their two terminals.
    wires=[];fresh=2
    def build(i,j,a,b,s,t):
        nonlocal fresh
        if j==i+1:
            wires.append((s,t,(i,a,b)))
            return
        k=split[i,j] if split is not None else (i+j)//2
        for d in range(sizes[k]):
            v=fresh;fresh+=1
            build(i,k,a,d,s,v);build(k,j,d,b,v,t)
    build(0,len(sizes)-1,0,0,0,1)
    return wires,0,1

def reachable(graph,truth,undirected):
    es,s,t=graph;seen={s}
    while True:
        old=len(seen)
        for u,v,key in es:
            if key not in truth:continue
            if u in seen:seen.add(v)
            if undirected and v in seen:seen.add(u)
        if len(seen)==old:return t in seen

def witness_path(graph,states):
    es,s,t=graph;verts={s:[]}
    # Edge ordering is topological on directed s-t paths for both compilers.
    for j,(u,v,(i,a,b)) in enumerate(es):
        if u in verts and (a,b)==tuple(states[i:i+2]):verts[v]=verts[u]+[j]
    return verts.get(t)

def toy_encrypt(graph,atoms,msg,p):
    es,s,t=graph
    # atoms[key] contains its local witnesses. Its emptiness is decidable by the toy leaf.
    return (p[s],p[t]^msg,tuple((p[u]^p[v]) if atoms[key] else 0 for u,v,key in es))

def decrypt(graph,ct,states,local,atoms):
    path=witness_path(graph,states)
    if path is None:return None
    bit=ct[0]^ct[1]
    for j in path:
        key=graph[0][j][2];i=key[0]
        if local[i] not in atoms[key]:return None
        bit^=ct[2][j]
    return bit

def test():
    sizes=(1,2,2,2,1);es=edges(sizes);naive=direct(sizes);safe=expand(sizes)
    invalid=0;functional=0;checks=0
    for mask in range(1<<len(es)):
        truth={e for j,e in enumerate(es) if mask>>j&1}
        yes=reachable(naive,truth,False)
        assert reachable(safe,truth,True)==yes
        und=reachable(naive,truth,True)
        invalid+=und and not yes
        if len({(i,a) for i,a,b in truth})==len(truth):
            assert und==yes;functional+=1
        checks+=1
    print('subgraphs, unsafe false positives, functional subgraphs:',checks,invalid,functional)

    sizes=(1,2,2,1);es=edges(sizes);graph=expand(sizes)
    vertices=sorted({v for s,t,e in graph[0] for v in (s,t)})
    rng=Random(650);histchecks=0;dec=0
    for _ in range(40):
        atoms={e:{i for i in range(3) if rng.randrange(5)==0} for e in es}
        truth={k for k,v in atoms.items() if v}
        p={v:rng.randrange(2) for v in vertices}
        if reachable(graph,truth,True):
            for a,b in product(range(2),repeat=2):
                states=(0,a,b,0);keys=[(i,*states[i:i+2]) for i in range(3)]
                if all(atoms[k] for k in keys):
                    wit=[min(atoms[k]) for k in keys]
                    for bit in (0,1):
                        assert decrypt(graph,toy_encrypt(graph,atoms,bit,p),states,wit,atoms)==bit;dec+=1
        else:
            bins=[Counter(),Counter()]
            for vals in product((0,1),repeat=len(vertices)):
                p=dict(zip(vertices,vals))
                for bit in (0,1):bins[bit][toy_encrypt(graph,atoms,bit,p)]+=1
            assert bins[0]==bins[1];histchecks+=1
    print('identical full NO histograms, valid decryptions:',histchecks,dec)
    for h in (8,16,64):
        sizes=(1,)+(2,)*(h-1)+(1,)
        print('bags / all boundary strings / formula edge calls / functional edge calls:',
              h,2**(h-1),len(expand(sizes)[0]),len(edges(sizes)))
if __name__=='__main__':test()

def directed_toy(sizes,atoms,bit,length,rng,states=None,local=None):
    from hashlib import shake_256
    # Distinct slots of a single publicly evaluable expander per source.
    def expandkey(k,d):
        s=shake_256(b'path-test'+k).digest(length*d)
        return [int.from_bytes(s[i*length:(i+1)*length],'big') for i in range(d)]
    keys={(i,a):rng.randbytes(length) for i,d in enumerate(sizes) for a in range(d)}
    table={}
    for i,d in enumerate(sizes[1:]):
        for a in range(sizes[i]):
            pads=expandkey(keys[i,a],d)
            for b in range(d):
                e=(i,a,b);payload=int.from_bytes(keys[i+1,b],'big')^pads[b]
                table[e]=payload if atoms[e] else 0
    last=len(sizes)-1
    masked=bit^(expandkey(keys[last,0],1)[0]&1)
    ct=(keys[0,0],table,masked)
    if states is None:return ct
    k=ct[0]
    for i,(a,b) in enumerate(zip(states,states[1:])):
        e=(i,a,b)
        if local[i] not in atoms[e]:return None
        k=(ct[1][e]^expandkey(k,sizes[i+1])[b]).to_bytes(length,'big')
    return ct[2]^(expandkey(k,1)[0]&1)

def directed_test():
    rng=Random(177);count=0
    for sizes in [(1,2,2,2,1),(1,3,2,4,1)]:
        for _ in range(24):
            atoms={e:{j for j in range(4) if rng.randrange(4)==0} for e in edges(sizes)}
            for states in product(*(range(d) for d in sizes)):
                path=[(i,a,b) for i,(a,b) in enumerate(zip(states,states[1:]))]
                if all(atoms[e] for e in path):
                    local=list(map(lambda e:min(atoms[e]),path))
                    for bit in (0,1):
                        assert directed_toy(sizes,atoms,bit,16,rng,states,local)==bit;count+=1
    print('directed label passing, valid decryptions:',count)
if __name__=='__main__':directed_test()
~~~

~~~python
from itertools import product
from random import Random

def schedule(n,gates,cuts):
    assert cuts[0]==0 and cuts[-1]==len(gates) and all(i<j for i,j in zip(cuts,cuts[1:]))
    norm=[tuple(a if 0<a<n+i+1 else 0 for a in g) for i,g in enumerate(gates)]
    terms=[];first={};last={}
    for i,(lo,hi) in enumerate(zip(cuts,cuts[1:])):
        scope=set()
        for j in range(lo,hi):
            scope.update(norm[j]);scope.add(n+j+1)
        scope.discard(0);terms.append(scope)
        for x in scope:first.setdefault(x,i);last[x]=i
    bd=[tuple(sorted(x for x in first if first[x]<i<=last[x])) for i in range(len(terms)+1)]
    priv=[tuple(sorted(x for x in scope if x<=n and x not in bd[i] and x not in bd[i+1])) for i,scope in enumerate(terms)]
    return norm,cuts,bd,priv

def value(plan,n,i,a,b,local):
    norm,cuts,bd,priv=plan
    d={0:1}
    for x,k in zip(bd[i],range(len(bd[i]))):d[x]=a>>k&1
    desired={x:b>>j&1 for j,x in enumerate(bd[i+1])}
    if any(x in d and d[x]!=y for x,y in desired.items()):return False
    for x,y in desired.items():
        if x<=n:d[x]=y
    for j,x in enumerate(priv[i]):d[x]=local>>j&1
    for j in range(cuts[i],cuts[i+1]):
        u,v=norm[j];d[n+j+1]=1-d[u]*d[v]
    return all(d[x]==y for x,y in desired.items()) and (
        i+2<len(cuts) or not norm or bool(d[n+len(norm)]))

def table(n,plan):
    norm,cuts,bd,priv=plan;state={0};calls=0
    for i in range(len(priv)):
        nxt=set()
        for a in state:
            for b in range(1<<len(bd[i+1])):
                for local in range(1<<len(priv[i])):
                    calls+=1
                    if value(plan,n,i,a,b,local):nxt.add(b);break
        state=nxt
    return 0 in state,calls

def run():
    rng=Random(712);checked=0
    for _ in range(100):
        n=rng.randint(1,5);g=[tuple(rng.randrange(n+j+3) for _ in range(2)) for j in range(6)]
        p=schedule(n,g,[0,2,4,6]);ok=False
        for bits in product((0,1),repeat=n):
            d=[1,*bits]
            for a,b in p[0]:d.append(1-d[a]*d[b])
            w=lambda vs:sum(d[x]<<j for j,x in enumerate(vs))
            chain=all(value(p,n,i,w(p[2][i]),w(p[2][i+1]),w(priv)) for i,priv in enumerate(p[3]))
            assert chain==bool(d[-1]);ok|=chain;checked+=1
        assert table(n,p)[0]==ok
    for no in [False,True]:
        n=128;g=[];prev=0
        def nand(a,b):
            g.append((a,b));return n+len(g)
        for i in range(64):
            a,b=2*i+1,2*i+2
            # local = NAND(a,b); maintain conjunction with the preceding bag
            v=nand(a,b)
            if no and i==0:
                nv=nand(v,v);taut=nand(v,nv);v=nand(taut,taut)
            t=nand(prev,v);prev=nand(t,t)
            # End exactly at the bag output; a dead padding gate fixes parity.
            remaining=(i+1)*64-len(g)
            if remaining%2:nand(0,0)
            for _ in range(remaining//2):
                v=nand(prev,prev);prev=nand(v,v)
        p=schedule(n,g,list(range(0,4097,64)))
        ans,calls=table(n,p)
        assert ans!=no
        print('4096 gate control','NO' if no else 'YES','max boundary, max private primaries, local evaluations',
              max(map(len,p[2])),max(map(len,p[3])),calls)
    print('original witness traces cross-checked',checked)
if __name__=='__main__':run()
~~~

~~~python
"""Uniform per-leaf cost; dimensions already capped by the caller."""
from functools import cache

def plan(D, budget):
    H=len(D)-1
    if H<1 or not all(1<=x<=budget for x in D):
        raise ValueError('invalid or oversized layout')
    cost={};split={}
    for h in range(1,H+1):
        for i in range(H+1-h):
            j=i+h
            if h==1:cost[i,j]=1;continue
            best,k=min((min(budget+1,D[k]*(cost[i,k]+cost[k,j])),k) for k in range(i+1,j))
            cost[i,j]=best;split[i,j]=k
    @cache
    def midpoint(i,j):
        if i+1==j:return 1
        k=(i+j)//2
        return D[k]*(midpoint(i,k)+midpoint(k,j))
    return cost[0,H],split,midpoint(0,H)

def test():
    for name,d in [('uniform',[1]+[2]*63+[1]),
                   ('uniform width eight',[1]+[8]*63+[1]),('alternating',[1]+[8 if i%2 else 2 for i in range(1,65)]+[1]),
                   ('wide midpoint',[1]+[32 if i==32 else 2 for i in range(1,64)]+[1]),
                   ('periodic',[1]+[16 if i%8==0 else (1 if i%5==0 else 2) for i in range(1,64)]+[1])]:
        best,sp,base=plan(d,1<<25)
        g=sum(x*y for x,y in zip(d,d[1:]))
        print(name,'bags, midpoint, planned, functional, 128-bit directed calls:',len(d)-1,base,best,g,128*g)
        assert best<=base
def audit():
    from itertools import product
    for inner in product((1,2,3),repeat=4):
        d=(1,)+inner+(1,)
        @cache
        def every(i,j):
            if i+1==j:return (1,)
            return tuple(d[k]*(a+b) for k in range(i+1,j)
                         for a in every(i,k) for b in every(k,j))
        expected=min(every(0,len(d)-1))
        assert plan(d,10000)[0]==expected
        for budget in (3,7,16):
            assert plan(d,budget)[0]==min(expected,budget+1)
    print('all binary split trees checked on 81 profiles')
if __name__=='__main__':test();audit()
~~~

**Matrix-backend crossover.** The final listing feeds the YES control and its pinned local clauses to the read-once matrix compiler of [PR 99 at 58036ab](https://github.com/MachinaIO/SigabaPark/blob/58036abbee86216e6e0bf18a4a8234c6d55d82cb/dag/Notes/pq-we-live-clause-matrix-product.md). Assign variables in first-use order. Write m=alpha*w, where w is the compiled width. With a shortened root and final block, the interior alone has 2(h-2) alpha² w² residues at h>=2. The unsplit shape is (h,w)=(4224,9), with coefficient 683964 on alpha². Composing all 64 bags by the one-bit formula gives 4096 local encryptions, shapes (65 or 66, 7 or 8), and coefficient 29227136. At equal scale this costs 42.73 times as many interior residues. If all the local encryptions share a smaller scale, the monolithic-to-local alpha ratio must exceed 6.537 before the interior-residue comparison favors this split. Grouping into 2, 4, 8, 16 and 32 bags gives break-even ratios of 1.414, 1.998, 2.821, 3.979 and 5.594 respectively (rounded). When moduli change, multiply each residue count by its actual serialization width. Endpoint blocks, framing, parameter-dependent correctness/security margins, leaf sampling and traversal clocks are additional. These are measured program dimensions and derived size thresholds, not cryptographic parameter recommendations. The real dispatcher can use the cheap exact decision on this control. For a hard leaf backend, compare fully calibrated local and monolithic costs before committing to any split.

An asymptotic interpretation uses the explicit schedule of [VWW Remark 5.1](https://eprint.iacr.org/2022/1140.pdf). Suppose a family gives B equal-size bags (B a power of two), each of matrix-program length Theta(h/B), comparable compiled width w, fixed separator state count W, and an admissible common effective security parameter lambda for both layouts including composition losses. Take n of order (h² lambda)^(1/delta), log q of order h² lambda, and the trapdoor column count of order nw log q. For a length large enough to have interior blocks, the monolithic interior bit count scales as h^(7+4/delta) w² lambda^(3+2/delta). Balanced formula composition uses B^(1+log2 W) local encryptions; substituting the local length gives a composed-to-monolithic interior-bit ratio of order B^(log2 W-6-4/delta). The ratio decreases if log2 W < 6+4/delta. Along an honest witness only B local paths are multiplied. At comparable width, the modular multiply-add count for their interior blocks is smaller by order B^(4+4/delta). Reading all ciphertexts on a sequential machine may instead dominate Dec. These exponents apply to the stated scaling family; leaf framing, root and terminal blocks, precision and noise inequalities, and full simulator clocks remain necessary for a parameterized deployment. In particular, no numerical security level follows from choosing a value of delta. A family with tiny private witnesses can also be solved by the public shortcut before any encrypted comparison.

To reproduce the last listing, save PR 99's first Python listing as frontend.py, this note's second listing as nand.py and its first as paths.py. Run python shape.py frontend.py nand.py paths.py.

~~~python
"""Compare matrix geometry at a common scale, using the frontend of PR 99."""
from collections import Counter
import runpy,sys
def geometry(front,local,paths):
    n=128;g=[];prev=0
    def nand(a,b):
        g.append((a,b));return n+len(g)
    for i in range(64):
        a,b=2*i+1,2*i+2;v=nand(a,b);tmp=nand(prev,v);prev=nand(tmp,tmp)
        nand(0,0)
        for _ in range(30):tmp=nand(prev,prev);prev=nand(tmp,tmp)
    p=local['schedule'](n,g,list(range(0,len(g)+1,64)))
    def shape(lo,hi,binding,require):
        fixed={0:1,**binding}
        clauses=[];order={}
        def put(lits):
            row=[]
            for x,y in lits:
                if x in fixed:
                    if fixed[x]==y:return
                else:row.append(order[x] if y else -order[x])
            clauses.append(tuple(row))
        for j in range(lo,hi):
            a,b=p[0][j];z=n+j+1
            for v in (a,b,z):
                if v not in order and v not in fixed:order[v]=len(order)+1
            put([(a,1),(z,1)]);put([(b,1),(z,1)])
            put([(a,0),(b,0),(z,0)])
        if require:put([(n+len(g),1)])
        pr=front['compile_program'](clauses,len(order),0)
        return len(pr[1]),len(pr[0])
    def coeff(hw):
        h,w=hw
        assert h>=2
        # If m=alpha*w the interior residue count is alpha^2 times this number.
        return 2*(h-2)*w*w
    whole=shape(0,len(g),{},True)
    print('monolithic shape and interior coefficient',whole,coeff(whole))
    for chunk in (64,128,256,512,1024,2048,4096):
        p=local['schedule'](n,g,list(range(0,len(g)+1,chunk)))
        d=tuple(1<<len(bd) for bd in p[2])
        weights=Counter(e for _,_,e in paths['expand'](d)[0])
        hist=Counter()
        for (i,a,b),multiplicity in weights.items():
            bind={x:a>>j&1 for j,x in enumerate(p[2][i])}
            right={x:b>>j&1 for j,x in enumerate(p[2][i+1])}
            assert all(x not in bind or y==bind[x] for x,y in right.items())
            bind.update(right)
            hw=shape(p[1][i],p[1][i+1],bind,i==len(p[3])-1)
            hist[hw]+=multiplicity
        real=sum(coeff(hw)*v for hw,v in hist.items())
        print('bags, calls, total interior coefficient, required scale ratio',len(d)-1,sum(hist.values()),real,round((real/coeff(whole))**0.5,3))
        if chunk==64:print('local shape histogram',dict(sorted(hist.items())))
if __name__=='__main__':geometry(*(runpy.run_path(f) for f in sys.argv[1:]))
~~~
