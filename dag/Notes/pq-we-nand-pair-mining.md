---
title: Extracting small witness alphabets directly from arbitrary NAND lists
refs: [definition:WE_CircuitSAT]
tags: [circuit-sat, witness-encryption]
---

PR #75 uses certified conflicts to encode witnesses. Here the encryptor takes only the registered gate list, with no graph, source-language tags or monotonicity premise. It discovers both signed and unsigned two-input relations. An acceptance-preserving compiler changes the search alphabet for the exact one-bit encryptor or for split-witness ABE (#64). Public computation depends only on the statement.

**Algorithm.** Number the constant true wire zero, followed by inputs and gate outputs. Replace each forward read by zero at that gate. Forward-propagate exact truth tables on supports of at most two original inputs, with an additional unknown value. Compute NAND pointwise on the union of supports if it fits; remove inessential coordinates. Return unknown on overflow and allow the constant-false operand simplification even beside an unknown. In reverse gate order start by requiring the output to be true (constant true for an empty list). A required false NAND forces both operands true. A required true self-NAND forces its operand false, and a true NAND with one known-true operand forces the other false. Conflicting demands certify UNSAT. Whenever a demanded wire has a known table, intersect its allowed input tuples into the table for that support; an empty intersection certifies UNSAT. These rules can miss constraints and contradictions.

Take forced singleton coordinates and greedily select disjoint remaining pairs with the smallest surviving alphabets first. Single unpaired coordinates use radix two. If the accepted alphabets have sizes d_i, their Cartesian product has M=product d_i elements. Rank and unrank in mixed radix; reject every code outside [0,M). Efficient conversion preserves the *given* satisfying witness, including for nonmonotone bodies. The verifier always evaluates the original circuit on the decoded assignment. With no discovered constraints it can use the raw verifier. For a one-bit information-theoretic construction the encryptor can decide SAT by scanning at most M decoded assignments. For split ABE it can assign whole groups to the two tables and compile their public decoding into the policy. No new hardness premise arises from this compiler; the lattice ABE itself needs a suitable quantum security reduction and explicit parameters.

**Soundness.** Induction in gate order proves every known wire table equals the evaluator on every assignment; replacing forward reads agrees with its default-true rule. Fix any accepting assignment. Induction in reverse order proves every demanded wire has the required value on it, since every predecessor follows from one of the NAND identities above. Therefore all intersected tables retain the assignment's tuple. Conflicting wire demands or an empty table exclude every accepting assignment. Removing overlapping constraints only enlarges the set that can be decoded. Disjoint groups give a bijection with their Cartesian product by ordinary division with remainder. Together these prove both directions of existence and conversion of every accepting witness. This is a mathematical argument with exhaustive differential tests; a registered Lean proof of this compiler and a clocked machine are open.

**Cost.** On a word RAM with indexed gates, the two passes take O(n+s) operations and storage, using constant-size tables; with dictionary lookups this is an expected-time implementation. Sorting p distinct pairs adds O(p log p) comparisons. Counts and ranks use at most n+1 bits. The Python timings below exclude parsing the unary wire encoding, running the original circuit, ABE, rank conversion, and policy compilation. They include group selection. They are medians of eleven local calls. They do not certify the registered machine cost. The reference uses Python integers and dictionaries.

**Full-size controls.** Each guard joins 64 disjoint rail pairs to a seeded 218-clause body, with 128 inputs and 4,096 NAND gates. The exactly-one variant additionally requires at least one rail in each pair; this strengthens the *input circuit*. The miner is identical on both. The source body does not need to be identified by the miner. In the UNSAT controls all eight possible sign patterns on three source variables appear as clauses, excluding all total assignments (and partial rail assignments cannot restore satisfiability). The miner still returns a compressed verifier on those controls; the residual body must reject. The final row is one unguided seeded circuit, not a distributional lower bound.

| Gate list | Pairs extracted | Code bits | Local milliseconds (approx.) |
|---|---:|---:|---:|
| At most one, SAT / UNSAT | 64 / 64 | 102 / 102 | 6 / 6 |
| Exactly one, SAT / UNSAT | 64 / 64 | 64 / 64 | 6 / 6 |
| Random distinct earlier parents | 0 | 128 | 1.4 |

In the first family M=3^64. Assigning 32 ternary groups to either table gives exactly 3^32 entries in each. In the second M=2^64, hence 2^32 entries in each. In that case each decoded coordinate is just a bit, its complement, or a constant. Substituting these literals and applying structural hashing, constants, complement cancellation and output reachability gives **651 reachable binary AND nodes** on the planted verifier, compared with **907** using the same optimizer on its uncompressed 128-bit inputs. Complemented edges are free in this AIG metric. This comparison controls for padding removal; it is not a NAND count, a lattice ciphertext measurement, or a speed comparison with a 64-variable source formula. We compared both optimized evaluators with the emitted NAND list on the planted code and 1,000 seeded codes.

**Reproduction.** Standalone Python 3. The small tests cover every two-input two-gate list including forward reads, and 400 additional seeded circuits including empty lists. They verify containment of all accepted inputs, exact round trips, and sound rejection when the extractor declares contradiction.

~~~python
from itertools import product
from math import prod
from random import Random
from statistics import median
from time import perf_counter

# None means unknown function; otherwise bits are indexed little-endian on support.
def combine(f,g):
    if f is None or g is None:
        return ((),1) if ((),0) in (f,g) else None
    s=tuple(sorted(set(f[0])|set(g[0])))
    if len(s)>2:return None
    def at(h,x):
        j=sum(((x>>s.index(v))&1)<<i for i,v in enumerate(h[0]))
        return h[1]>>j&1
    t=sum((1-(at(f,x)&at(g,x)))<<x for x in range(1<<len(s)))
    for i in reversed(range(len(s))):
        if all(((t>>x)^(t>>(x^(1<<i))))&1==0 for x in range(1<<len(s))):
            keep=[x for x in range(1<<len(s)) if not x&(1<<i)]
            t=sum(((t>>x)&1)<<j for j,x in enumerate(keep))
            s=s[:i]+s[i+1:]
    return s,t

def mine(n,gates):
    funcs=[((),1)]+[((i,),2) for i in range(n)]
    edges=[]
    for a,b in gates:
        a=a if a<len(funcs) else 0
        b=b if b<len(funcs) else 0
        edges.append((a,b))
        funcs.append(combine(funcs[a],funcs[b]))
    out=n+len(gates) if gates else 0
    need={out:1}
    domains={}
    def require(v,val):
        if need.setdefault(v,val)!=val:raise ValueError
    for v in reversed(range(len(funcs))):
        if v not in need:continue
        y=need[v]
        if funcs[v] is not None:
            s,t=funcs[v]
            full=(1<<(1<<len(s)))-1
            allowed=domains.get(s,full)&(t if y else full^t)
            if not allowed:raise ValueError
            domains[s]=allowed
        if v<=n:continue
        a,b=edges[v-n-1]
        if not y:
            require(a,1)
            require(b,1)
        elif a==b:require(a,0)
        else:
            if funcs[a]==((),1):require(b,0)
            if funcs[b]==((),1):require(a,0)
    fixed={s[0]: (0 if t==1 else 1) for s,t in domains.items() if len(s)==1 and t!=3}
    free=set(range(n))-fixed.keys()
    groups=[]
    for s,t in sorted(domains.items(), key=lambda item:(item[1].bit_count(),item[0])):
        if len(s)!=2 or t==15 or not free.issuperset(s):continue
        groups.append((s,[k for k in range(4) if t>>k&1]))
        free.difference_update(s)
    return groups+[((i,),[0,1]) for i in sorted(free)],fixed

def rank(groups,x):
    c=0
    for s,values in reversed(groups):
        v=sum((x>>i&1)<<j for j,i in enumerate(s))
        c=c*len(values)+values.index(v)
    return c

def unrank(groups,fixed,c):
    x=sum(v<<i for i,v in fixed.items())
    for s,values in groups:
        c,j=divmod(c,len(values))
        for k,i in enumerate(s):x|=(values[j]>>k&1)<<i
    if c:raise ValueError
    return x

def evaluate(n,g,x):
    w=[1]+[x>>i&1 for i in range(n)]
    for a,b in g:w.append(1-((w[a] if a<len(w) else 1)&(w[b] if b<len(w) else 1)))
    return w[-1] if g else 1

def check(n,g):
    accepts={x for x in range(1<<n) if evaluate(n,g,x)}
    try:groups,fixed=mine(n,g)
    except ValueError:
        assert not accepts
        return
    size=prod(len(v) for _,v in groups)
    dec={unrank(groups,fixed,c) for c in range(size)}
    assert len(dec)==size and accepts<=dec
    for x in dec:assert unrank(groups,fixed,rank(groups,x))==x

for a,b,c,d in product(range(5),repeat=4):check(2,[(a,b),(c,d)])
rng=Random(790)
for _ in range(400):
    n=rng.randrange(7);s=rng.randrange(12)
    check(n,[(rng.randrange(n+s+1),rng.randrange(n+s+1)) for _ in range(s)])
print('625 exhaustive, 400 seeded circuits')

from itertools import product
from random import Random

def compile_rails(clauses, exact):
    gates = []
    def nand(a, b):
        gates.append((a, b))
        return 128 + len(gates)
    def both(a, b):
        t = nand(a, b)
        return nand(t, t)
    def either(a, b):
        return nand(nand(a, a), nand(b, b))
    def reduce_tree(items, op):
        while len(items) > 1:
            items = [op(items[i], items[i+1]) if i+1<len(items) else items[i]
                     for i in range(0,len(items),2)]
        return items[0]
    guards=[nand(2*i+1,2*i+2) for i in range(64)]
    if exact:
        guards += [either(2*i+1,2*i+2) for i in range(64)]
    guard=reduce_tree(guards,both)
    body = reduce_tree([reduce_tree(c, either) for c in clauses], both)
    used = len(gates)+2
    gates.extend([(0,0)]*(4096-used))
    both(guard, body)
    return used,gates

rng=Random(2971)
codes=[rng.getrandbits(64) for _ in range(201)]
def rails(c):return sum(1<<(2*i+(c>>i&1)) for i in range(64))
def clause():
    vs=rng.sample(range(64),3)
    terms=[2*i+1+rng.randrange(2) for i in vs]
    if not any(rails(codes[0])>>(v-1)&1 for v in terms):
        terms[0]=2*vs[0]+1+((codes[0]>>vs[0])&1)
    return terms
base=[clause() for _ in range(218)]

def report(name,g,w=None):
    times=[]
    for _ in range(11):
        start=perf_counter()
        groups,fixed=mine(128,g)
        times.append(1000*(perf_counter()-start))
    size=prod(len(vals) for _,vals in groups)
    if w is not None:
        assert evaluate(128,g,w) and unrank(groups,fixed,rank(groups,w))==w
    print(name,len(g),sum(len(s)==2 for s,_ in groups),(size-1).bit_length(),round(median(times),2))

for exact in (False,True):
    _,g=compile_rails(base,exact)
    report('exactly-one' if exact else 'at-most-one',g,rails(codes[0]))
    cs=list(base)
    cs[:8]=[[2*i+1+t for i,t in enumerate(bits)] for bits in product(range(2),repeat=3)]
    _,g=compile_rails(cs,exact)
    report('UNSAT control',g)
rng=Random(79)
g=[tuple(rng.sample(range(128+i+1),2)) for i in range(4096)]
report('random earlier parents',g)

# Compile a public affine literal substitution into an AND-inverter DAG.
# Use signed node identifiers. Node 1 is true. Only output-reachable ANDs count.
def aig(n,g,inputs):
    out=1
    wires=[1]+inputs
    nodes={}
    intern={}
    base=max([1]+[abs(v) for v in inputs])
    for a,b in g:
        a=wires[a] if a<len(wires) else 1
        b=wires[b] if b<len(wires) else 1
        if -1 in (a,b) or a==-b:t=-1
        elif a==1:t=b
        elif b==1 or a==b:t=a
        else:
            k=tuple(sorted((a,b)))
            if k not in intern:
                fresh=base+len(nodes)+1
                nodes[fresh]=k
                intern[k]=fresh
            t=intern[k]
        out=-t
        wires.append(out)
    active=set()
    queue=[abs(out)]
    while queue:
        t=queue.pop()
        if t in nodes and t not in active:
            active.add(t)
            queue.extend(abs(v) for v in nodes[t])
    return out,{i:nodes[i] for i in sorted(active)}

def literal_inputs(groups,n):
    xs=[0]*n
    for j,(s,vs) in enumerate(groups):
        assert len(vs)==2
        for k,i in enumerate(s):
            a,b=[v>>k&1 for v in vs]
            xs[i]=(1 if a else -1) if a==b else (j+2)*(-1 if a else 1)
    return xs

def run_aig(out,nodes,z):
    vals={1:1}
    def at(v):
        i=abs(v)
        return (vals[i] if i in vals else z>>(i-2)&1) ^ (v<0)
    for i,(a,b) in nodes.items():vals[i]=at(a)&at(b)
    return at(out)

_,g=compile_rails(base,True)
gs,fixed=mine(128,g)
assert not fixed
raw=aig(128,g,list(range(2,130)))
short=aig(128,g,literal_inputs(gs,128))
for z in [rank(gs,rails(codes[0]))]+[rng.getrandbits(64) for _ in range(1000)]:
    x=unrank(gs,fixed,z)
    assert run_aig(*short,z)==run_aig(*raw,x)==evaluate(128,g,x)
print('reachable ANDs, raw and compressed',len(raw[1]),len(short[1]))
~~~
