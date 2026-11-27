---
title: Combining fixed syndrome decoding, witness lists and hard-core masking
refs: [definition:WE_CircuitSAT, note:pq-we-broad-literature-sweep]
tags: [witness-encryption, reduction, coding, complexity]
---

**A non-lattice target.** The fixed search challenger samples a uniform binary matrix H of a prescribed shape and a uniform weight-w length-n error e, gives H,He, and accepts any weight-w preimage of He. The size-class parameters are independent of the circuit. Quantum hardness for the chosen parameters is the assumption. This is a code-based search game with an efficient win predicate. The learning perspective on WE motivates looking for a feature sampler rather than an encoded program; see [Witness Encryption and NP-Hardness of Learning](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CCC.2025.34). The following interface is a proposed approach to constructing that sampler.

Given the sampled e and H, generate public features X for the source statement. On YES, a witness algorithm using H,He,X (before any hash seeds) returns at most L distinct candidate errors and includes e with probability at least p. On NO, one needs a proof that the same features can be simulated from H,He for purposes of the joint hard-core experiment. This is a proof obligation, not an additional assumption. A sufficient but restrictive case is statistical closeness delta of the joint laws including e. The encoder, simulator and list algorithms are not supplied for general NP.

**List-to-bit conversion.** Publish H,He,X, k independent public binary inner-product tags of e (seeds and answers), and a fresh random inner-product seed with its answer masked by the message bit. Keep candidates matching all tags; if there is exactly one, use its last parity, otherwise guess an independent fair bit. Any wrong candidate collides with all k tags with probability 2^-k even conditioned on the list, since it was formed before the independent tags. Except on the event of any such collision, the decoder either recovers e or guesses. More precisely correct-unique probability is at least p-L 2^-k and wrong-unique probability is at most L 2^-k. Success is therefore at least 1/2+p/2-L 2^-k. Choose k=ceil(log2(4L/p)) for p>0,L>=1. Independent repetitions, with fresh matrices, errors, features and seeds, followed by majority yield error at most exp(-T p²/8) with T repetitions. Only logarithmically many tags are needed for polynomial lists and inverse-polynomial p.

For the simulated NO features, [Goldreich–Levin](https://www.wisdom.weizmann.ac.il/~/oded/gl.html) connects prediction of a random parity to recovering the planted e on a nonnegligible fraction of instances; a recovered e wins the fixed game regardless of syndrome collisions. The classical list-reconstruction argument can use independently restarted quantum tests on classical inputs (polynomial-size circuit descriptions, no scarce quantum advice). To handle previous tags one may hybridize the k+1 parity answers, guessing earlier true tags and using the standard signed predictor: subtract a control with the target answer independently random. Equivalently Fourier-expand a test on the k+1 answer bits: a nonzero acceptance gap against uniform gives a nonempty parity character with correlation at least the gap divided by 2^(k+1). For that subset the XOR of the corresponding public seeds is uniform. Given a parity query select the other seeds uniformly and set one selected seed to give the requested XOR. Draw independent random answer bits, run the test and weight its acceptance by the selected answer character to obtain the predictor correlation (choose the sign or try both). This pays polynomial overhead for k=O(log lambda), not for a linear number of reused tags. Independent repetition costs a further ordinary T-hybrid loss. Include feature simulation error per repetition and all simulation time. This supplies no code parameters with a claimed concrete quantum security level.

**Where the tools must meet.** Suppose one universal efficient simulator, defined on every statement, produced joint statistical distance negligible on all NO statements for the experiments including e. On YES a witness list contains e with probability p in the real joint experiment. In the simulated experiment this probability is negligible under nonuniform fixed-game hardness, since a reduction with the fixed statement and witness hardwired could generate the features, run the list and verify all candidates. Thus the two efficiently samplable labeled experiments have an inverse-polynomial statistical gap on YES and negligible gap on NO. Polynomial independent products amplify the former to a constant by counting list hits with the fixed witness; they preserve negligible NO distance. These samplers would reduce CircuitSAT to Statistical Difference and place NP in SZK. A single universally applicable statistical simulator is therefore an implausible target. The open route is a computational, potentially witness-indexed sequence of feature replacements tied to the same fixed game. In particular randomizing a code while leaving an unverified circuit-specific decoding assumption would not fill this step.

A second toolset worth contrasting is classical randomized circuit encodings and secret sharing over inconsistent assignments. The security obligation is simulation of *all* information published for mutually incompatible input choices. Ordinary single-input garbling privacy does not establish that property. Assuming full monotone-NP secret sharing as the central ingredient would also obscure what is being built: the literature explicitly constructs it from WE and one-way functions ([Secret-Sharing for NP](https://doi.org/10.1007/s00145-015-9226-0)). Neither this note nor the code route invokes iO or general functional encryption.

**Control.** Enumerate every pair of tag seeds and a fresh mask seed in four dimensions, for each planted weight-two error, with a list that sometimes omits that error. Count fair fallback guesses fractionally.
~~~python
from itertools import combinations,product
from fractions import Fraction as F
errors=[(1<<i)|(1<<j) for i,j in combinations(range(4),2)]
good=total=0
for e in errors:
    candidates=errors[:3]
    for r,s,t in product(range(16),repeat=3):
        matching=[v for v in candidates if all(((e^v)&u).bit_count()%2==0 for u in (r,s))]
        good+=1 if len(matching)!=1 else 2*int(((matching[0]^e)&t).bit_count()%2==0)
        total+=2
assert F(good,total)>F(1,2)
for e,v in combinations(errors,2):
    assert sum(all(((e^v)&u).bit_count()%2==0 for u in (r,s))
               for r,s in product(range(16),repeat=2))==64
print("exact decoding success",F(good,total),"and 15 pairwise collision checks")
~~~
