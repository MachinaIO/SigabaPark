---
title: A streamed fixed LWE-bank issuer and a reverse-counting registered witness readout
refs: [definition:WE_CircuitSAT_Capped, definition:StreamBucketBank, theorem:AdvancedEncryption.WE.StreamBank.IssuerCost, theorem:AdvancedEncryption.WE.StreamBank.ReadoutCost, theorem:AdvancedEncryption.WE.StreamBank.ClockAccount, theorem:AdvancedEncryption.WE.StreamBank.SentinelWord, theorem:AdvancedEncryption.WE.StreamBank.ShareFold, theorem:AdvancedEncryption.WE.StreamBank.ReadoutDet]
tags: [witness-encryption, machine, lwe, concrete-cost]
---

## Interface and arithmetic

The bank has 753 rows, 1024 columns, q=64, 513 training bodies, and sixteen tags with fifteen fresh source bodies per tag. The input to the three-work-tape issuer is the raw payload bit followed by 256 tag-major reachability flags. A present role prints its share; an absent role prints six zeros. Within each residue the least significant bit comes first. The output is the whole random matrix row-major, then all training bodies, then the sixteen roles in each of sixteen buckets. Each matrix bit is one fresh fair coin. A pair of independent bits defines each CBD(1) secret coordinate by subtraction, and another independent pair defines each row error. Masked-off roles still participate in the modular sum defining the sixteenth share. On an authorized tag the sixteen printed residues sum to 32β modulo 64 on every tape.

StreamBucketBank.machine replaces the earlier fixed-source issuer whose absolute instruction position, beta and accumulator were stored together in the control state. It uses the same ideal fair-coin law and field layout, although the fair coins used by a replay occur at different tick numbers. In the new machine a single linear pass of n finite states writes a row-template prefix onto the first tape and secret-length markers onto the second. The template labels are training/ordinary shares and bucket-closing flags. It expands each row to two markers and six initialized body bits on the third tape. The two secret tapes are rewound and overwritten by the two CBD bits per coordinate. The supported template range is 0 < t+15k ≤ n. Blank cells on both sides delimit loops without carrying the row index through arithmetic. The row loop has six bit-position phases times 64 accumulator states. A six-bit body is written by repeatedly shifting a seven-bit sentinel word. Work heads never pass their reserved blank at cell zero. The body tape is rewound once the matrix is complete, and the two record header bits drive training output, ordinary masked roles and final modular complements. The payload is retained on the input until the matrix is finished, then stored on the first work tape. The second tape can hold the closing-role flag during output. Arithmetic and initialization state counts add instead of multiplying.

## Cost and native replay

The registered metrics for the actual three-tape machine are 2,273 states, 5,435,863 steps, 10,310,328 description bits and total cost **15,746,191**, below 2^24. The earlier unrolled machine had 693,213,952 states, 5,415,733 steps and total cost 5,165,835,786,037. The improvement is almost entirely in the charged description. With R=t+15k, initialization takes 5n+17R+8 ticks, the R row loops take R(7n+11), and terminal rewind and release take 16R+6k+3. Counts are independent of all data and valid input bits. ClockAccount checks the sum and SentinelWord checks the six data bits and sentinel position. IssuerCost evaluates Machine.cost itself on the implemented machine. ShareFold checks the modular subtraction fold. The complete tape invariant and distributional equivalence to the registered LWE sampler are mathematical interface arguments and replay evidence here, not end-to-end theorems about Machine.run.

The full native transition replay used a deterministic 64-bit LCG with seed 251, one update per model step, replacing the fair tape for testing only. It halted on exactly 5,435,863 steps and emitted 4,631,046 raw bits, consuming one payload plus 256 flags. An independent arithmetic checker regenerated all 771,072 matrix words, 513 training bodies, and 256 masked shares. The actual YES reachability fixture omits tag i for roles i<15 and omits tag 14 for role 15. With payload one, its byte-per-bit replay digest was 051ba0496c4175303d11d5d4114452ee9d46384a359736de30af107860ca4577. An alternative diagonal-missing bitmap including an absent final share at tag 15 gave digest 0a56fcc4c30400336244bcb00e60cf4383871e01ff2864d4e04608a473c575e6. Boundary replays n=16,t=1,k=1 and n=3,t=1,k=0 also agreed, including a zero payload on the former. All unused transition coins are ignored. There are 2n+6nR+2R=4,629,986 meaningful independent coin bits at the fixed parameters. A generic probability coupling can feed the old and new machines the same subsequence of meaningful coins of each kind.

## Registered witness readout

The separate raw localDecoder accepts four big-endian tag bits followed by the raw ciphertext, and costs 5,420,940 with zero work tapes. The more useful framedDecoder starts at the registered four-frame decoder input. The parameters, gate-list statement, 128-bit witness and raw ciphertext each come in that order in encodeTuple, with each data bit framed as a present marker and its value. The decoder skips the first two frames, interprets the first eight original witness bits in their prescribed order, applies the fixed first-role table and skips the remaining witness bits. It scans the ciphertext frame in pairs to its terminator with just the sixteen possible tags, then walks backwards at most 3,071 positions to the requested bucket. It consumes the 96 selected value bits, sums the sixteen little-endian residues modulo 64 and writes the registered three-symbol output [true, sum==32, false]. Its determinism is verified for every first-role function. For authorized tags its decision agrees with β. Framing control across the matrix is independent of the number of matrix bits.

For any fixed first-role lookup this decoder has 15,877 states, zero work tapes, clock 268,435,456, description 1,714,716 and **cost 270,150,172**. The former absolute-position framed decoder cost 2,162,977,182,380. Each of 4096 gates uses at most 12·4224+6 physical frame symbols for the two allowed unary parent indices, at most 207,642,624 gate symbols in total; parameters, witness, four delimiters and the fixed 9,262,093-symbol ciphertext frame plus 3,071-position backward scan and the final read fit the new clock with room to spare. On the actual fixed YES fixture, using the first role that maps the XOR of its two four-bit nibbles to itself except that zero maps to one, the native decoder consumed the full framed packet emitted from the verified raw bank, followed its backward path and wrote [true,true,false] after **54,247,058 transitions** on a 54,246,674-symbol original input. The raw issuer output was wrapped in its standard ciphertext frame by the replay adapter before this decoder run.

The registered path is complete here for Dec with the stipulated first-role function and bucket semantics. The issuer still expects precomputed flags and a raw payload. In particular, no frame-packing wrapper, circuit classifier, table builder, working-time proof for arbitrary shared NANDs, or fixed-source reduction machine has been added to the native issuer. The goal's general circuit submission remains open. The LWE parameters and security premise have not changed. The bit counts and native replay do not alone prove the full Machine.run distribution.

## Independent replay arithmetic

In the following checker the binary file is serialized as one byte per actual output bit. For the actual YES fixture set the last role's missing tag to 14 as below. The matrix and body offset do not depend on the public reachability bitmap.

```python
from pathlib import Path
from hashlib import sha256
import sys
n,t,k,beta=map(int,sys.argv[1:5]);src=Path(sys.argv[5])
class Coins:
 def __init__(self):self.x=251
 def one(self):
    self.x=(self.x*6364136223846793005+1442695040888963407)%2**64
    return self.x>>63
 def skip(self,l):
    m,a=6364136223846793005,1442695040888963407
    while l:
        if l&1:self.x=(m*self.x+a)%2**64
        m,a=m*m%2**64,a*(m+1)%2**64
        l>>=1
c=Coins();c.skip(2*n+17*(t+15*k)+6)
s=[c.one()-c.one() for _ in range(n)];c.skip(n+2)
got=src.read_bytes()
head=0
def take6():
 global head
 r=sum(got[head+j]<<j for j in range(6));head+=6
 return r
v=[]
for j in range(t+15*k):
 c.skip(2)
 x=0
 for a in s:
    word=sum(c.one()<<h for h in range(6))
    assert take6()==word
    x+=word*a
 v.append((x+c.one()-c.one())%64)
 c.skip(7+n)
assert [take6() for _ in range(t)]==v[:t]
for key in range(k):
 r=v[t+15*key:t+15*key+15]
 vals=r+[(32*beta-sum(r))%64]
 for i,x in enumerate(vals):
    assert take6()==(x if key!=min(i,14) else 0)
assert head==len(got)
print('all matrix entries/training rows/tag shares',n*(t+15*k),t,16*k,sha256(got).hexdigest())
```
