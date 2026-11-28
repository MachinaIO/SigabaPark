---
title: Variable-width directed grants use thirteen public bits or less on the overlapping fixture
refs: [definition:WE_CircuitSAT_Capped, definition:PinnedSeparator, theorem:PinnedSeparator.combinedCost, note:quotient-separators-and-compact-monotone-joins]
tags: [witness-encryption, secret-sharing, turing-machine]
---

The fixed-width fixture in the companion note measures the full two-row source. Its root needs only one output bit. Payload size can instead propagate backwards through *public use counts*. Start with root width one. For each lower state s, let D_s be the sum of its consuming rows' already-set output label widths (count every occurrence separately). Use independent secret labels of width w_s=min(D_s,lambda); an unused state needs zero bits. For D_s≤lambda, split the fresh D_s bits into disjoint public-indexed pieces of the output widths. For D_s>lambda, expand a lambda-bit seed to ceil(D_s/lambda) leaves by the same two-row binary generator, concatenate them, truncate unused trailing bits and partition the result into disjoint pieces. Each generated lambda-bit block may serve several small uses. This demand calculation depends only on the signature structure, never on which states extend to a global accepting trace.

Grant each row's output by masking it with its children's appointed slices; the root label itself masks the bit. The previous bottom-up proof applies to all unequal widths: once idealized, disjoint slices from a uniform state expansion are jointly uniform; exact one-time raw labels need no switch. Cost is sum of row output widths plus one terminal bit and any source header (omit it if no expansion exists). Uniform label bits are sum of w_s. Thus dense reuse of a state can still be information-theoretically safe. The fixed-width count f_s-1 is replaced by max(ceil(D_s/lambda)-1,0) expander calls per state. Width propagation remains valid if several allowed rows share their output state because distinct grants can transmit the same parent label.

In the 128-input example, in both public modes six one-bit root grants consume six bits from each child side. The four child state's widths on each side are 1,1,2,2 in a mode-dependent order. Together with the root this costs thirteen independent fair bits, no lattice operations and no public source header. Only the two locally allowed keys per side are released. In the positive mode they total six bits across the sides; in the negative mode four. With the six masked rows and terminal bit, the ciphertext has 13 or 11 bits, respectively. Ciphertext length depends only on the public circuit. A complete enumeration (below) yields identical NO histograms on all 2048 possible 11-bit values, and disjoint YES supports of size 2048 in the 13-bit packet.

PinnedSeparator.enc is a genuine Sigaba Machine taking the predecoded public mode and the payload. It samples the thirteen bits onto its single work tape, emits the terminal at the first draw and performs alternating scans to compute remaining row parities. The decoder takes predecoded mode, all 128 raw primary witness bits in the registered group order, and the packet. It scans the three ORs and accumulates the four appropriate packet bits for a valid group triple. False or invalid triples return zero. With no framed-statement parser, the Enc component has 171 ticks, 1376 control states, description length 470592 and cost 470763; Dec has 142 ticks, 4576 states, description length 466752 and cost 466894. The theorem verifies their combined cost 937657, without including recognition of the raw full templates or encoding/decoding the registered tuple framing. These components do not implement a general Circuit-SAT wrapper. The machine bit masks enumerate terminal first, root grants in lexicographic triple order, then leaf keys in (side,state,occurrence) order; the first four columns of the mask lookup depend only on the public template.

The Lean transition replay exercised twenty actual machine encryptions, checked every emitted bit against the row parities, and ran 160 actual witness/ciphertext decodings across the two modes. The full enumeration below uses exact integer histograms. In the pinned positive circuit, the two witness group patterns are 010 and 101; their read positions (numbering the terminal zero) are (0,3,7,12) and (0,5,9,11). There is a further optional local simplification: when leaf-state feasibility is publicly decidable from its own allowed rows, supply known zero pads at those feasible states and retain independent disjoint pads for infeasible states. No internal reachability test is needed. The six root grants and one terminal then form a seven-bit ciphertext in either fixture. On NO every root grant has an independent missing-leaf pad, so all seven bits are independent uniform; on YES the two valid grant rows open the common root key. This variant is separate from the measured machines and histogram below. The public root predicates below are exactly the syntax-specific tests in the companion NAND replay.

```python
from collections import Counter,defaultdict
from itertools import product
for yes in (False,True):
 rows=[(a,b,c) for a,b,c in product(range(2),repeat=3) if ((a<=c) if yes else (a!=c or a==b==c))]
 slots=defaultdict(list)
 for row in rows:
  slots[(0,*row[:2])].append(row);slots[(1,*row[1:])].append(row)
 refs={};offset=1
 for key in sorted(slots):
  for idx,row in enumerate(slots[key]):refs[key,row]=offset+idx
  offset+=len(slots[key])
 assert offset==13
 def enc(k,b):
  view=[(k&1)^b]
  for row in rows:
   l,r=(0,*row[:2]),(1,*row[1:])
   view.append((k&1)^((k>>refs[l,row])&1)^((k>>refs[r,row])&1))
  for key in sorted(slots):
   if key[1]!=key[2]:
    view.extend((k>>refs[key,row])&1 for row in slots[key])
  return tuple(view)
 laws=[Counter(enc(k,b) for k in range(8192)) for b in (0,1)]
 print("YES" if yes else "NO","width",len(enc(0,0)),"support",len(laws[0]),len(laws[1]),"overlap",len(laws[0].keys()&laws[1].keys()),"equal",laws[0]==laws[1])
 assert (laws[0]==laws[1])==(not yes)
```
