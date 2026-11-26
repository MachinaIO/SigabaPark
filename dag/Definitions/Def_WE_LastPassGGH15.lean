import Definitions.Def_WE_MaskedGGH15

/-!
# Multi-pass masked γ⊗-GGH15 with the comparator on the last copy (regime (d))

Vocabulary for the equality-cube flip of the multi-pass candidates MP2/MP3 (DAG notes
`pq-we-multipass-ggh15` §3(d) and `pq-we-equality-cube-flip`). It reuses everything of
`Def_WE_MaskedGGH15` (`positionalView`): secrets `diag(P ⊗ R, M ⊗ S', S)` with bit-independent
`R_i`, the CNF branching program of `Ψ`, the left matrices `J_O`, `J_C`, the encoding of
CVW18 Construction 5.1. Two things change.

* **The comparator reads only the levels `o, …, h−1`** (`cmpMatFrom`): it is the identity on the
  levels `< o` and the reflected-Gray comparator of `cmpMat (h − o) t` on the last `h − o` levels.
  With `o = h − n` these are the `n` levels of the last copy of the witness, so in hybrid `t` a
  level string is labelled `mask'` iff the Gray rank of its last copy is `< t`. All
  `2^o` prefixes of the first `o` levels reach the start of the comparator (the classes of the
  comparator are *fat*).
* **The label of the eq state is a parameter** (`lastPassTop`): with `eqFlip = false` the eq rows
  of the top matrix are `mask` (as in `positionalTop`: eq/gt labelled `mask`); with
  `eqFlip = true` they are `mask'` (eq labelled like lt). Flipping it changes the value of exactly
  the strings whose last copy is the codeword of rank `t`: the consistent string and all its
  orphan mixed strings, one *equality cube* per first mismatch position.

`copyOff h n c p` is the first level of copy `p < c` of the witness in the layout used by the
nodes of this vocabulary: copies `0, …, c−2` at levels `p·n, …, p·n + n − 1`, the last copy at
the end (`h − n, …, h − 1`), further levels (Tseitin gate bits) in between.
-/

namespace AdvancedEncryption.WE.LastPass

open SigabaNeo SigabaNeo.Lattices Matrix AdvancedEncryption.WE.GGH15
open AdvancedEncryption.WE.MaskedGGH15
open Cslib.Probability

/-- First level of copy `p` of the `n` witness bits among `c` copies over `h` levels: the last
copy (`p = c − 1`) occupies the last `n` levels, the others the levels `p·n, …, p·n + n − 1`. -/
def copyOff (h n c p : ℕ) : ℕ := if p + 1 = c then h - n else p * n

/-- The comparator on the levels `≥ o` only: identity below `o`, `cmpMat (h − o) t` at
level `i ≥ o` (as its level `i − o`). -/
def cmpMatFrom (h o t : ℕ) (i : Fin h) (b : Bool) : Matrix (Fin 3) (Fin 3) ℤ :=
  if hi : o ≤ (i : ℕ) then cmpMat (h - o) t ⟨(i : ℕ) - o, by have := i.isLt; omega⟩ b else 1

/-- The top matrix: comparator rows `mask'` on lt, `mask` on gt, and on eq `mask'` if `eqFlip`,
else `mask`; constraint rows `A^{con}`; CPRF rows `A^{bot}`. -/
def lastPassTop {sh : Shape} {m q : ℕ} (eqFlip : Bool)
    (mask mask' : Matrix (Fin sh.dR) (Fin m) (ZMod q))
    (Acon : Matrix (Fin sh.w × Fin sh.n') (Fin m) (ZMod q))
    (Abot : Matrix (Fin sh.n) (Fin m) (ZMod q)) : Matrix (Rows 3 sh) (Fin m) (ZMod q) :=
  Sum.elim (fun sr => if sr.1 = 0 ∨ (sr.1 = 1 ∧ eqFlip = true) then mask' sr.2 else mask sr.2)
    (Sum.elim Acon Abot)

/-- **Hybrid `(t, eqFlip)` of the masked γ⊗-GGH15 candidate with the comparator on the levels
`≥ o`.** As `positionalView`, with comparator `cmpMatFrom h o t`, start state
`cmpStart (h − o) t`, and top matrix `lastPassTop eqFlip`. Published:
`(J_O A_0, J_C A_0, {D_{i,b}})` and the challenge component `(r₀ R_*) · mask`. With `o = h − n`:
hybrid `(0, false)` is the real view; in `(t, false)` the strings whose last copy has Gray rank
`< t` are labelled `mask'`; `(t, true)` also labels the rank-`t` codeword's strings `mask'`, so it
has the same labels as `(t + 1, false)`; in `(2^n, false)` `mask` occurs only in the challenge. -/
noncomputable def lastPassView (p : Params) (h : ℕ) (sh : Shape) (Ψ : CNF sh.w h)
    (r0 : Fin sh.dR → ℤ) (jC : Fin sh.w → ℤ) (s0 : Fin sh.n' → ℤ) (o t : ℕ) (eqFlip : Bool) :
    PMF (List Bool) := do
  let RS ← secretLaw h sh p.σ
  let mask ← PMF.uniformOfFintype (Matrix (Fin sh.dR) (Fin p.m) (ZMod p.q))
  let mask' ← PMF.uniformOfFintype (Matrix (Fin sh.dR) (Fin p.m) (ZMod p.q))
  let Acon ← PMF.uniformOfFintype (Matrix (Fin sh.w × Fin sh.n') (Fin p.m) (ZMod p.q))
  let Abot ← PMF.uniformOfFintype (Matrix (Fin sh.n) (Fin p.m) (ZMod p.q))
  let Shat := fun i b =>
    maskedSecret (cmpMatFrom h o t i b) (RS.1 i) (cnfMat Ψ i b) (RS.2.1 i b) (RS.2.2 i b)
  let AD ← encode p Shat (lastPassTop eqFlip mask mask' Acon Abot)
  return encodeView (leftO (cmpStart (h - o) t) r0) (leftC jC s0) (AD.1 0) AD.2
    (encodeVec (maskOf p.q r0 RS.1 mask))

end AdvancedEncryption.WE.LastPass
