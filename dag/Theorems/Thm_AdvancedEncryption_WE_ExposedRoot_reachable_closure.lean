import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Common

/-- **Reachable closure (note `pq-we-exposed-root-reachable-lemma`, §2).** Let `V_{i-1}` span
the rows of `A_{i-1}` reachable from the public exposure and `V_i` a row basis of
`[V_{i-1} Ŝ_{i,0}; V_{i-1} Ŝ_{i,1}]`, so `V_{i-1} Ŝ_{i,b} = K_{i,b} V_i`. Then the exposed part of
the level-`i` target is `K_{i,b} (V_i A_i) + V_{i-1} E_{i,b}`: it depends on `A_i` only through
`V_i A_i`. Hence the complement `P' A_i` appears only in the level-`i+1` preimages, which is the
hidden-matrix hypothesis of CVW18 Lemma 4.4 for the complement. -/
theorem AdvancedEncryption.WE.ExposedRoot.reachable_closure {R : Type*} [Ring R] {r r' n m : Type*}
    [Fintype r] [Fintype n]
    (V' : Matrix r' n R) (S : Matrix n n R) (K : Matrix r' r R) (V : Matrix r n R)
    (A : Matrix n m R) (E : Matrix n m R) (hX : V' * S = K * V) :
    V' * (S * A + E) = K * (V * A) + V' * E := by sorry
