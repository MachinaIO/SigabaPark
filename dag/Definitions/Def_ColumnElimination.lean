import Mathlib

namespace AdvancedEncryption.WE.ColumnElimination

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

/-- The target is a linear combination of these columns with one scalar per column. -/
def Reach (K : Type) {V : Type} [Field K] [AddCommGroup V] [Module K V] :
    List V → V → Prop
  | [], v => v = 0
  | a :: cs, v => ∃ (t : K) (u : V), Reach K cs u ∧ v = t • a + u

/-- Subtract the pivot column scaled by the selected coordinate. -/
def kill (a : V) (l : V →ₗ[K] K) : V →ₗ[K] V :=
  LinearMap.id - l.smulRight a

/-- Compose a projection for each current column. The choice can change with that column. -/
def terminal (choose : V → (V →ₗ[K] K)) : List V → (V →ₗ[K] V) → (V →ₗ[K] V)
  | [], H => H
  | a :: cs, H => terminal choose cs ((kill (H a) (choose (H a))).comp H)

/-- Recombine an ordered scalar witness with its source columns. -/
def weighted : List V → List K → V
  | a :: cs, t :: bs => t • a + weighted cs bs
  | _, _ => 0

/-- Back-substitution in original column order. The zero-column case simply chooses a scalar
that never changes the reconstructed sum. -/
def backsolve (choose : V → (V →ₗ[K] K)) : List V → (V →ₗ[K] V) → V → List K
  | [], _, _ => []
  | a :: cs, H, v =>
    let l := choose (H a)
    let bs := backsolve choose cs ((kill (H a) l).comp H) v
    (l (H v - H (weighted cs bs))) :: bs

/-- Pick the least nonzero row in a binary column, and the zero functional for a zero column. -/
noncomputable def firstOne {m : Nat} (a : Fin m → ZMod 2) :
    (Fin m → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  let s := Finset.univ.filter (fun i => a i ≠ 0)
  if h : s.Nonempty then LinearMap.proj (s.min' h) else 0

end AdvancedEncryption.WE.ColumnElimination
