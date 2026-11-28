import SigabaNeoStd.Machines.Gates
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace NANDShiftedSupport
abbrev Word := Fin 16
abbrev F := ZMod 2

/-- Bit j is one exactly when the monomial on subset j occurs at the given center. -/
def mask : Word → Nat :=
  ![32488,27580,28122,31135,31206,28087,27607,32406,32406,27607,28087,31206,31135,28122,27580,32488]
def terms (c : Word) := Finset.univ.filter (fun m : Word ↦ (mask c).testBit m.val)
def mon (x m : Word) : F := if x.val &&& m.val = m.val then 1 else 0
def exactlyTwo (a : Nat) : F := if a ∈ ([3,5,6,9,10,12] : List Nat) then 1 else 0

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem local_eval : ∀ c x : Word, ∑ m ∈ terms c, mon x m = exactlyTwo (x.val ^^^ c.val) := by decide

theorem local_counts : ∀ c : Word, (terms c).card=10 ∨ (terms c).card=11 := by decide

def support {k : Nat} (c : Fin k → Word) := Fintype.piFinset (fun i ↦ terms (c i))

/-- A product of block monomials is uniquely indexed by its tuple of subsets on
the disjoint four-bit blocks. The Cartesian support has no repeated terms. -/
theorem global_eval {k : Nat} (c x : Fin k → Word) :
    ∑ m ∈ support c, (∏ i, mon (x i) (m i)) = ∏ i, exactlyTwo ((x i).val ^^^ (c i).val) := by
  rw [support,← Finset.prod_univ_sum]
  simp only [local_eval]

theorem global_count {k : Nat} (c : Fin k → Word) : 10^k ≤ (support c).card := by
  rw [support,Fintype.card_piFinset]
  calc
    10^k = ∏ _ : Fin k, (10:Nat) := by simp
    _ ≤ _ := Finset.prod_le_prod' (fun i _ ↦ by rcases local_counts (c i) with h|h <;> omega)

theorem over_cap (c : Fin 32 → Word) : 2^106 < (support c).card-1 := by
  have h := global_count c
  omega


/-- A complete four-primary-input, 55-gate native fixture. Its first wire is
constant true, followed by four bits in least-significant-first order. -/
def block : SigabaNeo.GateList := [
  (1,1),(2,2),(3,3),(4,4),(1,2),(9,9),(10,7),(11,11),(12,8),(13,13),(1,6),(15,15),(16,3),(17,17),(18,8),(19,19),(5,2),(21,21),(22,3),(23,23),(24,8),(25,25),(1,6),(27,27),(28,7),(29,29),(30,4),(31,31),(5,2),(33,33),(34,7),(35,35),(36,4),(37,37),(5,6),(39,39),(40,3),(41,41),(42,4),(43,43),(14,14),(20,20),(45,46),(47,47),(26,26),(48,49),(50,50),(32,32),(51,52),(53,53),(38,38),(54,55),(56,56),(44,44),(57,58)]
theorem block_size : block.length=55 := by decide
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem native_block : ∀ x : Word,
    SigabaNeo.evalGates ((List.range 4).map (fun i ↦ x.val.testBit i),block) =
    decide (exactlyTwo x.val=1) := by decide
theorem full_gate_accounting : 32*55 + (32-1)*2 + 2274 = 4096 := by decide

end NANDShiftedSupport
