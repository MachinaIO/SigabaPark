import Mathlib
import SigabaNeo.Trusted.Assumption

namespace TerminalRectangle

/-- One bit of a shared terminal word at one index and one pair of sides. -/
def body (t j a c : Bool) := t ^^ j ^^ a ^^ c

/-- The same role is hidden across all side pairs at an index. -/
inductive HiddenRole | join | leftSource | rightSource

/-- Which role has its hidden terminal-bit coordinate complemented. -/
def flipJoin : HiddenRole → Bool → Bool
  | .join, x => !x
  | _, x => x

def flipLeft : HiddenRole → Bool → Bool
  | .leftSource, x => !x
  | _, x => x

def flipRight : HiddenRole → Bool → Bool
  | .rightSource, x => !x
  | _, x => x

/-- The two source indices may coincide, but neither may equal the join. -/
def Wins {I : Type} (A J C : Set I) : Prop :=
  ∃ i ∈ A, ∃ j ∈ J, ∃ k ∈ C, i ≠ j ∧ k ≠ j

end TerminalRectangle
