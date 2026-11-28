import Mathlib.Tactic
namespace PermutationSignatureTree
variable {A B : Type}
abbrev Trans (A B : Type) := (A → A) × (B → B)
inductive Tree where
  | leaf | node (rev : Bool) (l r : Tree)
def Input : Tree → Type
  | .leaf => Bool
  | .node _ l r => Input l × Input r
def Tables (A B : Type) : Tree → Type
  | .leaf => Bool → Trans A B
  | .node _ l r => Tables A B l × Tables A B r

def combine (rev : Bool) (p q : Trans A B) : Trans A B :=
  (q.1 ∘ p.1,if rev then p.2 ∘ q.2 else q.2 ∘ p.2)
def run : (t : Tree) → Tables A B t → Input t → Trans A B
  | .leaf,g,x => g x
  | .node rev l r,g,x => combine rev (run l g.1 x.1) (run r g.2 x.2)

def attainable [DecidableEq (Trans A B)] : (t : Tree) → Tables A B t → Finset (Trans A B)
  | .leaf,g => Finset.univ.image g
  | .node rev l r,g => ((attainable l g.1).product (attainable r g.2)).image
      (fun q ↦ combine rev q.1 q.2)
theorem mem_iff [DecidableEq (Trans A B)] (t : Tree) (g : Tables A B t) (q : Trans A B) :
    q∈attainable t g ↔ ∃ x,run t g x=q := by
  induction t generalizing q with
  | leaf =>
    change q ∈ Finset.univ.image g ↔ ∃ x : Bool,g x=q
    constructor
    · intro h; obtain ⟨x,_,hx⟩ := Finset.mem_image.mp h; exact ⟨x,hx⟩
    · rintro ⟨x,hx⟩; exact Finset.mem_image.mpr ⟨x,Finset.mem_univ _,hx⟩
  | node rev l r il ir =>
    simp only [attainable,Finset.mem_image,Finset.mem_product,run]
    constructor
    · rintro ⟨⟨p,q⟩,hpq,rfl⟩
      obtain ⟨hp,hq⟩ := Finset.mem_product.mp hpq
      obtain ⟨x,rfl⟩ := (il _ _).mp hp
      obtain ⟨y,rfl⟩ := (ir _ _).mp hq
      exact ⟨(x,y),rfl⟩
    · rintro ⟨⟨x,y⟩,rfl⟩
      exact ⟨(run l g.1 x,run r g.2 y),Finset.mem_product.mpr ⟨(il _ _).mpr ⟨x,rfl⟩,(ir _ _).mpr ⟨y,rfl⟩⟩,rfl⟩

theorem count [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (t : Tree) (g : Tables A B t) : (attainable t g).card ≤
      Fintype.card A ^ Fintype.card A * Fintype.card B ^ Fintype.card B := by
  simpa [Trans,Fintype.card_fun] using (attainable t g).card_le_univ

def verdict (a : A) (b : B) (fa : A → Bool) (fb : B → Bool) (p : Trans A B) :=
  (fa (p.1 a),fb (p.2 b))
theorem both [DecidableEq (Trans A B)] (t : Tree) (g : Tables A B t)
    (a : A) (b : B) (fa : A → Bool) (fb : B → Bool) :
    (∃ p∈attainable t g,verdict a b fa fb p=(true,true)) ↔
      ∃ x,verdict a b fa fb (run t g x)=(true,true) := by
  simp only [mem_iff]; constructor
  · rintro ⟨p,⟨x,rfl⟩,h⟩; exact ⟨x,h⟩
  · rintro ⟨x,h⟩; exact ⟨_,⟨x,rfl⟩,h⟩
/-- Opposite whole-block orders with independent words; the suffix is represented
by its full acceptance profile, not a guessed start state. -/
def leftCell {U : Type} (fb : B → Bool) (a : A)
    (p : U → A → A) (q : U → B → B) (u : U) := (p u a,fb ∘ q u)
def rightCell {V : Type} (fa : A → Bool) (b : B)
    (p : V → A → A) (q : V → B → B) (v : V) := (fa ∘ p v,q v b)
theorem opposite {U V : Type} (fa : A → Bool) (fb : B → Bool) (a : A) (b : B)
    (lA : U → A → A) (lB : U → B → B) (rA : V → A → A) (rB : V → B → B)
    (u : U) (v : V) :
    let l := leftCell fb a lA lB u
    let r := rightCell fa b rA rB v
    (r.1 l.1,l.2 r.2)=(fa (rA v (lA u a)),fb (lB u (rB v b))) := by rfl

/-- With an absorbing dead state all transformations are determined by the live entries. -/
theorem dead_bound (T : Finset (Fin 3 → Fin 3)) (h : ∀ f∈T,f 2=2) : T.card≤9 := by
  let r := fun f : Fin 3 → Fin 3 ↦ (f 0,f 1)
  have inj : Set.InjOn r T := by
    intro f hf g hg eq
    have h0 : f 0=g 0 := congrArg Prod.fst eq
    have h1 : f 1=g 1 := congrArg Prod.snd eq
    funext i; fin_cases i
    · exact h0
    · exact h1
    · exact (h f hf).trans (h g hg).symm
  rw [← Finset.card_image_of_injOn inj]
  exact (T.image r).card_le_univ
end PermutationSignatureTree
