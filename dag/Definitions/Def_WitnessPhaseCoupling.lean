import Mathlib.Tactic

namespace WitnessPhaseCoupling

variable {F U V I X Y : Type*} [Field F] [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]

/-- The issuer knows the phase in its own coins, even when the public-key simulator cannot
    sample the unknown phase on the same front. NO translates each independent mask. -/
def align (v : I → U) (h₀ h₁ : I → F) : (I → U) ≃ (I → U) where
  toFun us := fun i => us i + (h₀ i-h₁ i) • v i
  invFun us := fun i => us i - (h₀ i-h₁ i) • v i
  left_inv := by intro us; funext i; simp
  right_inv := by intro us; funext i; simp

def capsule (R : I → U →ₗ[F] V) (T : I → U →ₗ[F] F)
    (h : I → F) (us : I → U) : I → V × F :=
  fun i => (R i (us i), h i + T i (us i))

theorem capsule_align (v : I → U) (R : I → U →ₗ[F] V) (T : I → U →ₗ[F] F)
    (hR : ∀ i, R i (v i)=0) (hT : ∀ i, T i (v i)=1) (h₀ h₁ : I → F) (us : I → U) :
    capsule R T h₁ (align v h₀ h₁ us) = capsule R T h₀ us := by
  funext i
  apply Prod.ext
  · simp [capsule, align, hR]
  · simp [capsule, align, hT]
    abel

/-- Change the front seed and align the unknown phase *after* that change. This does not
    require the simulator to compute either phase; it gives a coupling of honest laws. -/
def tapeEquiv (e : X ≃ X) (v : I → U) (h₀ h₁ : X → I → F) :
    X × (I → U) ≃ X × (I → U) where
  toFun p := (e p.1, align v (h₀ p.1) (h₁ (e p.1)) p.2)
  invFun p := (e.symm p.1, (align v (h₀ (e.symm p.1)) (h₁ p.1)).symm p.2)
  left_inv := by rintro ⟨x,us⟩; simp
  right_inv := by rintro ⟨y,us⟩; simp

theorem whole_view (f₀ f₁ : X → Y) (e : X ≃ X) (he : ∀ x, f₁ (e x)=f₀ x)
    (v : I → U) (R : I → U →ₗ[F] V) (T : I → U →ₗ[F] F)
    (hR : ∀ i, R i (v i)=0) (hT : ∀ i, T i (v i)=1)
    (h₀ h₁ : X → I → F) (p : X × (I → U)) :
    let q := tapeEquiv e v h₀ h₁ p
    (f₁ q.1, capsule R T (h₁ q.1) q.2) =
      (f₀ p.1, capsule R T (h₀ p.1) p.2) := by
  rcases p with ⟨x,us⟩
  change (f₁ (e x), capsule R T (h₁ (e x)) (align v (h₀ x) (h₁ (e x)) us)) =
    (f₀ x, capsule R T (h₀ x) us)
  rw [he, capsule_align v R T hR hT]

/-- Fresh dedicated uniform body pads give a front permutation even when its offsets depend
    on the complete published header. -/
def paddedFront {A B : Type*} [AddGroup B] (p : A ≃ A) (off : A → B) :
    A × B ≃ A × B where
  toFun x := (p x.1, x.2 + off (p x.1))
  invFun y := (p.symm y.1, y.2 - off y.1)
  left_inv := by rintro ⟨a,b⟩; simp
  right_inv := by rintro ⟨a,b⟩; simp

/-- Any observer event has equal coin multiplicity once the whole views agree under a
    permutation; the event may test several data fields together. -/
def eventEquiv {A B : Type*} (f₀ f₁ : A → B) (e : A ≃ A)
    (h : ∀ a, f₁ (e a) = f₀ a) (event : B → Prop) :
    {a // event (f₀ a)} ≃ {a // event (f₁ a)} where
  toFun a := ⟨e a.val, (h a.val).symm ▸ a.property⟩
  invFun a := ⟨e.symm a.val, by simpa only [← h, Equiv.apply_symm_apply] using a.property⟩
  left_inv := by intro a; apply Subtype.ext; simp
  right_inv := by intro a; apply Subtype.ext; simp

theorem equalMultiplicity {A B : Type*} [Fintype A] (f₀ f₁ : A → B) (e : A ≃ A)
    (h : ∀ a, f₁ (e a) = f₀ a) (event : B → Prop)
    [DecidablePred (fun a => event (f₀ a))] [DecidablePred (fun a => event (f₁ a))] :
    Fintype.card {a // event (f₀ a)} = Fintype.card {a // event (f₁ a)} :=
  Fintype.card_congr (eventEquiv f₀ f₁ e h event)

/-- With a fixed nonzero binary column combination, put a pivot in the last column.
    All other columns contribute a fixed vector after their coins have been sampled.
    Exactly one pivot column cancels that vector. -/
def fixedCombinationFiber {A G : Type*} [AddGroup G] (offset : A → G) :
    {p : A × G // p.2 + offset p.1 = 0} ≃ A where
  toFun p := p.val.1
  invFun x := ⟨(x,-offset x), by simp⟩
  left_inv := by
    rintro ⟨⟨x,y⟩,h⟩
    change y+offset x=0 at h
    apply Subtype.ext
    change (x,-offset x)=(x,y)
    rw [eq_neg_of_add_eq_zero_left h]
  right_inv := by intro x; rfl

/-- Union bound by assigning every bad matrix one offending combination. The summands
    may overlap; no independence across the combinations is assumed. -/
theorem unionCount {A J : Type*} [Fintype A] [Fintype J] (Q : J → A → Prop)
    [∀ j, DecidablePred (Q j)] [DecidablePred (fun x => ∃ j, Q j x)] :
    Fintype.card {x // ∃ j, Q j x} ≤ ∑ j, Fintype.card {x // Q j x} := by
  classical
  let f : {x // ∃ j, Q j x} → Σ j, {x // Q j x} := fun x =>
    ⟨x.property.choose, x.val, x.property.choose_spec⟩
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : Σ j, {x // Q j x} => z.2.val) h)
  simpa only [Fintype.card_sigma] using Fintype.card_le_of_injective f hf

def view (f : X → Y) (h : X → I → F) (R : I → U →ₗ[F] V) (T : I → U →ₗ[F] F)
    (p : X × (I → U)) : Y × (I → V × F) := (f p.1, capsule R T (h p.1) p.2)

end WitnessPhaseCoupling
