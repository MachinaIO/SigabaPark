import Definitions.Def_WE_TranslationXAG
open AdvancedEncryption.WE.TranslationXAG
/-- Live AND input parity equations certify a constant derivative of an XOR-AND circuit. -/
theorem solution {ι : Type} (t x : ι → Bool) (gates : List (Form ι × Form ι))
    (zero : ∀ ab ∈ gates, parity ab.1.raw t=false ∧ parity ab.2.raw t=false)
    (f : Form ι) (init : List Bool) :
    value f (fun i => x i ^^ t i) (run (fun i => x i ^^ t i) init gates) =
      (value f x (run x init gates) ^^ parity f.raw t) := by
  have par (r : List ι) : parity r (fun i => x i ^^ t i)= (parity r x ^^ parity r t) := by
    induction r with
    | nil => rfl
    | cons a r ih =>
      change ((x a ^^ t a) ^^ parity r (fun i => x i ^^ t i)) = ((x a ^^ parity r x) ^^ (t a ^^ parity r t))
      rw [ih]
      cases x a <;> cases t a <;> cases parity r x <;> cases parity r t <;> rfl
  have shift (f : Form ι) (v : List Bool) : value f (fun i => x i ^^ t i) v =
      (value f x v ^^ parity f.raw t) := by
    unfold value
    rw [par]
    cases f.bias <;> cases parity f.raw x <;> cases parity f.raw t <;> cases parity f.atoms (fun j => v.getD j false) <;> rfl
  have same : run (fun i => x i ^^ t i) init gates=run x init gates := by
    induction gates generalizing init with
    | nil => rfl
    | cons ab tail ih =>
      have h := zero ab (by simp)
      change run _ (init ++ [value ab.1 _ init && value ab.2 _ init]) tail = run _ (init ++ [value ab.1 _ init && value ab.2 _ init]) tail
      rw [shift ab.1 init,shift ab.2 init,h.1,h.2,Bool.xor_false,Bool.xor_false]
      exact ih (fun p hp => zero p (by simp [hp])) _
  rw [same,shift]
