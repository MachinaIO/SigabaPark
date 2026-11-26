import Lean

theorem solution {α : Type} (neg : α → α) (inv : ∀ a, neg (neg a) = a)
    (R : α → α → Prop) (refl : ∀ a, R a a)
    (trans : ∀ {a b c}, R a b → R b c → R a c)
    (contra : ∀ {a b}, R a b → R (neg b) (neg a))
    (base : ∀ a, ¬ (R a (neg a) ∧ R (neg a) a))
    (required : α → Prop) (vars : List α) :
    (∀ a b, required a → required b → ¬ R a (neg b)) ↔
    ∃ S : α → Prop, (∀ a, required a → S a) ∧
      (∀ a b, S a → R a b → S b) ∧ (∀ a, S a → ¬ S (neg a)) ∧
      (∀ a ∈ vars, S a ∨ S (neg a)) := by
  classical
  constructor
  · intro compatible
    let Closed (S : α → Prop) := ∀ a b, S a → R a b → S b
    let Cons (S : α → Prop) := ∀ a, S a → ¬ S (neg a)
    have add (S : α → Prop) (hc : Closed S) (hs : Cons S) (d : α)
        (hopp : ¬ S (neg d)) (hpath : ¬ R d (neg d)) :
        Closed (fun x ↦ S x ∨ R d x) ∧ Cons (fun x ↦ S x ∨ R d x) := by
      constructor
      · intro a b ha hab
        rcases ha with h | h
        · exact Or.inl (hc a b h hab)
        · exact Or.inr (trans h hab)
      · intro a ha hn
        rcases ha with aS | ad <;> rcases hn with nS | nd
        · exact hs a aS nS
        · exact hopp (hc a (neg d) aS (by simpa only [inv] using contra nd))
        · exact hopp (hc (neg a) (neg d) nS (contra ad))
        · exact hpath (trans nd (contra ad))
    have extend (S : α → Prop) (hc : Closed S) (hs : Cons S) (a : α) :
        ∃ T : α → Prop, (∀ x, S x → T x) ∧ Closed T ∧ Cons T ∧ (T a ∨ T (neg a)) := by
      by_cases h : S a ∨ S (neg a)
      · exact ⟨S, fun _ hx ↦ hx, hc, hs, h⟩
      · by_cases p : R a (neg a)
        · have q : ¬ R (neg a) (neg (neg a)) := by
            simpa only [inv] using (fun r ↦ base a ⟨p,r⟩ : ¬ R (neg a) a)
          have z := add S hc hs (neg a) (by simpa only [inv] using (fun v ↦ h (Or.inl v) : ¬ S a)) q
          exact ⟨_, fun _ hx ↦ Or.inl hx, z.1, z.2, Or.inr (Or.inr (refl _))⟩
        · have z := add S hc hs a (fun v ↦ h (Or.inr v)) p
          exact ⟨_, fun _ hx ↦ Or.inl hx, z.1, z.2, Or.inl (Or.inr (refl _))⟩
    let init := fun x ↦ ∃ d, required d ∧ R d x
    have hc : Closed init := by
      rintro a b ⟨d, hd, hda⟩ hab
      exact ⟨d,hd,trans hda hab⟩
    have hs : Cons init := by
      rintro a ⟨u, hu, hua⟩ ⟨v, hv, hvn⟩
      exact compatible v u hv hu (trans hvn (contra hua))
    induction vars with
    | nil =>
      exact ⟨init, fun a ha ↦ ⟨a,ha,refl a⟩, hc, hs, by simp⟩
    | cons a rest ih =>
      obtain ⟨S,hr,cl,cs,ht⟩ := ih
      obtain ⟨T,hst,tc,ts,hdec⟩ := extend S cl cs a
      refine ⟨T,fun x hx ↦ hst x (hr x hx),tc,ts,?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | h
      · exact hdec
      · exact (ht x h).elim (fun v ↦ Or.inl (hst _ v)) (fun v ↦ Or.inr (hst _ v))
  · rintro ⟨S,hr,hc,hs,_⟩ a b ha hb hab
    exact hs b (hr b hb) (hc a (neg b) (hr a ha) hab)
