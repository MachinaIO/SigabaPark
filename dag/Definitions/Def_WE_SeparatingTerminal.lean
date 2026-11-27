import Mathlib

namespace AdvancedEncryption.WE.SeparatingTerminal

open Polynomial

/-- A systematic label encoding by four base-nine digits, with a fixed numbering of the field. -/
noncomputable def labels {K : Type} [Field K] (digits : Fin 9 ≃ K) :
    Fin 4224 ↪ degreeLT K 4 :=
  (Fin.castLEEmb (show 4224 ≤ 9 ^ 4 by decide)).trans
    (finFunctionFinEquiv.symm.trans
      ((Equiv.piCongrRight fun _ : Fin 4 ↦ digits).trans (degreeLTEquiv K 4).symm.toEquiv)).toEmbedding

/-- At seven distinct points the product of two nonzero cubic differences cannot vanish. -/
theorem separates {K : Type} [Field K] (digits : Fin 9 ≃ K)
    (points : Fin 7 ↪ K) (a c j : Fin 4224) (ha : a ≠ j) (hc : c ≠ j) :
    ∃ x, ((labels digits a).val.eval (points x) ≠ (labels digits j).val.eval (points x)) ∧
         ((labels digits c).val.eval (points x) ≠ (labels digits j).val.eval (points x)) := by
  classical
  let f := fun i ↦ (labels digits i).val
  have hinj : Function.Injective f := fun _ _ h ↦ (labels digits).injective (Subtype.ext h)
  have bound (i) : (f i).natDegree ≤ 3 := by
    by_cases h : f i = 0
    · simp [h]
    · have := (natDegree_lt_iff_degree_lt h).2 (mem_degreeLT.1 (labels digits i).property)
      omega
  let p := (f a - f j) * (f c - f j)
  have hn : p ≠ 0 := mul_ne_zero (sub_ne_zero.mpr (hinj.ne ha)) (sub_ne_zero.mpr (hinj.ne hc))
  have hd : p.natDegree ≤ 3 + 3 := natDegree_mul_le_of_le
    (natDegree_sub_le_of_le (bound a) (bound j)) (natDegree_sub_le_of_le (bound c) (bound j))
  by_contra! h
  have hall : (Finset.univ.map points).val ⊆ p.roots := by
    intro y hy
    change y ∈ Finset.univ.map points at hy
    obtain ⟨x, _, rfl⟩ := Finset.mem_map.1 hy
    apply (mem_roots hn).2
    simp only [IsRoot, p, eval_mul, eval_sub, mul_eq_zero, sub_eq_zero]
    exact or_iff_not_imp_left.mpr (h x)
  have hcard := (card_le_degree_of_subset_roots hall).trans hd
  simp at hcard

abbrev Role := Fin 3

/-- A finite family of ternary terms, with any number of selected source indices per role. -/
def Wins {I T : Type} (eligible : Role → I → T → Prop) (opened : Role → I → Prop) : Prop :=
  ∃ t, ∀ r, ∃ i, opened r i ∧ eligible r i t

theorem missing_role {I T : Type} (e : Role → I → T → Prop) (o : Role → I → Prop)
    (h : ¬ Wins e o) : ∃ miss : T → Role, ∀ t i, o (miss t) i → ¬ e (miss t) i t := by
  classical
  simp only [Wins, not_exists, not_forall, not_and] at h
  exact ⟨fun t ↦ (h t).choose, fun t ↦ (h t).choose_spec⟩

/-- Terms are indexed by a point and one of the nine possible field values. -/
def eligible {K : Type} [Field K] (digits : Fin 9 ≃ K) (points : Fin 7 ↪ K)
    (r : Role) (i : Fin 4224) (t : Fin 7 × K) : Prop :=
  if r = 2 then (labels digits i).val.eval (points t.1) = t.2
  else (labels digits i).val.eval (points t.1) ≠ t.2

theorem wins_iff {K : Type} [Field K] (digits : Fin 9 ≃ K) (points : Fin 7 ↪ K)
    (o : Role → Fin 4224 → Prop) :
    Wins (eligible digits points) o ↔
    ∃ a c j, o 0 a ∧ o 1 c ∧ o 2 j ∧ a ≠ j ∧ c ≠ j := by
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨a, ha, ea⟩ := ht 0
    obtain ⟨c, hc, ec⟩ := ht 1
    obtain ⟨j, hj, ej⟩ := ht 2
    simp [eligible] at ea ec ej
    exact ⟨a, c, j, ha, hc, hj, fun h ↦ ea (h ▸ ej), fun h ↦ ec (h ▸ ej)⟩
  · rintro ⟨a, c, j, ha, hc, hj, haj, hcj⟩
    obtain ⟨x, exa, exc⟩ := separates digits points a c j haj hcj
    refine ⟨(x, (labels digits j).val.eval (points x)), ?_⟩
    intro r
    fin_cases r
    · exact ⟨a, ha, by simpa [eligible] using exa⟩
    · exact ⟨c, hc, by simpa [eligible] using exc⟩
    · exact ⟨j, hj, by simp [eligible]⟩

/-- A field numbering and seven evaluation points exist. Their choice affects only serialization. -/
noncomputable def fieldDigits : Fin 9 ≃ GaloisField 3 2 := by
  classical
  letI := Fintype.ofFinite (GaloisField 3 2)
  apply Fintype.equivOfCardEq
  simpa [Nat.card_eq_fintype_card] using (GaloisField.card 3 2 (by decide)).symm

noncomputable def fieldPoints : Fin 7 ↪ GaloisField 3 2 :=
  (Fin.castLEEmb (show 7 ≤ 9 by decide)).trans fieldDigits.toEmbedding

def roleShare (b u v : Bool) (r : Role) : Bool :=
  if r = 0 then u else if r = 1 then v else (b ^^ u) ^^ v

theorem recover (b u v : Bool) :
    (roleShare b u v 0 ^^ roleShare b u v 1) ^^ roleShare b u v 2 = b := by
  cases b <;> cases u <;> cases v <;> decide

theorem flip_share (b u v : Bool) (r m : Role) :
    roleShare (!b) (u ^^ decide (m = 0)) (v ^^ decide (m = 1)) r =
      (roleShare b u v r ^^ decide (m = r)) := by
  fin_cases r <;> fin_cases m <;> cases b <;> cases u <;> cases v <;> decide

/-- A public correction and its corresponding independently sampled source-pad coordinate. -/
abbrev Index {I T : Type} (e : Role → I → T → Prop) := {k : Role × I × T // e k.1 k.2.1 k.2.2}

abbrev Coins {I T : Type} (e : Role → I → T → Prop) :=
  (T → Bool) × (T → Bool) × (Index e → Bool)

def view {I T : Type} {e : Role → I → T → Prop} (o : Role → I → Prop) (b : Bool)
    (s : Coins e) : (Index e → Bool) × ({k : Index e // o k.val.1 k.val.2.1} → Bool) :=
  (fun k ↦ roleShare b (s.1 k.val.2.2) (s.2.1 k.val.2.2) k.val.1 ^^ s.2.2 k,
   fun k ↦ s.2.2 k.val)

def toggle {I T : Type} {e : Role → I → T → Prop} (m : T → Role) (s : Coins e) : Coins e :=
  (fun t ↦ s.1 t ^^ decide (m t = 0), fun t ↦ s.2.1 t ^^ decide (m t = 1),
   fun k ↦ s.2.2 k ^^ decide (m k.val.2.2 = k.val.1))

theorem toggle_twice {I T : Type} {e : Role → I → T → Prop} (m : T → Role)
    (s : Coins e) : toggle m (toggle m s) = s := by
  apply Prod.ext
  · funext t; simp [toggle]
  · apply Prod.ext <;> funext t <;> simp [toggle]

theorem view_toggle {I T : Type} {e : Role → I → T → Prop} {o : Role → I → Prop}
    {m : T → Role} (hm : ∀ t i, o (m t) i → ¬ e (m t) i t) (b : Bool) (s : Coins e) :
    view o (!b) (toggle m s) = view o b s := by
  apply Prod.ext
  · funext k
    simp only [view, toggle, flip_share]
    generalize roleShare b (s.1 k.val.2.2) (s.2.1 k.val.2.2) k.val.1 = a
    generalize decide (m k.val.2.2 = k.val.1) = z
    cases a <;> cases z <;> cases s.2.2 k <;> rfl
  · funext k
    have ne : m k.val.val.2.2 ≠ k.val.val.1 := by
      intro h
      exact hm _ _ (h.symm ▸ k.property) (h.symm ▸ k.val.property)
    simp [view, toggle, ne]

/-- Exact equality of every fixed losing view's two finite uniform fiber sizes. -/
noncomputable def fibers {I T : Type} {e : Role → I → T → Prop} {o : Role → I → Prop}
    (h : ¬ Wins e o) (b : Bool) (z) :
    {s : Coins e // view o b s = z} ≃ {s : Coins e // view o (!b) s = z} := by
  classical
  let m := (missing_role e o h).choose
  have hm := (missing_role e o h).choose_spec
  exact {
    toFun := fun s ↦ ⟨toggle m s.val, (view_toggle hm b s.val).trans s.property⟩
    invFun := fun s ↦ ⟨toggle m s.val, (by simpa using (view_toggle hm (!b) s.val).trans s.property)⟩
    left_inv := fun s ↦ Subtype.ext (toggle_twice m s.val)
    right_inv := fun s ↦ Subtype.ext (toggle_twice m s.val) }

/-- A classical adaptive reader with bounded queries. The state can store the entire history. -/
def walk {D S : Type} (query : S → Option D) (advance : S → D → Bool → S)
    (pad : D → Bool) : ℕ → S → List (D × Bool)
  | 0, _ => []
  | n + 1, state =>
    match query state with
    | none => []
    | some k => (k, pad k) :: walk query advance pad n (advance state k (pad k))

theorem replay {D S : Type} (query : S → Option D) (advance : S → D → Bool → S)
    (a b : D → Bool) (n : ℕ) (state : S)
    (agree : ∀ k v, (k,v) ∈ walk query advance a n state → b k = a k) :
    walk query advance b n state = walk query advance a n state := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
    cases h : query state with
    | none => simp [walk, h]
    | some k =>
      have hk := agree k (a k) (by simp [walk, h])
      simp only [walk, h, hk, List.cons.injEq, true_and]
      exact ih _ (fun i v hi ↦ agree i v (by simp [walk, h, hi]))

/-- A complete public record and a particular adaptive trace have equal fiber sizes when
every opened source along that trace belongs to a losing union. -/
noncomputable def transcriptFibers {I T S : Type} {e : Role → I → T → Prop}
    (o : Role → I → Prop) (lost : ¬ Wins e o) (n : ℕ)
    (start : (Index e → Bool) → S) (query : S → Option (Index e))
    (advance : S → Index e → Bool → S) (pub : Index e → Bool) (tr : List (Index e × Bool))
    (covered : ∀ k v, (k,v) ∈ tr → o k.val.1 k.val.2.1) (b : Bool) :
    {s : Coins e // (view o b s).1 = pub ∧ walk query advance s.2.2 n (start pub) = tr} ≃
    {s : Coins e // (view o (!b) s).1 = pub ∧ walk query advance s.2.2 n (start pub) = tr} := by
  classical
  let m := (missing_role e o lost).choose
  have hm := (missing_role e o lost).choose_spec
  have go (d : Bool) (s : Coins e) (h : (view o d s).1 = pub ∧
      walk query advance s.2.2 n (start pub) = tr) :
      (view o (!d) (toggle m s)).1 = pub ∧
      walk query advance (toggle m s).2.2 n (start pub) = tr := by
    have hv := view_toggle hm d s
    refine ⟨(congrArg Prod.fst hv).trans h.1, (replay _ _ _ _ _ _ ?_).trans h.2⟩
    intro k v hk
    exact congrFun (congrArg Prod.snd hv) ⟨k, covered k v (h.2 ▸ hk)⟩
  exact {
    toFun := fun s ↦ ⟨toggle m s.val, go b s.val s.property⟩
    invFun := fun s ↦ ⟨toggle m s.val, by simpa using go (!b) s.val s.property⟩
    left_inv := fun s ↦ Subtype.ext (toggle_twice m s.val)
    right_inv := fun s ↦ Subtype.ext (toggle_twice m s.val) }

end AdvancedEncryption.WE.SeparatingTerminal
