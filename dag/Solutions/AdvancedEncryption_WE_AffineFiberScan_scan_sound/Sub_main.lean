import Definitions.Def_AffineFiberScan

open AdvancedEncryption.WE.AffineFiberScan

theorem solution {W D : Type} (d : Domain W D) (w : W) (gates : SigabaNeo.GateList)
    (input : List Bool) (labels : List D)
    (h : List.Forall₂ (fun a x => d.holds a x w) labels input) :
    d.holds (gates.foldl (advance d) (d.one :: labels, d.one)).2
      (SigabaNeo.evalGates (input, gates)) w := by
  let R := fun a x => d.holds a x w
  have get : ∀ {as bs}, List.Forall₂ R as bs → ∀ i,
      R (as.getD i d.one) (bs.getD i true) := by
    intro as bs hr
    induction hr with
    | nil => intro i; cases i <;> exact d.one_true w
    | cons hab _ ih =>
      intro i
      cases i with
      | zero => exact hab
      | succ j => exact ih j
  have snoc : ∀ {as bs}, List.Forall₂ R as bs → ∀ {a b}, R a b →
      List.Forall₂ R (as ++ [a]) (bs ++ [b]) := by
    intro as bs hr
    induction hr with
    | nil => intro a b hab; exact .cons hab .nil
    | cons h _ ih => intro a b hab; exact .cons h (ih hab)
  have go : ∀ (gs : SigabaNeo.GateList) (as : List D × D) (bs : List Bool × Bool),
      List.Forall₂ R as.1 bs.1 → R as.2 bs.2 →
      R (gs.foldl (advance d) as).2 (gs.foldl SigabaNeo.estep bs).2 := by
    intro gs
    induction gs with
    | nil => intro as bs _ hb; exact hb
    | cons g gs ih =>
      intro as bs hr _
      have hv := d.transfer_sound _ _ _ _ w (get hr g.1) (get hr g.2)
      exact ih _ _ (snoc hr hv) hv
  exact go gates _ _ (.cons (d.one_true w) h) (d.one_true w)
