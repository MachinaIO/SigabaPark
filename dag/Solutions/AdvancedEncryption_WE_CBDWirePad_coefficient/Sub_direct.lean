import SigabaNeoStd.Lattices.RingLWE
open SigabaNeo.Lattices Cslib.Probability

theorem solution : ModuleLWE.coeffLaw 256 (.cbd 1) =
    (Cslib.Probability.PMF.uniformOfFintype (Bool × Bool)).map
      (fun ab => ((if ab.1 then (1:ZMod 256) else 0) -
                  (if ab.2 then (1:ZMod 256) else 0))) := by
  let e : ((Fin 1 → Bool) × (Fin 1 → Bool)) ≃ (Bool × Bool) :=
    (Equiv.funUnique (Fin 1) Bool).prodCongr (Equiv.funUnique (Fin 1) Bool)
  unfold ModuleLWE.coeffLaw
  rw [← Cslib.Probability.PMF.uniformOfFintype_map_equiv e, _root_.PMF.map_comp]
  apply congrArg (fun g => _root_.PMF.map g _)
  funext ab
  have all : (Finset.univ : Finset (Fin 1)) = {0} := by decide
  simp only [all, Function.comp_apply]
  change _ = ((if ab.1 0 then (1:ZMod 256) else 0) - (if ab.2 0 then (1:ZMod 256) else 0))
  cases h : ab.1 0 <;> cases j : ab.2 0 <;> simp [Finset.filter_singleton,h,j]
