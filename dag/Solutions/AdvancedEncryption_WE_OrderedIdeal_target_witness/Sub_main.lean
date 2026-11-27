import Definitions.Def_OrderedNand
import Theorems.Thm_AdvancedEncryption_WE_OrderedIdeal_clean_extends
import Theorems.Thm_AdvancedEncryption_WE_OrderedIdeal_log_sound
import Theorems.Thm_AdvancedEncryption_WE_OrderedIdeal_issued_valid

open OrderedNand SigabaNeo

theorem solution {n : Nat} (pre : GateList) (g : Nat × Nat) {S : Tags (Fin n)}
    (d : Derives (Inputs n) (issued (n+1) (pre++[g])) (.wire (n+1+pre.length) true) S)
    (clean : consistent S) : ∃ x : Fin n → Bool, evalGates (List.ofFn x,pre++[g]) = true := by
  let gs := pre++[g]
  let V := fun (x : Fin n → Bool) => val (gs.foldl estep (true::List.ofFn x,true)).1
  have prefWitness (ds : GateList) (st : List Bool × Bool) :
      ∃ tail, (ds.foldl estep st).1 = st.1 ++ tail := by
    induction ds generalizing st with
    | nil => exact ⟨[],by simp⟩
    | cons a ds ih =>
      obtain ⟨t,hh⟩ := ih (estep st a)
      exact ⟨_::t,by simpa [estep,List.append_assoc] using hh⟩
  have init : ∀ w T x, Inputs n w T → extendsT x T → live (V x) w := by
    intro w T x hw hx
    obtain ⟨tail,h⟩ := prefWitness gs (true::List.ofFn x,true)
    cases hw with
    | dummy => trivial
    | const => change val _ 0 = true; dsimp [val];rw [h];rfl
    | lit i b =>
      change val _ (i.val+1) = b
      have hi : i.val+1 < (true::List.ofFn x).length := by simp
      have lit := hx i b (by simp)
      dsimp [val];rw [h,List.getD_append _ _ _ _ hi]
      simpa [List.getD_eq_getElem _ _ hi] using lit
  obtain ⟨x,hx⟩ := AdvancedEncryption.WE.OrderedIdeal.clean_extends S clean
  have edge : ∀ a b c x, issued (n+1) gs a b c → live (V x) a → live (V x) b → live (V x) c := by
    intro a b c x he
    apply AdvancedEncryption.WE.OrderedIdeal.issued_valid gs (List.ofFn x) true a b c
    simpa using he
  have out := AdvancedEncryption.WE.OrderedIdeal.log_sound (fun x w => live (V x) w) init edge d x hx
  refine ⟨x,?_⟩
  have len (ds : GateList) (s : List Bool × Bool) : (ds.foldl estep s).1.length = s.1.length+ds.length := by
    induction ds generalizing s with
    | nil => simp
    | cons a ds ih => simp [ih,estep];omega
  let st := pre.foldl estep (true::List.ofFn x,true)
  have hs : st.1.length = n+1+pre.length := by simpa [st] using len pre (true::List.ofFn x,true)
  let z := !(val st.1 g.1 && val st.1 g.2)
  change ((gs.foldl estep (true::List.ofFn x,true)).1.getD (n+1+pre.length) true) = true at out
  simp only [gs,List.foldl_append,List.foldl_cons,List.foldl_nil] at out
  change (st.1++[z]).getD (n+1+pre.length) true = true at out
  rw [←hs,List.getD_append_right _ _ _ _ (by rfl)] at out
  simpa [evalGates,List.foldl_append,estep,st,z,val] using out
