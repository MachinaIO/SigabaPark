import Definitions.Def_WE_SeparatingTerminal
import Mathlib.Algebra.QuadraticAlgebra.Basic
import SigabaNeoStd.Machines.FromPolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.Transducer
import Mathlib.Data.Fintype.Card

namespace SeparatingTerminalMachine

open SigabaNeo Turing

abbrev Registers := Bool × Bool × Bool
abbrev Op := Fin 7

/-- 0 loads the message; 1 and 2 load the fresh share coins. Remaining instructions emit. -/
def update (a : Op) (x : Bool) (s : Registers) : Registers :=
  if a = 0 then (x,s.2) else if a = 1 then (s.1,x,s.2.2)
  else if a = 2 then (s.1,s.2.1,x) else s

def emit (a : Op) (x : Bool) (s : Registers) : List Bool :=
  if a.val < 3 then [] else
  [if a = 3 then s.2.1 ^^ x else if a = 4 then s.2.2 ^^ x
   else if a = 5 then ((s.1 ^^ s.2.1) ^^ s.2.2) ^^ x else false]

def eval : List (Op × Bool) → Registers → List Bool
  | [], _ => []
  | (c,x) :: l, s => emit c x s ++ eval l (update c x s)

abbrev Q (n : ℕ) := Fin (n + 1) × Registers

/-- The opcodes are fixed in the transition table. The input contains only their operands. -/
def reader (plan : List Op) : MultiTapeTM.Transducer Bool (Q plan.length) where
  q₀ := (0,false,false,false)
  step q x :=
    let a := plan[q.1.val]?.getD 6
    ((⟨min (q.1.val + 1) plan.length, by omega⟩, update a x q.2), emit a x q.2)
  final _ := []
  length_step_le _ _ := by simp [emit]; split <;> simp
  length_final_le _ := by decide

theorem run_suffix (plan : List Op) (pre : List Op) (l : List (Op × Bool))
    (hp : plan = pre ++ l.map Prod.fst) (i : Fin (plan.length+1)) (hi : i.val = pre.length)
    (s : Registers) : (reader plan).run (i,s) (l.map Prod.snd) = eval l s := by
  induction l generalizing pre i s with
  | nil => rfl
  | cons h l ih =>
    obtain ⟨a,x⟩ := h
    have hget : plan[i.val]? = some a := by simp [hp, hi]
    have hlt : pre.length < plan.length := by simp [hp]
    simp only [List.map_cons, MultiTapeTM.Transducer.run_cons, reader, hget, Option.getD_some,
      eval]
    congr 1
    apply ih (pre ++ [a])
    · simpa [List.append_assoc] using hp
    · simp [hi, Nat.min_eq_left (by omega : pre.length + 1 ≤ plan.length)]

def clock (n : ℕ) := 2 * n + 3

noncomputable def machine (plan : List Op) : Machine :=
  Machine.ofTM (reader plan).toTM (clock plan.length)

theorem run_machine (plan : List Op) (l : List (Op × Bool)) (hp : plan = l.map Prod.fst) :
    (machine plan).run (l.map Prod.snd) = PMF.pure (eval l (false,false,false)) := by
  rw [machine, Machine.run_ofTM]
  congr 1
  let w := l.map Prod.snd
  have hc := (reader plan).computesInTimeAndSpace_toTM w
  obtain ⟨⟨u, hu, hout⟩, htime, _⟩ := hc
  have hlen : w.length = plan.length := by simp [w,hp]
  have hh := MultiTapeTM.runsInTime_iff_halted.mp htime
  have hclock : clock plan.length = 2 * w.length + 3 := by rw [clock,hlen]
  rw [hclock]
  have hrun : ((reader plan).toTM.runFrom ((reader plan).toTM.initCfg w)
      (2 * w.length + 3)).output = (reader plan).run (reader plan).q₀ w := by
    rcases le_total u (2 * w.length + 3) with le | le
    · rw [MultiTapeTM.runFrom_eq_of_halt _ _ le hu]; exact hout
    · rw [← MultiTapeTM.runFrom_eq_of_halt _ _ le hh]; exact hout
  exact hrun.trans (run_suffix plan [] l (by simpa using hp) 0 rfl _)

theorem cost_machine (plan : List Op) :
    (machine plan).cost = clock plan.length +
    6 * ((plan.length + 1) * 48) * (4 + Nat.size ((plan.length + 1) * 48)) := by
  have hs : (machine plan).states = (plan.length+1)*48 := by
    change Nat.card (Q plan.length × Option Bool × Bool) = _
    simp [Q, Registers, Nat.card_eq_fintype_card, Fintype.card_option]
    omega
  unfold Machine.cost Machine.descLen Machine.entryBits
  rw [hs]
  change clock _ + 6 * _ * 3^0 * 3^0 * (4 + 4*0 + 4*0 + Nat.size 0 + Nat.size _) = _
  simp [Nat.size_zero]

/-- Source-role opcodes and an ineligible dummy. -/
def correction (role : Fin 3) (ok : Bool) : Op :=
  if ok then ⟨3 + role.val, by omega⟩ else 6

/-- Registers persist throughout the pad section. -/
theorem eval_pads {X : Type} (xs : List X) (role : X → Fin 3) (ok pad : X → Bool)
    (tail : List (Op × Bool)) (s : Registers) :
    eval ((xs.map fun i ↦ (correction (role i) (ok i), pad i)) ++ tail) s =
    (xs.flatMap fun i ↦ emit (correction (role i) (ok i)) (pad i) s) ++ eval tail s := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    have hu : update (correction (role i) (ok i)) (pad i) s = s := by
      generalize role i = r
      cases ok i <;> fin_cases r <;> rfl
    simp [eval, hu, ih, List.append_assoc]

/-- Each term reads two fresh coins and then the pad bits of its slots, in public order. -/
def block {X T : Type} (slots : List X) (role : X → Fin 3) (ok : T → X → Bool)
    (u v : T → Bool) (pad : T → X → Bool) (t : T) : List (Op × Bool) :=
  (1,u t) :: (2,v t) :: slots.map fun i ↦ (correction (role i) (ok t i), pad t i)

def packet {X T : Type} (terms : List T) (slots : List X) (role : X → Fin 3)
    (ok : T → X → Bool) (b : Bool) (u v : T → Bool) (pad : T → X → Bool) :=
  (0,b) :: terms.flatMap (block slots role ok u v pad)

def planFor {X T : Type} (terms : List T) (slots : List X) (role : X → Fin 3)
    (ok : T → X → Bool) : List Op :=
  0 :: terms.flatMap fun t ↦ 1 :: 2 :: slots.map fun i ↦ correction (role i) (ok t i)

theorem plan_packet {X T : Type} (ts : List T) (xs : List X) (role : X → Fin 3)
    (ok : T → X → Bool) (b : Bool) (u v : T → Bool) (pad : T → X → Bool) :
    planFor ts xs role ok = (packet ts xs role ok b u v pad).map Prod.fst := by
  simp [planFor, packet, block, List.map_flatMap, List.map_map, Function.comp_def]

theorem eval_blocks {X T : Type} (ts : List T) (xs : List X) (role : X → Fin 3)
    (ok : T → X → Bool) (u v : T → Bool) (pad : T → X → Bool) (s : Registers) :
    eval (ts.flatMap (block xs role ok u v pad)) s =
    ts.flatMap fun t ↦ xs.flatMap fun i ↦
      emit (correction (role i) (ok t i)) (pad t i) (s.1,u t,v t) := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.flatMap_cons, block, List.cons_append, eval]
    change eval ((xs.map _) ++ _) (s.1, u t, v t) = _
    rw [eval_pads, ih]

theorem output_packet {X T : Type} (ts : List T) (xs : List X) (role : X → Fin 3)
    (ok : T → X → Bool) (b : Bool) (u v : T → Bool) (pad : T → X → Bool) :
    (machine (planFor ts xs role ok)).run ((packet ts xs role ok b u v pad).map Prod.snd) =
    PMF.pure (ts.flatMap fun t ↦ xs.flatMap fun i ↦
      emit (correction (role i) (ok t i)) (pad t i) (b,u t,v t)) := by
  rw [run_machine _ _ (plan_packet ..)]
  congr 1
  exact eval_blocks ts xs role ok u v pad (b,false,false)

theorem plan_length {X T : Type} (ts : List T) (xs : List X) (role : X → Fin 3)
    (ok : T → X → Bool) :
    (planFor ts xs role ok).length = 1 + ts.length * (2 + xs.length) := by
  unfold planFor
  induction ts with
  | nil => simp
  | cons t ts ih =>
    simp only [List.flatMap_cons, List.length_cons, List.length_append, List.length_map] at *
    rw [Nat.add_mul]
    omega

theorem dense_cost {X T : Type} (ts : List T) (xs : List X) (role : X → Fin 3)
    (ok : T → X → Bool) (ht : ts.length = 63) (hx : xs.length = 12672) :
    (machine (planFor ts xs role ok)).cost = 6900325889 := by
  rw [cost_machine, plan_length, ht, hx]
  decide

open AdvancedEncryption.WE.SeparatingTerminal

abbrev F9 := QuadraticAlgebra (ZMod 3) (-1) 0

local instance : Fact (∀ r : ZMod 3, r ^ 2 ≠ -1 + 0 * r) := ⟨by decide⟩

/-- The low ternary digit is the real coefficient of the quadratic element. -/
def digits : Fin 9 ≃ F9 :=
  finProdFinEquiv.symm.trans ((Equiv.prodComm (Fin 3) (Fin 3)).trans
    (((ZMod.finEquiv 3).toEquiv.prodCongr (ZMod.finEquiv 3).toEquiv).trans
      (QuadraticAlgebra.equivProd (-1 : ZMod 3) 0).symm))

def points : Fin 7 ↪ F9 := (Fin.castLEEmb (by decide : 7 ≤ 9)).trans digits.toEmbedding

/-- Direct arithmetic over pairs of residues; no root choice or polynomial object is evaluated. -/
def word (i : Fin 4224) (x : Fin 7) : F9 :=
  ∑ k : Fin 4, digits (finFunctionFinEquiv.symm (Fin.castLE (by decide : 4224 ≤ 9^4) i) k) *
    (points x)^(k : ℕ)

theorem word_eq (i : Fin 4224) (x : Fin 7) :
    (labels digits i).val.eval (points x) = word i x := by
  rw [Polynomial.eval_eq_sum_degreeLTEquiv (labels digits i).property]
  simp [word, labels]

abbrev Slot := Fin 3 × Fin 4224
abbrev Term := Fin 7 × Fin 9

def allow (t : Term) (s : Slot) : Bool :=
  if s.1 = 2 then decide (word s.2 t.1 = digits t.2)
  else decide (word s.2 t.1 ≠ digits t.2)

theorem allow_iff (t : Term) (s : Slot) :
    allow t s = true ↔ eligible digits points s.1 s.2 (t.1,digits t.2) := by
  simp [allow, eligible, word_eq]

def terms : List Term := (List.finRange 63).map finProdFinEquiv.symm

def slots : List Slot := (List.finRange 12672).map finProdFinEquiv.symm

def fixedPlan := planFor terms slots Prod.fst allow

noncomputable def encCorrection : Machine := machine fixedPlan

theorem encCorrection_cost : encCorrection.cost = 6900325889 :=
  dense_cost terms slots Prod.fst allow (by simp [terms]) (by simp [slots])

theorem emit_correct (r : Fin 3) (ok b u v p : Bool) :
    emit (correction r ok) p (b,u,v) =
    [if ok then roleShare b u v r ^^ p else false] := by
  fin_cases r <;> cases ok <;> rfl

theorem encCorrection_run (b : Bool) (u v : Term → Bool) (pad : Term → Slot → Bool) :
    encCorrection.run ((packet terms slots Prod.fst allow b u v pad).map Prod.snd) =
      PMF.pure (terms.flatMap fun t ↦ slots.map fun s ↦
        if allow t s then roleShare b (u t) (v t) s.1 ^^ pad t s else false) := by
  simpa only [encCorrection, fixedPlan, emit_correct, ← List.map_eq_flatMap] using
    output_packet terms slots Prod.fst allow b u v pad

end SeparatingTerminalMachine
