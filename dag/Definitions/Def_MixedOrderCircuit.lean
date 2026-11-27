import SigabaNeoStd.Machines.Gates
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import Mathlib.Tactic.Ring
import Mathlib.Data.List.Nodup

namespace MixedOrderCircuit
open SigabaNeo
variable {α : Type}

inductive E where
  | bit (v : Bool)
  | atom (i : Nat)
  | neg (a : E)
  | gate (a b : E)

def E.val (x : Nat → Bool) : E → Bool
  | .bit v => v
  | .atom i => x i
  | .neg a => !(a.val x)
  | .gate a b => !(a.val x && b.val x)

def E.vars : E → List Nat
  | .bit _ => []
  | .atom i => [i]
  | .neg a => a.vars
  | .gate a b => a.vars ++ b.vars

def flip : E → E
  | .bit v => .bit (!v)
  | .neg a => a
  | a => .neg a

@[simp] theorem val_flip (x : Nat → Bool) (a : E) : (flip a).val x = !a.val x := by
  cases a <;> simp [flip,E.val]

def merge : E → E → E
  | .bit false, _ | _, .bit false => .bit true
  | .bit true, b => flip b
  | a, .bit true => flip a
  | a, b => .gate a b

theorem val_merge (x : Nat → Bool) (a b : E) :
    (merge a b).val x = !(a.val x && b.val x) := by
  cases a <;> cases b <;> simp [merge,E.val,flip] <;> split <;> simp_all [E.val]

def sstep (s : List E × E) (g : Nat × Nat) : List E × E :=
  let a := s.1.getD g.1 (.bit true)
  let b := s.1.getD g.2 (.bit true)
  let v := if g.1 = g.2 then flip a else merge a b
  (s.1 ++ [v],v)

def interp (x : Nat → Bool) (s : List E × E) :=
  (s.1.map (E.val x),s.2.val x)

theorem getD_val (x : Nat → Bool) (l : List E) (i : Nat) :
    (l.map (E.val x)).getD i true = (l.getD i (.bit true)).val x := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases l[i]? <;> rfl

theorem step_sound (x : Nat → Bool) (s : List E × E) (g : Nat × Nat) :
    interp x (sstep s g) = estep (interp x s) g := by
  simp only [sstep,estep,interp,getD_val,List.map_append,List.map_cons,List.map_nil]
  by_cases h : g.1 = g.2 <;> simp [h,val_merge]

theorem fold_sound (x : Nat → Bool) (s : List E × E) (gs : GateList) :
    interp x (gs.foldl sstep s) = gs.foldl estep (interp x s) := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih => simp only [List.foldl_cons, ih, step_sound]

/-- Public address bits occupy the suffix of the primary inputs. -/
def compile (n : Nat) (addr : List Bool) (gs : GateList) : E :=
  (gs.foldl sstep (.bit true :: ((List.range n).map E.atom ++ addr.map E.bit),.bit true)).2

theorem compile_sound (n : Nat) (addr : List Bool) (gs : GateList) (x : Nat → Bool) :
    (compile n addr gs).val x = evalGates ((List.range n).map x ++ addr,gs) := by
  have h := congrArg Prod.snd (fold_sound x
    (.bit true :: ((List.range n).map E.atom ++ addr.map E.bit),.bit true) gs)
  simpa [compile,interp,evalGates,List.map_map,Function.comp_def,E.val] using h

def E.possible (v : Bool) : E → Bool
  | .bit b => b == v
  | .atom _ => true
  | .neg a => a.possible (!v)
  | .gate a b => if v then a.possible false || b.possible false
                  else a.possible true && b.possible true

theorem E.local_val {x y : Nat → Bool} (a : E) (h : ∀ i ∈ a.vars, x i = y i) :
    a.val x = a.val y := by
  induction a with
  | bit => rfl
  | atom i => exact h i (by simp [E.vars])
  | neg a ih => simp [E.val,ih h]
  | gate a b ia ib =>
    simp [E.val,ia (fun i hi ↦ h i (by simp [E.vars,hi])),
      ib (fun i hi ↦ h i (by simp [E.vars,hi]))]

theorem E.attain (a : E) (hw : a.vars.Nodup) (v : Bool) :
    a.possible v = true ↔ ∃ x, a.val x = v := by
  induction a generalizing v with
  | bit b => simp [E.possible,E.val]
  | atom i => exact ⟨fun _ ↦ ⟨fun _ ↦ v,rfl⟩,fun _ ↦ rfl⟩
  | neg a ih =>
    rw [E.possible,ih hw]
    cases v <;> simp [E.val]
  | gate a b ia ib =>
    obtain ⟨ha,hb,hd⟩ := List.nodup_append'.mp hw
    cases v
    · simp only [E.possible, Bool.false_eq_true, ↓reduceIte,Bool.and_eq_true,
        ia ha,ib hb,E.val,Bool.not_eq_false']
      constructor
      · rintro ⟨⟨x,hx⟩,⟨y,hy⟩⟩
        let z := fun i ↦ if i ∈ a.vars then x i else y i
        refine ⟨z, ?_, ?_⟩
        · rw [← hx]; apply a.local_val; intro i hi; simp [z,hi]
        · rw [← hy]; apply b.local_val; intro i hi
          have hn : i ∉ a.vars := fun hj ↦ List.disjoint_left.mp hd hj hi
          simp [z,hn]
      · rintro ⟨x,hx,hy⟩; exact ⟨⟨x,hx⟩,⟨x,hy⟩⟩
    · simp [E.possible,ia ha,ib hb,E.val,exists_or]

/-- A recognized YES emits the message. A recognized NO emits zero. Failure is delegated. -/
def issue (n : Nat) (as : List (List Bool)) (gs : GateList) (msg : Bool) : Option Bool :=
  let es := as.map (fun a ↦ compile n a gs)
  if es.all (fun e ↦ decide e.vars.Nodup) then some (msg && es.any (E.possible true)) else none

theorem issue_eq (n : Nat) (as : List (List Bool)) (gs : GateList) (msg : Bool)
    (h : ∀ a ∈ as, (compile n a gs).vars.Nodup) :
    issue n as gs msg = some (msg && (as.map (fun a ↦ compile n a gs)).any (E.possible true)) := by
  have h' : (as.map (fun a ↦ compile n a gs)).all (fun e ↦ decide e.vars.Nodup) = true := by
    apply List.all_eq_true.mpr
    intro e he
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp he
    simpa using h a ha
  simp only [issue,h',ite_true]

theorem found_iff (n : Nat) (as : List (List Bool)) (gs : GateList)
    (h : ∀ a ∈ as, (compile n a gs).vars.Nodup) :
    (as.map (fun a ↦ compile n a gs)).any (E.possible true) = true ↔
      ∃ a ∈ as, ∃ x, evalGates ((List.range n).map x ++ a,gs) = true := by
  simp only [List.any_map,List.any_eq_true,Function.comp_apply]
  constructor
  · rintro ⟨a,ha,hp⟩
    obtain ⟨x,hx⟩ := (E.attain _ (h a ha) true).mp hp
    exact ⟨a,ha,x, (compile_sound n a gs x) ▸ hx⟩
  · rintro ⟨a,ha,x,hx⟩
    exact ⟨a,ha,(E.attain _ (h a ha) true).mpr ⟨x,(compile_sound n a gs x).trans hx⟩⟩



def E.nodes : E → Nat
  | .bit _ | .atom _ => 1
  | .neg a => 1 + a.nodes
  | .gate a b => 1 + a.nodes + b.nodes

/-- Reject an oversized intermediate before processing another gate. -/
def boundedFold (B : Nat) (s : List E × E) : GateList → Option (List E × E)
  | [] => some s
  | g :: gs =>
    let next := sstep s g
    if next.2.nodes ≤ B then boundedFold B next gs else none

theorem bounded_sound (B : Nat) (s out : List E × E) (gs : GateList)
    (h : boundedFold B s gs = some out) : gs.foldl sstep s = out := by
  induction gs generalizing s with
  | nil => simpa [boundedFold] using h
  | cons g gs ih =>
    simp only [boundedFold] at h
    split at h
    · exact ih _ h
    · contradiction

def checked (B n : Nat) (addr : List Bool) (gs : GateList) : Option Bool := do
  let r ← boundedFold B
    (.bit true :: ((List.range n).map E.atom ++ addr.map E.bit),.bit true) gs
  if r.2.vars.Nodup then some (r.2.possible true) else none

theorem checked_sound {B n : Nat} {addr : List Bool} {gs : GateList} {v : Bool}
    (h : checked B n addr gs = some v) :
    (v = true ↔ ∃ x, evalGates ((List.range n).map x ++ addr,gs) = true) := by
  unfold checked at h
  cases hh : boundedFold B
    (.bit true :: ((List.range n).map E.atom ++ addr.map E.bit),.bit true) gs with
  | none => simp [hh] at h
  | some out =>
    simp [hh] at h
    obtain ⟨hn, hv⟩ := h
    have he : compile n addr gs = out.2 := congrArg Prod.snd (bounded_sound _ _ _ _ hh)
    subst v
    rw [E.attain _ hn, ← he]
    simp only [compile_sound]

def addresses : Nat → List (List Bool)
  | 0 => [[]]
  | k+1 => (addresses k).map (false :: ·) ++ (addresses k).map (true :: ·)

theorem mem_addresses (a : List Bool) (k : Nat) : a ∈ addresses k ↔ a.length = k := by
  induction k generalizing a with
  | zero => simp [addresses]
  | succ k ih => cases a with
    | nil => simp [addresses]
    | cons b a => cases b <;> simp [addresses,ih]

open Turing.MultiTapeTM

def gateDecoder := Decoder.list (Decoder.pair Decoder.unary Decoder.unary)


def collect (f : α → Option Bool) : List α → Option Bool
  | [] => some false
  | i :: is => do
    let a ← f i
    let b ← collect f is
    return a || b

theorem collect_sound {f : α → Option Bool} {P : α → Prop}
    (hf : ∀ a v, f a = some v → (v = true ↔ P a)) (xs : List α) (v : Bool)
    (h : collect f xs = some v) : v = true ↔ ∃ a ∈ xs, P a := by
  induction xs generalizing v with
  | nil => cases v <;> simp_all [collect]
  | cons a xs ih =>
    cases ha : f a with
    | none => simp [collect,ha] at h
    | some b =>
      cases hc : collect f xs with
      | none => simp [collect,ha,hc] at h
      | some c =>
        simp [collect,ha,hc] at h
        subst v
        simp only [Bool.or_eq_true, hf a b ha, ih c hc, List.mem_cons]
        aesop

def decideWire (B n k : Nat) (word : List Bool) : Option Bool :=
  collect (fun a ↦ checked B n a (gateDecoder.decode word)) (addresses k)

theorem decode_gates (gs : GateList) : gateDecoder.decode (encGates gs) = gs :=
  gateDecoder.decode_enc gs

theorem decideWire_sound {B n k : Nat} {gs : GateList} {v : Bool}
    (h : decideWire B n k (encGates gs) = some v) :
    v = true ↔ ∃ a, a.length = k ∧ ∃ x, evalGates ((List.range n).map x ++ a,gs) = true := by
  simp only [decideWire,decode_gates] at h
  simpa only [mem_addresses] using collect_sound (P := fun a ↦
    ∃ x, evalGates ((List.range n).map x ++ a,gs) = true)
    (fun _ _ hc ↦ checked_sound hc) (addresses k) v h

def encryptWire (B n k : Nat) (word : List Bool) (b : Bool) : Option Bool :=
  (decideWire B n k word).map (fun yes ↦ yes && b)

theorem encryptWire_yes {B n k : Nat} {gs : GateList} {v : Bool}
    (h : decideWire B n k (encGates gs) = some v)
    (yes : ∃ a, a.length = k ∧ ∃ x, evalGates ((List.range n).map x ++ a,gs) = true)
    (b : Bool) : encryptWire B n k (encGates gs) b = some b := by
  have hv := (decideWire_sound h).mpr yes
  simp [encryptWire,h,hv]

theorem encryptWire_no {B n k : Nat} {gs : GateList} {v : Bool}
    (h : decideWire B n k (encGates gs) = some v)
    (no : ¬ ∃ a, a.length = k ∧ ∃ x, evalGates ((List.range n).map x ++ a,gs) = true)
    (b : Bool) : encryptWire B n k (encGates gs) b = some false := by
  have hn : v ≠ true := fun hv ↦ no ((decideWire_sound h).mp hv)
  have hv : v = false := by cases v <;> simp_all
  simp [encryptWire,h,hv]


theorem checked_nodup {B n : Nat} {a : List Bool} {gs : GateList} {v : Bool}
    (h : checked B n a gs = some v) : (compile n a gs).vars.Nodup := by
  unfold checked at h
  cases hh : boundedFold B
    (.bit true :: ((List.range n).map E.atom ++ a.map E.bit),.bit true) gs with
  | none => simp [hh] at h
  | some out =>
    simp [hh] at h
    have he : compile n a gs = out.2 := congrArg Prod.snd (bounded_sound _ _ _ _ hh)
    exact he ▸ h.1

theorem collect_total {f : α → Option Bool} (xs : List α) (v : Bool)
    (h : collect f xs = some v) : ∀ a ∈ xs, ∃ b, f a = some b := by
  induction xs generalizing v with
  | nil => simp
  | cons x xs ih =>
    cases hx : f x with
    | none => simp [collect,hx] at h
    | some b =>
      cases ht : collect f xs with
      | none => simp [collect,hx,ht] at h
      | some c =>
        intro a ha
        rcases List.mem_cons.mp ha with rfl|hm
        · exact ⟨b,hx⟩
        · exact ih c ht a hm

theorem checked_all {B n k : Nat} {gs : GateList} {v : Bool}
    (h : decideWire B n k (encGates gs) = some v) :
    ∀ a, a.length = k → (compile n a gs).vars.Nodup := by
  simp only [decideWire,decode_gates] at h
  intro a ha
  obtain ⟨_,hb⟩ := collect_total _ _ h a ((mem_addresses _ _).mpr ha)
  exact checked_nodup hb

theorem split_witness (n k : Nat) (gs : GateList) :
    (∃ a, a.length = k ∧ ∃ x, evalGates ((List.range n).map x ++ a,gs) = true) ↔
    ∃ w : Fin (n+k) → Bool, evalGates (List.ofFn w,gs) = true := by
  constructor
  · rintro ⟨a,ha,x,hx⟩
    let bits := (List.range n).map x ++ a
    have hl : bits.length = n+k := by simp [bits,ha]
    let w : Fin (n+k) → Bool := fun i ↦ bits[i.val]?.getD false
    refine ⟨w,?_⟩
    have hw : List.ofFn w = bits := by
      apply List.ext_getElem
      · simp [hl]
      · intro i hi hj; simp [w,List.getElem?_eq_getElem hj]
    simpa only [hw] using hx
  · rintro ⟨w,hw⟩
    let bits := List.ofFn w
    let x := fun (i : Nat) ↦ bits[i]?.getD false
    have hl : bits.length = n+k := by simp [bits]
    have hp : (List.range n).map x = bits.take n := by
      apply List.ext_getElem
      · simp [hl]
      · intro i hi hj
        have hn : i < n := by simpa using hi
        have hb : i < bits.length := by omega
        simp [x, List.getElem?_eq_getElem hb]
    refine ⟨bits.drop n,by simp [hl],x,?_⟩
    simpa only [hp,List.take_append_drop] using hw

section Extension
variable {K : Type} [CommRing K]

def E.ext (p : Nat → K) : E → K
  | .bit v => if v then 1 else 0
  | .atom i => p i
  | .neg a => 1 - a.ext p
  | .gate a b => 1 - a.ext p * b.ext p

theorem E.ext_cube (x : Nat → Bool) (a : E) :
    a.ext (fun i ↦ if x i then (1 : K) else 0) = if a.val x then 1 else 0 := by
  induction a with
  | bit | atom => rfl
  | neg a ih => cases h : a.val x <;> simp [E.ext,E.val,ih,h]
  | gate a b ia ib => cases h : a.val x <;> cases g : b.val x <;> simp [E.ext,E.val,ia,ib,h,g]

theorem E.local_ext {x y : Nat → K} (a : E) (h : ∀ i ∈ a.vars, x i = y i) :
    a.ext x = a.ext y := by
  induction a with
  | bit => rfl
  | atom i => exact h i (by simp [E.vars])
  | neg a ih => simp [E.ext,ih h]
  | gate a b ia ib =>
    simp [E.ext,ia (fun i hi ↦ h i (by simp [E.vars,hi])),
      ib (fun i hi ↦ h i (by simp [E.vars,hi]))]

theorem E.ext_unused (p : Nat → K) (i : Nat) (v : K) (a : E) (hi : i ∉ a.vars) :
    a.ext (Function.update p i v) = a.ext p := by
  apply a.local_ext
  intro j hj
  have hji : j ≠ i := by rintro rfl; exact hi hj
  exact Function.update_of_ne hji _ _

/-- Affineness in every named coordinate, on arbitrary field points. -/
theorem E.affine (a : E) (hw : a.vars.Nodup) (p : Nat → K) (i : Nat) (v : K) :
    a.ext (Function.update p i v) =
      (1-v) * a.ext (Function.update p i 0) + v * a.ext (Function.update p i 1) := by
  induction a with
  | bit b => cases b <;> simp [E.ext]
  | atom j =>
    by_cases h : j = i
    · subst j; simp [E.ext]
    · simp [E.ext,Function.update_of_ne h]; ring
  | neg a ih => simp only [E.ext]; rw [ih hw]; ring
  | gate a b ia ib =>
    obtain ⟨ha,hb,hd⟩ := List.nodup_append'.mp hw
    simp only [E.ext]
    by_cases h : i ∈ a.vars
    · have hn : i ∉ b.vars := fun hj ↦ List.disjoint_left.mp hd h hj
      simp only [b.ext_unused p i _ hn]; rw [ia ha]; ring
    · simp only [a.ext_unused p i _ h]; rw [ib hb]; ring

/-- Fold an address tree by Shannon interpolation, sharing data coordinates across its branches. -/
def muxEval (p : Nat → K) (leaf : List Bool → K) : Nat → List Bool → K
  | 0, a => leaf a
  | k+1, a => (1-p k) * muxEval p leaf k (false :: a) + p k * muxEval p leaf k (true :: a)

theorem mux_cube (z : Nat → Bool) (leaf : List Bool → K) (k : Nat) (a : List Bool) :
    muxEval (fun i ↦ if z i then 1 else 0) leaf k a = leaf ((List.range k).map z ++ a) := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih => cases h : z k <;> simp [muxEval,h,ih,List.range_succ,List.append_assoc]


theorem mux_linear (p : Nat → K) (f g : List Bool → K) (u v : K) (k : Nat) (a : List Bool) :
    muxEval p (fun s ↦ u * f s + v * g s) k a =
      u * muxEval p f k a + v * muxEval p g k a := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih => simp only [muxEval,ih]; ring

theorem mux_unused (p : Nat → K) (f : List Bool → K) (k i : Nat) (v : K) (a : List Bool)
    (hi : k ≤ i) : muxEval (Function.update p i v) f k a = muxEval p f k a := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    simp only [muxEval,Function.update_of_ne (show k ≠ i by omega),
      ih _ (show k ≤ i by omega)]

theorem mux_affine (p : Nat → K) (f : List Bool → K) (k i : Nat) (v : K) (a : List Bool) :
    muxEval (Function.update p i v) f k a =
    (1-v) * muxEval (Function.update p i 0) f k a + v * muxEval (Function.update p i 1) f k a := by
  induction k generalizing a with
  | zero => simp [muxEval]; ring
  | succ k ih =>
    by_cases h : k = i
    · subst i; simp [muxEval,mux_unused]
    · simp only [muxEval,Function.update_of_ne h]
      rw [ih (false :: a),ih (true :: a)]; ring

def whole (n k : Nat) (gs : GateList) (data addr : Nat → K) :=
  muxEval addr (fun a ↦ (compile n a gs).ext data) k []

theorem whole_cube (n k : Nat) (gs : GateList) (data addr : Nat → Bool) :
    whole n k gs (fun i ↦ if data i then (1 : K) else 0) (fun i ↦ if addr i then 1 else 0) =
    if evalGates ((List.range n).map data ++ (List.range k).map addr,gs) then 1 else 0 := by
  simp [whole,mux_cube,E.ext_cube,compile_sound]

theorem mux_congr (p : Nat → K) (f g : List Bool → K) (k : Nat) (a : List Bool)
    (h : ∀ s, s.length = k + a.length → f s = g s) : muxEval p f k a = muxEval p g k a := by
  induction k generalizing a with
  | zero => exact h _ (by simp)
  | succ k ih =>
    simp only [muxEval]
    rw [ih (false :: a) (fun s hs ↦ h s (by simp only [List.length_cons] at hs; omega)),
      ih (true :: a) (fun s hs ↦ h s (by simp only [List.length_cons] at hs; omega))]

theorem whole_data_affine (n k : Nat) (gs : GateList) (data addr : Nat → K) (i : Nat) (v : K)
    (h : ∀ a, a.length = k → (compile n a gs).vars.Nodup) :
    whole n k gs (Function.update data i v) addr =
    (1-v) * whole n k gs (Function.update data i 0) addr +
      v * whole n k gs (Function.update data i 1) addr := by
  unfold whole
  rw [← mux_linear]
  apply mux_congr
  intro s hs
  exact E.affine _ (h _ (by simpa using hs)) _ _ _

theorem whole_addr_affine (n k : Nat) (gs : GateList) (data addr : Nat → K) (i : Nat) (v : K) :
    whole n k gs data (Function.update addr i v) =
    (1-v) * whole n k gs data (Function.update addr i 0) +
      v * whole n k gs data (Function.update addr i 1) := mux_affine _ _ _ _ _ _

end Extension

end MixedOrderCircuit
