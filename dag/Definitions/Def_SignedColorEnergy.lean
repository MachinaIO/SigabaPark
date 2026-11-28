import Mathlib
import SigabaNeoStd.Machines.Gates

namespace SignedColorEnergy

inductive Color | red | green | blue deriving DecidableEq
structure Marginal where
  x : ℤ
  y : ℤ
  z : ℤ
  deriving DecidableEq

structure Table where
  rg : ℤ
  rb : ℤ
  gr : ℤ
  gb : ℤ
  br : ℤ
  bg : ℤ
  deriving DecidableEq

def Marginal.mass (v : Marginal) := v.x + v.y + v.z
def Marginal.energy (v : Marginal) := v.x^2 + v.y^2 + v.z^2
def Marginal.round (v : Marginal) : Color :=
  if v.x%2=1 then .red else if v.y%2=1 then .green else .blue

def Table.left (t : Table) : Marginal := ⟨t.rg+t.rb,t.gr+t.gb,t.br+t.bg⟩
def Table.right (t : Table) : Marginal := ⟨t.gr+t.br,t.rg+t.bg,t.rb+t.gb⟩
def Table.energy (t : Table) := t.rg^2+t.rb^2+t.gr^2+t.gb^2+t.br^2+t.bg^2

def unit : Color → Marginal
  | .red => ⟨1,0,0⟩
  | .green => ⟨0,1,0⟩
  | .blue => ⟨0,0,1⟩

def lift : Color → Color → Table
  | .red,.red => ⟨1,0,0,0,1,-1⟩
  | .red,.green => ⟨1,0,0,0,0,0⟩
  | .red,.blue => ⟨0,1,0,0,0,0⟩
  | .green,.red => ⟨0,0,1,0,0,0⟩
  | .green,.green => ⟨1,-1,0,1,0,0⟩
  | .green,.blue => ⟨0,0,0,1,0,0⟩
  | .blue,.red => ⟨0,0,0,0,1,0⟩
  | .blue,.green => ⟨0,0,0,0,0,1⟩
  | .blue,.blue => ⟨0,0,-1,1,1,0⟩

def price (a b : Color) : ℤ := if a=b then 3 else 1

theorem square_parity (a : ℤ) : a%2 ≤ a^2 := by
  by_cases h : a=0
  · simp [h]
  · have hp : 0 < a^2 := sq_pos_of_ne_zero h
    omega

theorem vertex_lower (v : Marginal) (h : v.mass%2=1) : 1 ≤ v.energy := by
  rcases v with ⟨a,b,c⟩
  change (a+b+c)%2=1 at h
  change 1 ≤ a^2+b^2+c^2
  have ha:=square_parity a
  have hb:=square_parity b
  have hc:=square_parity c
  omega

theorem edge_lower (t : Table) (h : t.left.mass%2=1) :
    price t.left.round t.right.round ≤ t.energy := by
  rcases t with ⟨a,b,c,d,e,f⟩
  change ((a+b)+(c+d)+(e+f))%2=1 at h
  simp only [price, Marginal.round, Table.left, Table.right, Table.energy]
  have ha:=square_parity a
  have hb:=square_parity b
  have hc:=square_parity c
  have hd:=square_parity d
  have he:=square_parity e
  have hf:=square_parity f
  simp only [Int.add_emod a b 2, Int.add_emod c d 2, Int.add_emod c e 2, Int.add_emod a f 2]
  have par (x : ℤ) : x%2=0 ∨ x%2=1 := by omega
  have hmod : (a%2+b%2+c%2+d%2+e%2+f%2)%2=1 := by omega
  rcases par a with ha0|ha0 <;> rcases par b with hb0|hb0 <;>
    rcases par c with hc0|hc0 <;> rcases par d with hd0|hd0 <;>
    rcases par e with he0|he0 <;> rcases par f with hf0|hf0 <;>
    simp only [ha0,hb0,hc0,hd0,he0,hf0] at * <;> norm_num at hmod <;> norm_num <;> omega

theorem lift_spec (a b : Color) :
    (lift a b).left=unit a ∧ (lift a b).right=unit b ∧
    (lift a b).energy=price a b := by
  cases a <;> cases b <;> decide

def feasible {n m : ℕ} (l r : Fin m → Fin n) (v : Fin n → Marginal)
    (t : Fin m → Table) := (∀ i, (v i).mass=1) ∧
    (∀ j, (t j).left=v (l j) ∧ (t j).right=v (r j))
def energy {n m : ℕ} (v : Fin n → Marginal) (t : Fin m → Table) : ℤ :=
  (∑ i, (v i).energy) + ∑ j, (t j).energy
def objective {n m : ℕ} (l r : Fin m → Fin n) (c : Fin n → Color) : ℤ :=
  n + ∑ j, price (c (l j)) (c (r j))
def bitColor (b : Bool) : Fin 3 := if b then 1 else 0

def tripleGadget (x y z : Bool) : Prop := ∃ a b c : Fin 3,
  a ≠ b ∧ b ≠ c ∧ c ≠ a ∧ a ≠ bitColor x ∧ b ≠ bitColor y ∧ c ≠ bitColor z

instance gadgetDecidable (x y z : Bool) : Decidable (tripleGadget x y z) := by
  unfold tripleGadget
  infer_instance
def sameParity (u v : Marginal) : Prop :=
  u.x%2=v.x%2 ∧ u.y%2=v.y%2 ∧ u.z%2=v.z%2

theorem round_congr {u v : Marginal} (h : sameParity u v) : u.round=v.round := by
  simp only [Marginal.round, h.1,h.2.1]

theorem mass_congr {u v : Marginal} (h : sameParity u v) : u.mass%2=v.mass%2 := by
  rcases h with ⟨hx,hy,hz⟩
  unfold Marginal.mass
  omega

def parityFeasible {n m : ℕ} (l r : Fin m → Fin n) (v : Fin n → Marginal)
    (t : Fin m → Table) : Prop := (∀ i, (v i).mass%2=1) ∧
    (∀ j, sameParity (t j).left (v (l j)) ∧ sameParity (t j).right (v (r j)))

def parityLift (a b : Color) : Table :=
  let t := lift a b
  ⟨t.rg%2,t.rb%2,t.gr%2,t.gb%2,t.br%2,t.bg%2⟩

theorem parity_lift_spec (a b : Color) :
    sameParity (parityLift a b).left (unit a) ∧ sameParity (parityLift a b).right (unit b) ∧
    (parityLift a b).energy=price a b := by
  cases a <;> cases b <;> unfold sameParity <;> decide

def localOK (x y z : Bool) : Prop :=
  tripleGadget x z false ∧ tripleGadget y z false ∧ tripleGadget x y z

def accepted (s : List Bool × Bool) : List (ℕ × ℕ) → Prop
  | [] => s.2 = true
  | (a,b)::gs => ∃ z, localOK (s.1.getD a true) (s.1.getD b true) z ∧
      accepted (s.1 ++ [z], z) gs
end SignedColorEnergy
