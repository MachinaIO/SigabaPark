import Mathlib.Logic.Function.Basic

theorem solution {F J K I : Type} (X : I → Type)
    (O A H : J → Type) (S : J → I → Type)
    (G : J → K → Type) (V : J → K → I → Type)
    (group : (j : J) → K → (∀ i, X i) → (O j × A j) × (∀ i, S j i))
    (outer : ∀ j, K → O j) (akey : ∀ j, K → A j)
    (tail : ∀ j i, X i → S j i)
    (group_ok : ∀ j k x, group j k x = ((outer j k, akey j k), fun i => tail j i (x i)))
    (header : F → (j : J) → H j)
    (derive : ∀ j k, H j → O j → G j k) (directKey : F → ∀ j k, G j k)
    (key_ok : ∀ f j k, derive j k (header f j) (outer j k) = directKey f j k)
    (inner : ∀ j k, A j → (∀ i, S j i) → ∀ i, V j k i)
    (directCT : ∀ j k i, X i → V j k i)
    (inner_ok : ∀ j k (x : ∀ i, X i),
      inner j k (akey j k) (fun i => tail j i (x i)) = (fun i => directCT j k i (x i)))
    (finish : ∀ j k, G j k → (∀ i, V j k i) → Bool) :
    ∀ f j k x,
      finish j k (derive j k (header f j) (group j k x).1.1)
        (inner j k (group j k x).1.2 (group j k x).2) =
      finish j k (directKey f j k) (fun i => directCT j k i (x i)) := by
  intro f j k x
  simp only [group_ok, key_ok, inner_ok]
