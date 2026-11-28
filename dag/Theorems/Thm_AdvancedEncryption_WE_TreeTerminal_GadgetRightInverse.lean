import Mathlib

theorem AdvancedEncryption.WE.TreeTerminal.GadgetRightInverse {R : Type*} [CommRing R] {m n t d p : Type*}
    [Fintype m] [DecidableEq m] [Fintype n] [Fintype t] [Fintype d]
    (H : Matrix m n R) (J : Matrix n m R) (G : Matrix n t R)
    (T : Matrix t p R) (target : Matrix m p R)
    (inverse : H * J = 1) (digits : G * T = J * target) :
    (H * G) * T = target := by sorry
