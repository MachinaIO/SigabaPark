import Mathlib.Tactic

theorem NandMaskPlane.projectGate {E I : Type} [Add E] (port : E → I → ZMod 2) (secret : E → ZMod 2)
    (reconstruct : (I → ZMod 2) → ZMod 2)
    (mul : ∀ u v, reconstruct (fun i => port u i * port v i) = secret u * secret v)
    (a x y z : E) (hp : ∀ i, port (a + z) i = port a i + port z i)
    (hs : secret (a + z) = secret a + secret z)
    (hg : ∀ i, port x i * port y i = port a i * (port a i + port z i)) :
    secret x * secret y = secret a * (secret a + secret z) := by
  sorry
