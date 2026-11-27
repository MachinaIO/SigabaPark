import Mathlib.Data.Bool.Basic

theorem solution (h gamma u p s v orient k : Bool) :
    let d := fun r z : Bool => if r == h then v else z ^^ orient
    let header := d p false ^^ k ^^ s
    let g := s ^^ (u && gamma)
    header ^^ (u && ((h ^^ gamma) ^^ p)) ^^ k ^^ g = d p u := by
  cases h <;> cases gamma <;> cases u <;> cases p <;> cases s <;>
    cases v <;> cases orient <;> cases k <;> decide
