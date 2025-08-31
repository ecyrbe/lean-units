import LeanUnits.Framework.Units.Basic

namespace Units.Unit

theorem equiv_refl {u : Unit} : u ≈ u := Setoid.refl u

theorem equiv_symm {u1 u2 : Unit} (h : u1 ≈ u2) : u2 ≈ u1 := Setoid.symm h

theorem equiv_trans {u1 u2 u3 : Unit} (h1 : u1 ≈ u2) (h2 : u2 ≈ u3) : u1 ≈ u3 := Setoid.trans h1 h2

theorem eq_imp_equiv {μ} [Setoid μ] {u1 u2 : μ} (h : u1 = u2) : u1 ≈ u2 := by
  rw [h]
  exact Setoid.refl u2

end Units.Unit
