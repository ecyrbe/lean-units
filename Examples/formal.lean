import LeanUnits.Systems.Formal
import LeanUnits.Framework.Quantities.Lemmas
import Mathlib.Data.Real.Basic

namespace formal
open Units Real

abbrev SI (units : Dimension) := Quantity units ℝ


variable (G : SI (Dimension.Length ^ 3 / (Dimension.Mass * Dimension.Time ^ 2)))
variable (c : SI Dimension.Speed)

theorem kepler_third_law
    (T : SI Dimension.Time) (a : SI Dimension.Length) (M m : SI Dimension.Mass) :
    T² =  (4•π^2) • ↑(a³/ (G *(M + m)))  := by
  sorry

theorem e_equal_mc2 (E : SI Dimension.Energy) (m : SI Dimension.Mass) :
    E =  ↑(m * c²) := by
    sorry

-- theorem e_equal_mc (E : SI Dimension.Energy) (m : SI Dimension.Mass) :
--     E =  ↑(m * c) := by -- statement is wrong and is directly catched by the type checker
--     sorry

noncomputable def speed_from_pos_over_time (t : SI Dimension.Time)
  (v0 : SI Dimension.Speed) (angle : ℝ) : SI Dimension.Speed :=
  ↑ Quantity.deriv (fun t => Real.cos angle • v0 * t) t

theorem simp_over_time (t : SI Dimension.Time) (v0 : SI Dimension.Speed) (angle : ℝ) :
    Quantity.deriv (fun t => Real.cos angle • v0 * t) t =
    ↑(Real.cos angle•v0) := by
  simp [Quantity.deriv, Quantity.cast]
  change deriv (fun t : ℝ => Real.cos angle • v0.val * t) t.val = Real.cos angle * v0.val
  rw [deriv_const_mul]
  · simp
  · exact differentiableAt_fun_id

end formal
