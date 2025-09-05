import LeanUnits.Systems.Formal
import LeanUnits.Framework.Quantities.Lemmas
import Mathlib.Data.Real.Basic

namespace formal
open Units Real

abbrev SI (units : Dimension) := Quantity units ℝ

noncomputable def speed_from_pos_over_time
  (t : SI Dimension.Time) (v0 : SI Dimension.Speed) (angle : ℝ) : SI Dimension.Speed :=
  ↑Quantity.deriv (fun t => Real.cos angle • v0 * t) t

theorem simp_over_time (t : SI Dimension.Time) (v0 : SI Dimension.Speed) (angle : ℝ) :
    Quantity.deriv (fun t => Real.cos angle • v0 * t) t = ↑(Real.cos angle•v0) := by
    rw [Quantity.deriv_qconst_mul_real,Quantity.deriv_id, Quantity.mul_one]
    · rfl
    · exact Quantity.differentiable_fun_id

theorem simp_over_time' (t : SI Dimension.Time) (v0 : SI Dimension.Speed) (angle : ℝ) :
    Quantity.deriv (fun t => Real.cos angle • v0 * t) t = ↑(Real.cos angle•v0) := by
  simp [Quantity.deriv, Quantity.cast]
  change deriv (fun t : ℝ => Real.cos angle • v0.val * t) t.val = Real.cos angle * v0.val
  rw [deriv_const_mul]
  · simp
  · exact differentiableAt_fun_id

end formal
