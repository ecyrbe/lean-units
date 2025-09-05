import LeanUnits.Systems.Formal
import LeanUnits.Framework.Quantities.Lemmas
import Mathlib.Data.Real.Basic

namespace formal
open Units Real Dimension

abbrev WithDim (units : Dimension) := Quantity units ℝ

noncomputable def speed_from_pos_over_time
  (t : WithDim Time) (v0 : WithDim Speed) (angle : ℝ) :WithDim Speed :=
  ↑Quantity.deriv (fun t => Real.cos angle • v0 * t) t

-- proof using Quantities lemmas
theorem simp_over_time (t : WithDim Time) (v0 : WithDim Speed) (angle : ℝ) :
    Quantity.deriv (fun t => Real.cos angle • v0 * t) t = ↑(Real.cos angle•v0) := by
    rw [Quantity.deriv_qconst_mul_real]
    · rw [Quantity.deriv_id, Quantity.mul_one]; rfl
    · exact Quantity.differentiable_fun_id

-- proof using only mathlib lemmas
theorem simp_over_time' (t : WithDim Time) (v0 : WithDim Speed) (angle : ℝ) :
    Quantity.deriv (fun t => Real.cos angle • v0 * t) t = ↑(Real.cos angle•v0) := by
  simp [Quantity.deriv, Quantity.cast]
  change deriv (fun t : ℝ => Real.cos angle • v0.val * t) t.val = Real.cos angle * v0.val
  rw [deriv_const_mul]
  · simp only [_root_.smul_eq_mul, deriv_id'', mul_one]
  · exact differentiableAt_fun_id

end formal
