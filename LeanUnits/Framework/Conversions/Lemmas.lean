import LeanUnits.Framework.Conversions.Basic
import Batteries.Data.Rat.Basic
import Batteries.Data.Rat.Lemmas
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

namespace Units.Conversion

theorem scalable_of_scale (s : ℚ) (h : s ≠ 0 := by simp) : Scalable (scale s h) := by rfl

theorem scalable_zero : Scalable 0 := by rfl

theorem scalable_add {c1 c2 : Conversion} (h1 : Scalable c1) (h2 : Scalable c2) :
  Scalable (c1 + c2) := by
  unfold Scalable at *
  simp only [HAdd.hAdd, Add.add, add, h1, h2]
  apply _root_.zero_add

theorem scalable_neg {c : Conversion} (h : Scalable c) : Scalable (-c) := by
  unfold Scalable at *
  simp only [Neg.neg, neg, h]
  apply neg_zero

theorem scalable_sub {c1 c2 : Conversion} (h1 : Scalable c1) (h2 : Scalable c2) :
  Scalable (c1 - c2) := by
  unfold Scalable at *
  simp only [HSub.hSub, Sub.sub, sub, h1, h2]
  apply _root_.zero_sub

theorem scalable_smul {c : Conversion} (s : ℕ) (h : Scalable c) : Scalable (s • c) := by
  unfold Scalable at *
  simp only [HSMul.hSMul, SMul.smul, nsmul, h]
  apply mul_zero

theorem scalable_zsmul {c : Conversion} (s : ℤ) (h : Scalable c) : Scalable (s • c) := by
  unfold Scalable at *
  simp only [HSMul.hSMul, SMul.smul, zsmul, h]
  apply mul_zero

theorem scalable_mul {c1 c2 : Conversion} (h1 : Scalable c1) (h2 : Scalable c2) :
  Scalable (c1 * c2) := by
  unfold Scalable at *
  rw [HMul.hMul,instHMul, Mul.mul]
  simp [mul, h1, h2]

theorem scalable_div {c1 c2 : Conversion} (h1 : Scalable c1) (h2 : Scalable c2) :
  Scalable (c1 / c2) := by
  unfold Scalable at *
  rw [HDiv.hDiv,instHDiv, Div.div]
  simp [div,mul, inv, h1, h2]

theorem scalable_inv {c : Conversion} (h : Scalable c) : Scalable (c⁻¹) := by
  unfold Scalable at *
  simp [Inv.inv,inv, h]

end Units.Conversion
