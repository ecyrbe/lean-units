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

theorem scalable_add_eq_mul {c1 c2 : Conversion} (h1 : Scalable c1) (h2 : Scalable c2) :
  c1 + c2 = c1 * c2 := by
  unfold Scalable at *
  rw [HAdd.hAdd,instHAdd, Add.add,instAdd, HMul.hMul,instHMul, Mul.mul]
  simp [add, mul, h1, h2]

theorem scalable_sub_eq_div {c1 c2 : Conversion} (h1 : Scalable c1) (h2 : Scalable c2) :
  c1 - c2 = c1 / c2 := by
  unfold Scalable at *
  rw [HSub.hSub,instHSub, Sub.sub,instSub, HDiv.hDiv,instHDiv, Div.div]
  simp [sub, div, inv,mul, h1, h2]
  rfl

theorem factor_zero : (0 : Conversion).factor = 1 := by rfl

theorem factor_div {c1 c2 : Conversion} :
  (c1 / c2).factor = c1.factor / c2.factor := by
  rw [HDiv.hDiv,instHDiv, Div.div]
  simp [div, mul, inv]
  rfl

theorem factor_mul {c1 c2 : Conversion} : (c1 * c2).factor = c1.factor * c2.factor := by rfl

theorem factor_inv {c : Conversion} : (c⁻¹).factor = 1 / c.factor := by rfl

theorem factor_add {c1 c2 : Conversion} : (c1 + c2).factor = c1.factor * c2.factor := by rfl

theorem factor_sub {c1 c2 : Conversion} : (c1 - c2).factor = c1.factor / c2.factor := by rfl

theorem factor_nsmul {c : Conversion} (s : ℕ) : (s • c).factor = c.factor ^ s := by rfl

theorem factor_zsmul {c : Conversion} (s : ℤ) : (s • c).factor = c.factor ^ s := by rfl

theorem factor_div_self_cancel {c : Conversion} : (c/c).factor = 1 := by
  rw [factor_div, div_self c.factor_ne_zero]

theorem scalable_apply {α} [RatCast α] [Field α]
  (c : Conversion) (x : α) (h : Scalable c)
  (h_coe_zero : (0 : ℚ) = (0 : α) := by norm_cast) :
  c.apply x = x * c.factor := by
  unfold Scalable at h
  simp only [apply, h, h_coe_zero]
  field_simp

theorem scalable_convert {α} [RatCast α] [Field α]
  (c1 c2 : Conversion) (x : α) (h1 : Scalable c1) (h2 : Scalable c2)
  (h_coe_zero : (0 : ℚ) = (0 : α) := by norm_cast) :
  convert c1 c2 x = x * ↑(c1.factor/c2.factor) := by
  simp only [convert, scalable_apply, scalable_div, h1, h2, h_coe_zero, factor_div]

theorem scalable_convert_same_eq_id {α} [RatCast α] [Field α]
  (c : Conversion) (x : α) (h : Scalable c)
  (h_coe_zero : (0 : ℚ) = (0 : α) := by norm_cast)
  (h_coe_one : (1 : ℚ) = (1 : α) := by norm_cast) :
  convert c c x = x := by
  simp only [scalable_convert, h, h_coe_zero, div_self c.factor_ne_zero, h_coe_one, mul_one]

theorem convert_zero_eq_id {α} [RatCast α] [Field α] (x : α)
  (h_coe_zero : (0 : ℚ) = (0 : α) := by norm_cast)
  (h_coe_one : (1 : ℚ) = (1 : α) := by norm_cast) :
  convert 0 0 x = x := by
  simp only [scalable_convert_same_eq_id, scalable_zero, h_coe_zero, h_coe_one]

end Units.Conversion
