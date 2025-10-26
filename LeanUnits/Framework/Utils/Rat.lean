import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Real.Basic

class RatCastClass (α) [RatCast α] [Field α] where
  zero_cast : (0 : ℚ) = (0 : α)
  one_cast  : (1 : ℚ) = (1 : α)

instance instRatCastClassReal : RatCastClass ℝ where
  zero_cast := by norm_cast
  one_cast  := by norm_cast
