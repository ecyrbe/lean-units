import Batteries.Data.Rat
import Mathlib.Data.Rat.Init
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.String.Basic
import Lean

namespace Units.Dimension

@[ext]
structure Base where
  name : String
  exponent : ℚ
  not_zero: exponent ≠ 0
  deriving Repr, DecidableEq

namespace Base

def ofString (b : String) : Base :=
  { name := b, exponent := 1, not_zero := by decide }

def merge (b : String) (e₁ e₂ : ℚ) : Option Base :=
  if h: e₁ + e₂ = 0 then
    none
  else
    some { name := b, exponent := e₁ + e₂, not_zero := by exact h }

end Base

end Units.Dimension
