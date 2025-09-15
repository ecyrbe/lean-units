import Batteries.Data.Rat

namespace Units

def formatExp (e : String) (n : Rat) : String :=
  match n with
  | 1   => e
  | 2   => s!"{e}²"
  | 3   => s!"{e}³"
  | 4   => s!"{e}⁴"
  | 5   => s!"{e}⁵"
  | 6   => s!"{e}⁶"
  | 7   => s!"{e}⁷"
  | 8   => s!"{e}⁸"
  | 9   => s!"{e}⁹"
  | -1  => s!"{e}⁻¹"
  | -2  => s!"{e}⁻²"
  | -3  => s!"{e}⁻³"
  | -4  => s!"{e}⁻⁴"
  | -5  => s!"{e}⁻⁵"
  | -6  => s!"{e}⁻⁶"
  | -7  => s!"{e}⁻⁷"
  | -8  => s!"{e}⁻⁸"
  | -9  => s!"{e}⁻⁹"
  | n   => s!"{e}^{n}"

section power
-- Single "power" notation that dispatches by exponent type (ℕ, ℤ, or ℚ)
universe u v w

/--
Dependent power operator, allows to have the output type depend on the exponent.
`q ^ᵈ n`:
- if `n : ℕ` uses `q.npow`
- if `n : ℤ` uses `q.zpow`
- if `n : ℚ` uses `q.qpow`

Examples:
- `q ^ᵈ 2`          -- npow
- `q ^ᵈ (-2 : ℤ)`   -- zpow
- `q ^ᵈ (1/3 : ℚ)`  -- qpow
-/
class DPow (α : Type u) (β : Type v) (γ : outParam (β → Type w)) where
  pow : α → (n : β) → γ n

infixr:80 " ^ᵈ " => DPow.pow

end power

end Units
