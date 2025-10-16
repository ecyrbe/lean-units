namespace Units

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
