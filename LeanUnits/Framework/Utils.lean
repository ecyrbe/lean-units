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
open Lean Meta Elab Term

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
syntax:80 (name := dependentPow) term:80 " ^ᵈ " term:81 : term

elab_rules : term
  | `($q:term ^ᵈ $n:term) => do
      let ne ← elabTerm n none
      let nty ← whnf (← inferType ne)

      let tryDot (field : Name) : TermElabM (Option Expr) := do
        let stx ← `(($q).$(mkIdent field) $n)
        try
          return some (← elabTerm stx none)
        catch _ =>
          return none

      let attempt (field : Name) : TermElabM Expr := do
        if let some e ← tryDot field then
        return e
        else
        throwErrorAt q m!"missing .{field} on base; cannot apply dependent power"

      if nty.isConstOf ``Nat then
        attempt `npow
      else if nty.isConstOf ``Int then
        attempt `zpow
      else if nty.isConstOf ``Rat then
        attempt `qpow
      else
        throwErrorAt n m!"exponent must be ℕ, ℤ, or ℚ; got type {nty}"

end power

end Units
