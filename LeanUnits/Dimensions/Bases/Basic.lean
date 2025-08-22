import Batteries.Data.Rat
import Mathlib.Data.Rat.Init
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.List.Nodup
import Mathlib.Data.String.Basic
import Lean
import LeanUnits.Dimensions.Base.Basic
import LeanUnits.Dimensions.Base.Lemmas

namespace Units.Dimension

abbrev Bases := List Base

namespace Bases

def Sorted : Bases → Prop := List.Pairwise (·.name < ·.name)
def Nodup : Bases → Prop := List.Pairwise (·.name ≠ ·.name)

def exponentOf (name : String) (l : Bases) : ℚ :=
  match l.find? (fun b => b.name = name) with
  | none => 0
  | some b => b.exponent

/--
Merge two lists of bases, combining exponents of bases with the same name.
-/
def merge : Bases → Bases → Bases
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
    if x.name = y.name then
      match Base.merge x.name x.exponent y.exponent with
      | none => merge xs ys
      | some z => z :: merge xs ys
    else if x.name < y.name then
      x :: merge xs (y :: ys)
    else
      y :: merge (x :: xs) ys

/--
Multiply all exponents in a list of bases by a rational number.
If the rational number is zero, the result is the empty list.
If the rational number is one, the result is the same list.
-/
def qmul (l : Bases) (n : ℚ) : Bases :=
  if n_ne_zero: n = 0 then
    []
  else if n = 1 then
    l
  else
    l.map fun e => {
      name := e.name,
      exponent := e.exponent * n,
      not_zero := by
        rw [mul_ne_zero_iff]
        constructor
        · exact e.not_zero
        · exact n_ne_zero
    }


end Bases

end Units.Dimension
