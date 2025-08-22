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

end Bases

end Units.Dimension
