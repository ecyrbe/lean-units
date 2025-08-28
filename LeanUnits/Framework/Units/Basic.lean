import LeanUnits.Framework.UnitSystem
import LeanUnits.Framework.Utils
import Mathlib.Data.DFinsupp.Defs
import Mathlib.Data.DFinsupp.BigOperators
import Batteries.Data.Rat.Basic
import Mathlib.Data.Rat.Defs

namespace Units

structure Unit where
  _impl : DFinsupp (fun _ : String =>  (ℚ×Conversion) × Dimension)
  deriving DecidableEq, BEq

namespace Unit


-- def defineDerivedUnit (s : String) (d : Dimension) (conv : Conversion) : Unit :=
--   ⟨DFinsupp.single s ((1,conv),d)⟩

instance instEquiv : Unit ≃ (DFinsupp (fun _ : String => (ℚ×Conversion)× Dimension)) where
  toFun := Unit._impl
  invFun := Unit.mk

instance instAddCommGroup : AddCommGroup Unit :=
  Unit.instEquiv.addCommGroup

-- implement convenient syntax for units, because addition is confusing
-- e.g. m/s = m + (-s) = m + (1/s)
@[simp]
instance : One Unit where
  one := 0

@[simp]
instance : Mul Unit where
  mul u1 u2 := u1 + u2

@[simp]
instance : Inv Unit where
  inv u := -u

@[simp]
instance : Div Unit where
  div u1 u2 := u1 - u2

@[simp]
instance : Pow Unit ℕ where
  pow u q := q • u

@[simp]
instance : Pow Unit ℤ where
  pow u n := n • u

def dimension (u : Unit) : Dimension :=
  u._impl.sum (fun _ qd => qd.2)

def conversion (u : Unit) : Conversion :=
  u._impl.sum (fun _ qd => qd.1.2)

instance : UnitSystem Unit where
  dimension := Unit.dimension
  conversion := Unit.conversion

def defineUnit (s : String) (d : Dimension) : Unit := ⟨DFinsupp.single s ((1,0),d)⟩
def defineDerivedUnit (s : String) (u : Unit)
  (conv : Conversion := 0) : Unit := ⟨DFinsupp.single s ((1,conv.div u.conversion),u.dimension)⟩

section Repr
open Lean Parser Term

unsafe instance : Repr Unit where
  reprPrec f _ :=
    let vals := f._impl.support'.unquot.val.map (fun i => (i,(f._impl i)))
      |>.unquot
      |>.filter (·.2 != 0)
      |>.dedup
      |>.mergeSort (fun a b => a.1 < b.1)
    if vals.length = 0 then
      "∅"
    else
      let parts : List String := vals.map (fun a => formatExp a.1 a.2.1.1)
      f!"{String.intercalate "•" parts}"

end Repr

end Unit

end Units
