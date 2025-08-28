import LeanUnits.Framework.Dimensions.Basic
import LeanUnits.Framework.Conversion
import LeanUnits.Framework.Utils
import Mathlib.Data.DFinsupp.Defs
import Mathlib.Data.DFinsupp.BigOperators
import Batteries.Data.Rat.Basic
import Mathlib.Data.Rat.Defs

namespace Units

/--
Choosing a metric involves choosing
- a power factor (it's one for base and derived units)
- an affine conversion (to convert between units of the same dimension)
- a dimension (to ensure dimensional correctness)

Note that all these 3 choices form a AddCommGroup, so we can combine them easily.
-/
abbrev UnitChoice := ℚ × Conversion × Dimension

/--
A unit is a product of base units raised to rational powers.
For example, the unit of force in the SI system is `kg•m/s²`
can be represented as :
- `force₁ = {"kg" ↦ (1,0,Mass), "m" ↦ (1,0,Length), "s" ↦ (-2,0,Time⁻²)}`

or when using derived units:
- `force₂={"N" ↦ (1,0,Mass•Length•Time⁻²)}`

Converting between these two representations is possible because
their dimensions are the same under product:
- `Π 𝒟(force₁) = Mass•Length•Time⁻² = Π 𝒟(force₂)`
-/
structure Unit where
  _impl : DFinsupp (fun _ : String =>  UnitChoice)
  deriving DecidableEq, BEq

namespace Unit

instance instEquiv : Unit ≃ (DFinsupp (fun _ : String => UnitChoice)) where
  toFun := Unit._impl
  invFun := Unit.mk

instance instAddCommGroup : AddCommGroup Unit :=
  Unit.instEquiv.addCommGroup

-- implement convenient syntax for units, because addition is confusing
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
  u._impl.sum (fun _ qd => qd.2.2)

def conversion (u : Unit) : Conversion :=
  u._impl.sum (fun _ qd => qd.2.1)

instance : HasDimension Unit where
  dimension := Unit.dimension

instance : HasConversion Unit where
  conversion := Unit.conversion

def defineUnit (s : String) (d : Dimension) : Unit := ⟨DFinsupp.single s (1,0,d)⟩
def defineDerivedUnit (s : String) (u : Unit)
  (conv : Conversion := 0) : Unit := ⟨DFinsupp.single s (1,conv.div u.conversion,u.dimension)⟩

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
