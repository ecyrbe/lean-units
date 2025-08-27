import LeanUnits.Framework.Dimensions.Basic
import LeanUnits.Framework.Conversion
import LeanUnits.Framework.Utils
import Mathlib.Data.DFinsupp.Defs
import Mathlib.Data.DFinsupp.BigOperators
import Batteries.Data.Rat.Basic
import Mathlib.Data.Rat.Defs

namespace Units

class UnitSystem (μ : Type) [AddCommGroup μ] where
  dimension (u : μ) : Dimension
  conversion (u : μ) : Conversion

alias 𝒞 := UnitSystem.conversion
alias 𝒟 := UnitSystem.dimension

structure Unit where
  _impl : DFinsupp (fun _ : String =>  (ℚ×Conversion) × Dimension)

namespace Unit


def defineUnit (s : String) (d : Dimension) : Unit := ⟨DFinsupp.single s ((1,0),d)⟩
def defineDerivedUnit (s : String) (d : Dimension) (conv : Conversion) : Unit :=
  ⟨DFinsupp.single s ((1,conv),d)⟩

instance instEquiv : Unit ≃ (DFinsupp (fun _ : String => (ℚ×Conversion)× Dimension)) where
  toFun := Unit._impl
  invFun := Unit.mk

instance instAddCommGroup : AddCommGroup Unit :=
  Unit.instEquiv.addCommGroup

def dimension (u : Unit) : Dimension :=
  u._impl.sum (fun _ qd => qd.2)

def conversion (u : Unit) : Conversion :=
  u._impl.sum (fun _ qd => qd.1.2)

instance : UnitSystem Unit where
  dimension := Unit.dimension
  conversion := Unit.conversion

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
