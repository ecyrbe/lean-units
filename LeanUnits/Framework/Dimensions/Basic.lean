import Mathlib.Data.DFinsupp.Defs
import Mathlib.Data.DFinsupp.Module
import Mathlib.Data.DFinsupp.Notation
import Batteries.Data.Rat
import Mathlib.Data.Rat.Init
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.Group.TransferInstance
import LeanUnits.Framework.Utils

namespace Units
@[ext]
structure Dimension where
  _impl : DFinsupp (fun _ : String => ℚ)
  deriving DecidableEq

namespace Dimension

def ofString (s : String) : Dimension := ⟨DFinsupp.single s 1⟩

def dimensionless : Dimension := ⟨0⟩

abbrev DecidableNEqZero.{u} (α : Type u) [Zero α] :=
  (x : α) → Decidable (x ≠ 0)

instance instEquiv : Dimension ≃ DFinsupp (fun _ : String => ℚ) :=
  ⟨Dimension._impl, Dimension.mk, by intro x; cases x; rfl, by intro y; rfl⟩

instance instAddCommGroup : AddCommGroup Dimension :=
  Dimension.instEquiv.addCommGroup

instance instSMul : SMul ℚ Dimension :=
  Dimension.instEquiv.smul ℚ

instance instDecidableNeqZero : DecidableNEqZero Dimension :=
  fun x => (inferInstance : Decidable (x ≠ 0))

section Repr
open Lean Parser Term

instance : Repr Dimension where
  reprPrec f _ :=
    let vals := unsafe f._impl.support'.unquot.val.map (fun i => (i,(f._impl i)))
      |>.unquot
      |>.filter (·.2 != 0)
      |>.dedup
      |>.mergeSort (fun a b => a.1 < b.1)
    if vals.length = 0 then
      "∅"
    else
      let parts : List String := vals.map (fun a => formatExp a.1 a.2)
      f!"{String.intercalate "•" parts}"

instance : ToString Dimension where
  toString d := reprStr d

end Repr

end Dimension

end Units
