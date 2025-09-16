import Mathlib.Data.DFinsupp.Defs
import Mathlib.Data.DFinsupp.Module
import Mathlib.Data.DFinsupp.Notation
import Mathlib.Data.DFinsupp.BigOperators
import Batteries.Data.Rat
import Mathlib.Data.Rat.Init
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.Group.TransferInstance
import LeanUnits.Framework.Dimensions.PrimeScale

namespace Units

@[ext]
structure Dimension where
  _impl : DFinsupp (fun _ : String => ℚ)
  deriving DecidableEq, BEq

class HasDimension (μ : Type) where
  dimension (u : μ) : Dimension

alias 𝒟 := HasDimension.dimension
namespace Dimension

def ofString (s : String) : Dimension := ⟨DFinsupp.single s 1⟩

def dimensionless : Dimension := ⟨0⟩

def IsBase (d : Dimension) : Prop := ∃ s : String, d = ofString s

def DecidableNEqZero.{u} (α : Type u) [Zero α] :=
  (x : α) → Decidable (x ≠ 0)

instance instEquiv : Dimension ≃ DFinsupp (fun _ : String => ℚ) :=
  ⟨Dimension._impl, Dimension.mk, by intro x; cases x; rfl, by intro y; rfl⟩

instance instAddCommGroup : AddCommGroup Dimension :=
  Dimension.instEquiv.addCommGroup

instance instSMul : SMul ℚ Dimension :=
  Dimension.instEquiv.smul ℚ

instance instMulAction : MulAction ℚ Dimension :=
  Dimension.instEquiv.mulAction ℚ

instance instSMulWithZero : SMulWithZero ℚ Dimension where
  zero_smul d := congrArg Dimension.mk (zero_smul ℚ d._impl)
  smul_zero q := congrArg Dimension.mk (smul_zero q)

instance instDecidableNeqZero : DecidableNEqZero Dimension :=
  fun x => (inferInstance : Decidable (x ≠ 0))

instance : HasDimension Dimension where
  dimension u := u

instance instSetoidUnit : Setoid Dimension where
  r := (· = ·)
  iseqv := ⟨fun _ => rfl, fun {_ _} h => h.symm, fun {_ _ _} h1 h2 => h1.trans h2⟩

instance instDecidableEquivDimension (a b : Dimension) : Decidable (a ≈ b) := by
  dsimp [HasEquiv.Equiv, instSetoidUnit]
  infer_instance

-- implement convenient syntax for dimensions, because addition is confusing
instance : One Dimension where
  one := 0

@[simp]
instance : Mul Dimension where
  mul u1 u2 := u1 + u2

@[simp]
instance : Inv Dimension where
  inv u := -u

@[simp]
instance : Div Dimension where
  div u1 u2 := u1 - u2

@[simp]
instance : Pow Dimension ℕ where
  pow u q := q • u

@[simp]
instance : Pow Dimension ℤ where
  pow u n := n • u

@[simp]
instance : Pow Dimension ℚ where
  pow u n := n • u


noncomputable def PrimeScale (d : Dimension) : ℝ := d._impl.prod PrimeScale.prime_pow
noncomputable def OneScale (_ : Dimension) : ℝ := 1

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
