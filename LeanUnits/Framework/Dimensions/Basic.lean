import Mathlib.Data.DFinsupp.Defs
import Mathlib.Data.DFinsupp.Module
import Mathlib.Data.DFinsupp.Notation
import Mathlib.Data.DFinsupp.BigOperators
import Batteries.Data.Rat
import Mathlib.Data.Rat.Init
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.Group.TransferInstance
import LeanUnits.Framework.Dimensions.PrimeScale
import LeanUnits.Framework.Utils.Format

namespace Units

/--
A dimension is a product of base dimensions raised to rational powers.
For example, the dimension of force in the SI system is `Mass•Length•Time⁻²`
can be represented as :
- `force = {"Mass" ↦ 1, "Length" ↦ 1, "Time" ↦ -2}`
you build it by combining base dimensions using multiplication and division.
- To build a base dimension, use the helper macro `def_base_dimension Length := "L"`
- To build a derived dimension, use multiplication `*`, division `/` and exponentiation `^`.

For example, the dimension of Area can be built using the helper macro:
- `def_derived_dimension Area := Length^2`

Note that using macros is encouraged to ensure correct simplification of dimensions when casting.
-/
@[ext]
structure Dimension where
  _impl : DFinsupp (fun _ : String => ℚ)
  deriving DecidableEq, BEq

/--
A typeclass for types that have an associated dimension.
-/
class HasDimension (μ : Type) where
  dimension (u : μ) : Dimension

alias 𝒟 := HasDimension.dimension
namespace Dimension

/--
Create a dimension from a string identifier.
Each unique string represents a different fundamental dimension.
For example, "L" for Length, "M" for Mass, "T" for Time, etc.
-/
def ofString (s : String) : Dimension := ⟨DFinsupp.single s 1⟩

/--
The dimension with no fundamental dimensions, representing a dimensionless quantity.
-/
def dimensionless : Dimension := ⟨0⟩

/--
A dimension is a base dimension if it corresponds to a single fundamental dimension,
represented by a string identifier and has an exponent of 1.
-/
def IsBase (d : Dimension) : Prop := ∃ s : String, d = ofString s

def bases (d : Dimension) : List String :=
  unsafe d._impl.support'.unquot.val.unquot
  |>.filter (fun s => d._impl s ≠ 0)
  |>.dedup
  |>.mergeSort (fun a b => a < b)

def IsBase' (d : Dimension) :=
  match d.bases with
  | [s] => d._impl s == 1
  | _   => false

def base_name (d : Dimension) (h : d.IsBase') : String :=
  have h': d.bases ≠ [] := by
    intro h''
    unfold IsBase' at h
    rw [h''] at h
    simp only at h
    contradiction
  d.bases.head h'


/--
A dimension is a single dimension if it corresponds to a single fundamental dimension,
represented by a string identifier and a rational exponent.
-/
def IsSingle (d : Dimension) : Prop := ∃ s : String, ∃ q: ℚ, q ≠ 0 ∧ d = ⟨DFinsupp.single s q⟩

/--
Non computable function to extract the name of the base dimension.
-/
noncomputable def IsBase.name {d : Dimension} (h : d.IsBase) : String :=
  Classical.choose h

def IsBase.exponent {d : Dimension} (_ : d.IsBase) : ℚ := 1

/--
The specification that the name corresponds to the base dimension.
-/
lemma IsBase.name_spec {d : Dimension} (h : d.IsBase) : d = Dimension.ofString (h.name) :=
  Classical.choose_spec h

/--
The specification that the name and exponent correspond to the base dimension.
-/
lemma IsBase.name_exponent_spec {d : Dimension} (h : d.IsBase) :
  h.exponent = 1 ∧ d = ⟨DFinsupp.single h.name h.exponent⟩ := by
  constructor
  · rfl
  · exact h.name_spec

/--
Non computable function to extract the name and exponent of the single dimension.

ie: dimensions like `Length^2` or `Time^-1`
-/
noncomputable def IsSingle.name {d : Dimension} (h : d.IsSingle) : String :=
  Classical.choose h

/--
Non computable function to extract the exponent of the single dimension.

ie: dimensions like `Length^2` or `Time^-1`
-/
noncomputable def IsSingle.exponent {d : Dimension} (h : d.IsSingle) : ℚ :=
  Classical.choose (Classical.choose_spec h)

/--
The specification that the name and exponent correspond to the single dimension.
-/
lemma IsSingle.name_exponent_spec {d : Dimension} (h : d.IsSingle) :
  h.exponent ≠ 0 ∧ d = ⟨DFinsupp.single h.name h.exponent⟩ :=
  Classical.choose_spec (Classical.choose_spec h)

def DecidableNEqZero.{u} (α : Type u) [Zero α] :=
  (x : α) → Decidable (x ≠ 0)

instance instEquiv : Dimension ≃ DFinsupp (fun _ : String => ℚ) :=
  ⟨Dimension._impl, Dimension.mk, by intro x; cases x; rfl, by intro y; rfl⟩

@[simp]
instance instAddCommGroup : AddCommGroup Dimension :=
  Dimension.instEquiv.addCommGroup

instance instSMul : SMul ℚ Dimension :=
  Dimension.instEquiv.smul ℚ

instance instMulAction : MulAction ℚ Dimension where
  one_smul d := congrArg Dimension.mk (one_smul ℚ d._impl)
  mul_smul q1 q2 d := congrArg Dimension.mk (mul_smul q1 q2 d._impl)

instance instSMulWithZero : SMulWithZero ℚ Dimension where
  zero_smul d := congrArg Dimension.mk (zero_smul ℚ d._impl)
  smul_zero q := congrArg Dimension.mk (smul_zero q)

instance instModule : Module ℚ Dimension where
  zero_smul d := congrArg Dimension.mk (zero_smul ℚ d._impl)
  smul_zero q := congrArg Dimension.mk (smul_zero q)
  smul_add q a b:= congrArg Dimension.mk (smul_add q a._impl b._impl)
  add_smul q1 q2 a := congrArg Dimension.mk (add_smul q1 q2 a._impl)

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

instance : Mul Dimension where
  mul u1 u2 := u1 + u2

instance : Inv Dimension where
  inv u := -u

instance : Div Dimension where
  div u1 u2 := u1 - u2

instance : Pow Dimension ℕ where
  pow u q := q • u

instance : Pow Dimension ℤ where
  pow u n := n • u

instance : Pow Dimension ℚ where
  pow u n := n • u


noncomputable def PrimeScale (d : Dimension) : ℝ := d._impl.prod PrimeScale.prime_pow
noncomputable def OneScale (_ : Dimension) : ℝ := 1

section Repr
open Lean Parser Term

instance : Repr Dimension where
  reprPrec f _ :=
    let bases := f.bases
    if bases.length = 0 then
      "∅"
    else
      let parts : List String := bases.map (fun a => formatExp a (f._impl a))
      f!"{String.intercalate "•" parts}"

instance : ToString Dimension where
  toString d := reprStr d

end Repr

end Dimension

end Units
