import Batteries.Data.Rat
import Mathlib.Data.Rat.Init
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.List.Nodup
import Mathlib.Data.String.Basic
import Lean
import LeanUnits.Dimensions.Base.Basic
import LeanUnits.Dimensions.Base.Lemmas
import LeanUnits.Dimensions.Bases.Basic
import LeanUnits.Dimensions.Bases.Lemmas

namespace Units

@[ext]
structure Dimension where
  elements : Dimension.Bases
  is_sorted : Dimension.Bases.Sorted elements
deriving Repr, DecidableEq, BEq


namespace Dimension

theorem eq_iff_elements_eq (d₁ d₂ : Dimension) :
  d₁ = d₂ ↔ d₁.elements = d₂.elements := by
  constructor
  · intro h
    rw [h]
  · intro h
    exact Dimension.ext h


def dimensionless : Dimension :=
  {
    elements := [],
    is_sorted := Bases.Sorted.nil
  }

def ofBase (b : Base) : Dimension :=
  {
    elements := [b],
    is_sorted := Bases.Sorted.singleton
  }

def ofString (b : String) : Dimension :=
  ofBase (Base.ofString b)

def add (d₁ d₂ : Dimension) : Dimension :=
  {
    elements := Bases.merge d₁.elements d₂.elements,
    is_sorted := by apply Bases.merge.sorted d₁.is_sorted d₂.is_sorted
  }

def smul (n : ℚ) (d : Dimension) : Dimension :=
  {
    elements := Bases.qmul d.elements n,
    is_sorted := by
      apply Bases.qmul.sorted
      exact d.is_sorted
  }

def neg (d : Dimension) : Dimension :=
  smul (-1) d

def sub (d₁ d₂ : Dimension) : Dimension :=
  add d₁ (neg d₂)

instance : Inhabited Dimension where
  default := dimensionless

instance : Zero Dimension where
  zero := dimensionless

instance : EmptyCollection Dimension where
  emptyCollection := dimensionless

instance : Add Dimension where
  add := add

instance : Sub Dimension where
  sub := sub

instance : SMul ℕ Dimension where
  smul n := smul ↑n

instance : SMul ℤ Dimension where
  smul n := smul ↑n

instance : SMul ℚ Dimension where
  smul := smul


instance : Neg Dimension where
  neg := smul (-1)

theorem zero_add' (d : Dimension) : add dimensionless d = d := by
  unfold add dimensionless
  rw [eq_iff_elements_eq]
  apply Bases.merge.nil_self_eq_self

theorem zero_add (d : Dimension) : 0 + d = d := by
  exact zero_add' d

theorem add_zero' (d : Dimension) : add d dimensionless = d := by
  unfold add dimensionless
  rw [eq_iff_elements_eq]
  apply Bases.merge.self_nil_eq_self

theorem add_zero (d : Dimension) : d + 0 = d := by
  exact add_zero' d

theorem add_comm' (d₁ d₂ : Dimension) : add d₁ d₂ = add d₂ d₁ := by
  unfold add
  rw [eq_iff_elements_eq]
  apply Bases.merge.comm d₁.elements d₂.elements

theorem add_comm (d₁ d₂ : Dimension) : d₁ + d₂ = d₂ + d₁ := by
  exact add_comm' d₁ d₂

theorem add_assoc' (d₁ d₂ d₃ : Dimension) : add (add d₁ d₂) d₃ = add d₁ (add d₂ d₃) := by
  unfold add
  rw [eq_iff_elements_eq]
  apply Bases.merge.assoc d₁.elements d₂.elements d₃.elements d₁.is_sorted d₂.is_sorted d₃.is_sorted

theorem add_assoc (d₁ d₂ d₃ : Dimension) : (d₁ + d₂) + d₃ = d₁ + (d₂ + d₃) := by
  exact add_assoc' d₁ d₂ d₃

theorem add_neg_cancel' (d : Dimension) : add d (neg d ) = 0 := by
  unfold add neg
  rw [eq_iff_elements_eq]
  apply Bases.merge_qmul_inv d.is_sorted

theorem add_neg_cancel (d : Dimension) : d + -d  = 0 := by
  exact add_neg_cancel' d

theorem neg_add_cancel' (d : Dimension) : add (neg d ) d = 0 := by
  rw [add_comm', add_neg_cancel']

theorem neg_add_cancel (d : Dimension) : -d + d = 0 := by
  exact neg_add_cancel' d

theorem smul_zero' (d : Dimension) : smul 0 d = dimensionless := by
  unfold smul dimensionless Bases.qmul
  rw [eq_iff_elements_eq]
  simp only [↓reduceDIte]

theorem smul_zero (d : Dimension) : 0 • d = 0 := by
  exact smul_zero' d

theorem smul_one' (d : Dimension) : smul 1 d = d := by
  unfold smul Bases.qmul
  rw [eq_iff_elements_eq]
  simp only [one_ne_zero, ↓reduceDIte, ↓reduceIte]

theorem smul_one (d : Dimension) : 1 • d = d := by
  exact smul_one' d

theorem smul_succ' (n : ℚ) (d : Dimension) :
  smul (n + 1) d = add (smul n d) d := by
  unfold smul add
  rw [eq_iff_elements_eq]
  simp
  apply Bases.qmul_succ_eq_merge d.is_sorted n

theorem smul_succ (n : ℚ) (d : Dimension) :
  (n + 1) • d = n • d + d := by
  exact smul_succ' n d

theorem smul_neg' (n : ℚ) (d : Dimension) :
  smul (-n) d = neg (smul n d) := by
  unfold smul neg
  rw [eq_iff_elements_eq]
  apply Bases.qmul.neg_eq_neg n d.is_sorted

theorem smul_neg (n : ℚ) (d : Dimension) :
  (-n) • d = -(n • d) := by
  exact smul_neg' n d

theorem nsmul_succ' (n : ℕ) (d : Dimension) :
  instSMulNat.smul (n + 1) d = add (instSMulNat.smul n d) d := by
  change smul ↑(n + 1) d = add (smul ↑n d) d
  simp only [Nat.cast_add, Nat.cast_one, smul_succ']

theorem nsmul_succ (n : ℕ) (d : Dimension) :
  (n + 1) • d = n • d + d := by
  exact nsmul_succ' n d

theorem zsmul_neg' (n : ℕ) (d : Dimension) :
  instSMulInt.smul (-(n + 1)) d = neg (instSMulInt.smul (n + 1) d) := by
  change smul (-↑(n + 1)) d = neg (smul ↑(n + 1) d)
  rw [smul_neg']

theorem zsmul_neg (n : ℕ) (d : Dimension) :
  (-((n:ℤ) + 1)) • d = -( (n + 1) • d) := by
  exact zsmul_neg' n d

instance instAddCommGroup : AddCommGroup Dimension where
  add_assoc := add_assoc
  zero_add := zero_add
  add_zero := add_zero
  nsmul n := smul ↑n
  zsmul n := smul ↑n
  neg_add_cancel := neg_add_cancel
  add_comm := add_comm
  nsmul_succ := nsmul_succ
  zsmul_succ' := nsmul_succ
  zsmul_neg' := zsmul_neg

instance : Repr Dimension where
  reprPrec d _ :=
    if d.elements.isEmpty then
      "∅"
    else
      String.intercalate "•" (
        d.elements.map (
          fun (e : Base) => match e.exponent with
          | 1 => e.name
          | 2 => s!"{e.name}²"
          | 3 => s!"{e.name}³"
          | 4 => s!"{e.name}⁴"
          | 5 => s!"{e.name}⁵"
          | 6 => s!"{e.name}⁶"
          | 7 => s!"{e.name}⁷"
          | 8 => s!"{e.name}⁸"
          | 9 => s!"{e.name}⁹"
          | -1 => s!"{e.name}⁻¹"
          | -2 => s!"{e.name}⁻²"
          | -3 => s!"{e.name}⁻³"
          | -4 => s!"{e.name}⁻⁴"
          | -5 => s!"{e.name}⁻⁵"
          | -6 => s!"{e.name}⁻⁶"
          | -7 => s!"{e.name}⁻⁷"
          | -8 => s!"{e.name}⁻⁸"
          | -9 => s!"{e.name}⁻⁹"
          | _ => s!"{e.name}^{e.exponent}"
        )
      )


end Dimension

namespace Dimension

def Length := ofString "L"
def Mass := ofString "M"
def Time := ofString "T"
def Temperature := ofString "Θ"
def Current := ofString "I"
def AmountOfSubstance := ofString "N"
def LuminousIntensity := ofString "J"
-- one can add more base exponents as needed that are not part of the SI system
-- e.g., currency, etc.
def Currency := ofString "C"

-- we can derive some new dimensions from the base ones
abbrev Area := 2 • Length
#eval Area
abbrev Volume := 3 • Length
#eval Volume
abbrev Speed := Length - Time
#eval Speed
abbrev Acceleration := Length - 2•Time
#eval Acceleration
abbrev Jerk := Length - 3•Time
#eval Jerk
abbrev Snap := Length - 4•Time
#eval Snap
abbrev Momentum := Mass + Speed
#eval Momentum
abbrev AngularMomentum := Momentum + Length
#eval AngularMomentum
abbrev Force := Mass + Acceleration
#eval Force
abbrev Pressure := Force - Area
#eval Pressure
abbrev Energy := Force + Length
#eval Energy
abbrev Action := Energy + Time
#eval Action
abbrev Power := Energy - Time
#eval Power
abbrev Charge := Current + Time
#eval Charge
abbrev Frequency := -Time
#eval Frequency
abbrev Voltage := Power - Current
#eval Voltage
abbrev Capacitance := Charge - Voltage
#eval Capacitance
abbrev Resistance := Voltage - Current
#eval Resistance
abbrev Conductance := Current - Voltage
#eval Conductance
abbrev Inductance := Resistance + Time
#eval Inductance
abbrev MagneticFlux := Voltage + Time
#eval MagneticFlux
abbrev MagneticInduction := MagneticFlux - Area
#eval MagneticInduction

end Units.Dimension
