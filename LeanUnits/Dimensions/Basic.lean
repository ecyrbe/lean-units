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
    is_sorted := Bases.Sorted.singleton b
  }

def ofString (b : String) : Dimension :=
  ofBase (Base.ofString b)

def mul (d₁ d₂ : Dimension) : Dimension :=
  {
    elements := Bases.merge d₁.elements d₂.elements,
    is_sorted := by
      apply Bases.merge.sorted
      · exact d₁.is_sorted
      · exact d₂.is_sorted
  }

def pow (d : Dimension) (n : ℚ) : Dimension :=
  {
    elements := Bases.qmul d.elements n,
    is_sorted := by
      apply Bases.qmul.sorted
      exact d.is_sorted
  }

def inv (d : Dimension) : Dimension :=
  pow d (-1)

def div (d₁ d₂ : Dimension) : Dimension :=
  mul d₁ (inv d₂)

instance : Inhabited Dimension where
  default := dimensionless

instance : One Dimension where
  one := dimensionless

instance : EmptyCollection Dimension where
  emptyCollection := dimensionless

instance : Mul Dimension where
  mul := mul

instance : Div Dimension where
  div := div

instance : Pow Dimension ℚ where
  pow := Dimension.pow

instance : Inv Dimension where
  inv d := pow d (-1)

theorem one_mul' (d : Dimension) : mul dimensionless d = d := by
  unfold mul dimensionless
  rw [eq_iff_elements_eq]
  apply Bases.merge.nil_self_eq_self

theorem one_mul (d : Dimension) : 1 * d = d := by
  exact one_mul' d

theorem mul_one' (d : Dimension) : mul d dimensionless = d := by
  unfold mul dimensionless
  rw [eq_iff_elements_eq]
  apply Bases.merge.self_nil_eq_self

theorem mul_one (d : Dimension) : d * 1 = d := by
  exact mul_one' d

theorem mul_comm' (d₁ d₂ : Dimension) : mul d₁ d₂ = mul d₂ d₁ := by
  unfold mul
  rw [eq_iff_elements_eq]
  apply Bases.merge.comm d₁.elements d₂.elements

theorem mul_comm (d₁ d₂ : Dimension) : d₁ * d₂ = d₂ * d₁ := by
  exact mul_comm' d₁ d₂

theorem mul_assoc' (d₁ d₂ d₃ : Dimension) : mul (mul d₁ d₂) d₃ = mul d₁ (mul d₂ d₃) := by
  unfold mul
  rw [eq_iff_elements_eq]
  apply Bases.merge.assoc d₁.elements d₂.elements d₃.elements d₁.is_sorted d₂.is_sorted d₃.is_sorted

theorem mul_assoc (d₁ d₂ d₃ : Dimension) : (d₁ * d₂) * d₃ = d₁ * (d₂ * d₃) := by
  exact mul_assoc' d₁ d₂ d₃

theorem mul_inv_cancel' (d : Dimension) : mul d (pow d (-1)) = 1 := by
  unfold mul pow
  rw [eq_iff_elements_eq]
  apply Bases.merge_qmul_inv d.elements d.is_sorted

theorem mul_inv_cancel (d : Dimension) : d * d ^ (-1:ℚ) = 1 := by
  exact mul_inv_cancel' d

theorem inv_mul_cancel' (d : Dimension) : mul (pow d (-1)) d = 1 := by
  rw [mul_comm', mul_inv_cancel']

theorem inv_mul_cancel (d : Dimension) : d ^ (-1:ℚ) * d = 1 := by
  exact inv_mul_cancel' d

instance instCommGroup : CommGroup Dimension where
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  mul_comm := mul_comm
  inv := inv
  inv_mul_cancel := inv_mul_cancel

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
def Area := Length ^ (2:ℚ)
#eval Area
def Volume := Length ^ (3:ℚ)
#eval Volume
def Speed := Length / Time
#eval Speed
def Acceleration := Length / Time ^ (2:ℚ)
#eval Acceleration
def Force := Mass * Acceleration
#eval Force
def Pressure := Force / Area
#eval Pressure
def Energy := Force * Length
#eval Energy
def Power := Energy / Time
#eval Power
def Charge := Current * Time
#eval Charge
def Empty := Speed / Length * Time
#eval Empty
def Frequency := 1 / Time
#eval Frequency

def accel1 := Length * Time^(-1 :ℚ) / Time * Length / Length
def accel2 := Length / Time ^ (2 :ℚ)

#eval accel1 == accel2
#eval accel1 = accel2
#eval Length * Time^(-1: ℚ) / Time * Length / Length = Length / Time ^ 2

end Units.Dimension
