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

/--
Merges two sorted lists of `Base` elements, removing duplicates and summing exponents.
If summed exponents are zero, they are also removed

This means that if b ∈ l₁ ∨ b ∈ l₂ we can't conclude that b ∈ merge l₁ l₂ and vice versa
But we have :
• a ∈ l₁, b ∈ l₂, a.name ≠ b.name → a ∈ merge l₁ l₂ ∧ b ∈ merge l₁ l₂
-/
def mulExponents (l : Bases) (n : ℚ) : Bases :=
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

theorem mulExponents_sorted (l : Bases) (n : ℚ) (h : Bases.Sorted l) :
  Bases.Sorted (mulExponents l n) := by
  unfold mulExponents
  split
  · exact List.Pairwise.nil
  · split
    · exact h
    · apply List.Pairwise.map
      · intro a b h_lt
        exact h_lt
      · exact h

def dimensionless : Dimension :=
  {
    elements := [],
    is_sorted := by exact List.Pairwise.nil
  }

def ofString (b : String) : Dimension :=
  {
    elements := [Base.ofString b],
    is_sorted := by exact List.pairwise_singleton (·.name < ·.name) (Base.ofString b)
  }

def mul (d₁ d₂ : Dimension) : Dimension :=
  {
    elements := Bases.merge d₁.elements d₂.elements,
    is_sorted := by
      apply Bases.merge_sorted
      · exact d₁.is_sorted
      · exact d₂.is_sorted
  }

def pow (d : Dimension) (n : ℚ) : Dimension :=
  {
    elements := mulExponents d.elements n,
    is_sorted := by
      apply mulExponents_sorted
      exact d.is_sorted
  }

def div (d₁ d₂ : Dimension) : Dimension :=
  mul d₁ (pow d₂ (-1))

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

theorem one_mul' (d : Dimension) : mul dimensionless d = d := by
  unfold mul dimensionless
  rw [eq_iff_elements_eq]
  apply Bases.merge_nil_self_eq_self

theorem one_mul (d : Dimension) : 1 * d = d := by
  exact one_mul' d

theorem mul_one' (d : Dimension) : mul d dimensionless = d := by
  unfold mul dimensionless
  rw [eq_iff_elements_eq]
  apply Bases.merge_self_nil_eq_self

theorem mul_one (d : Dimension) : d * 1 = d := by
  exact mul_one' d

theorem mul_comm' (d₁ d₂ : Dimension) : mul d₁ d₂ = mul d₂ d₁ := by
  unfold mul
  rw [eq_iff_elements_eq]
  apply Bases.merge_comm d₁.elements d₂.elements

theorem mul_comm (d₁ d₂ : Dimension) : d₁ * d₂ = d₂ * d₁ := by
  exact mul_comm' d₁ d₂

-- theorem mul_inv' (d : Dimension) : mul d (pow d (-1)) = 1 := by sorry

-- theorem mul_inv (d : Dimension) : d * d ^ (-1:ℚ) = 1 := by
--   exact mul_inv' d

-- theorem inv_mul' (d : Dimension) : mul (pow d (-1)) d = 1 := by sorry

-- theorem inv_mul (d : Dimension) : d ^ (-1:ℚ) * d = 1 := by
--   exact inv_mul' d

instance : Repr Dimension where
  reprPrec d _ :=
    if d.elements.isEmpty then
      "∅"
    else
      String.intercalate "·" (
        d.elements.map (
          fun (e : Base) => match e.exponent with
          | 1 => e.name
          | 2 => s!"{e.name}²"
          | 3 => s!"{e.name}³"
          | 4 => s!"{e.name}⁴"
          | 5 => s!"{e.name}⁵"
          | -1 => s!"{e.name}⁻¹"
          | -2 => s!"{e.name}⁻²"
          | -3 => s!"{e.name}⁻³"
          | -4 => s!"{e.name}⁻⁴"
          | -5 => s!"{e.name}⁻⁵"
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

def accel1 := Length * Time^(-1: ℚ) / Time * Length / Length
def accel2 := Length / Time ^ (2:ℚ)

#eval accel1 == accel2
#eval accel1 = accel2
#eval Length * Time^(-1: ℚ) / Time * Length / Length = Length / Time ^ (2:ℚ)

end Units.Dimension
