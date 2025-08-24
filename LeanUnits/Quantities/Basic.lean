import LeanUnits.Dimensions.Dfinsupp
import LeanUnits.Math
-- import ring tactic
import Mathlib

namespace Units

structure Quantity (dim : Dimension) (α : Type) where
  val : α
  deriving Inhabited, BEq, DecidableEq

namespace Quantity
open Units.Math

unsafe instance {α : Type} [Repr α] (dim : Dimension) :
  Repr (Quantity dim α) where
  reprPrec q _ := s!"{repr q.val} ({repr dim})"

unsafe instance {α : Type} [Repr α] (dim : Dimension) :
  ToString (Quantity dim α) where
  toString q := reprStr q

-- ### Operations on Quantities
variable {α : Type} {d d₁ d₂ : Dimension}

def add [Add α] (q1 q2 : Quantity d α) : Quantity d α :=
    { val := q1.val + q2.val }

instance [Add α] : Add (Quantity d α) where
  add := add

def sub [Sub α] (q1 q2 : Quantity d α) : Quantity d α :=
    { val := q1.val - q2.val }

instance [Sub α] : Sub (Quantity d α) where
  sub := sub

def neg [Neg α] (q : Quantity d α) : Quantity d α :=
    { val := -q.val }

instance [Neg α] : Neg (Quantity d α) where
  neg := neg

def hMul [Mul α] (q1 : Quantity d₁ α) (q2 : Quantity d₂ α) : Quantity (d₁ + d₂) α :=
    { val := q1.val * q2.val }

instance [Mul α] : HMul (Quantity d₁ α) (Quantity d₂ α) (Quantity (d₁ + d₂) α) where
  hMul := hMul

instance [Mul α] : HMul (Quantity d₁ α) (Quantity d₂ α) (Quantity (d₁ + d₂) α) where
  hMul := hMul

def hDiv [Div α] (q1 : Quantity d₁ α) (q2 : Quantity d₂ α) : Quantity (d₁ - d₂) α :=
    { val := q1.val / q2.val }

instance [Div α] : HDiv (Quantity d₁ α) (Quantity d₂ α) (Quantity (d₁ - d₂) α) where
  hDiv := hDiv

def sMul [Mul α] (s : α) (q : Quantity d α) : Quantity d α :=
    { val := s * q.val }

instance [Mul α] : HMul α (Quantity d α) (Quantity d α) where
    hMul := sMul

instance [Mul α] : HMul (Quantity d α) α (Quantity d α) where
    hMul q s := sMul s q

instance [Mul α] : SMul α (Quantity d α) where
    smul := sMul

def divS [Div α] (q : Quantity d α) (s : α) : Quantity d α :=
    { val := q.val / s }

instance [Div α] : HDiv (Quantity d α) α (Quantity d α) where
    hDiv := divS

def sDiv [Div α] (s : α) (q : Quantity d α) : Quantity (-d) α :=
    { val := s / q.val }

instance [Div α] : HDiv α (Quantity d α) (Quantity (-d) α) where
    hDiv := sDiv

def hInvSquare [Inv α] [Mul α] (q : Quantity d α) : Quantity (-2•d) α :=
    let inverse := q.val⁻¹
    { val := inverse * inverse }

instance [Inv α] [Mul α] : HIntPow (Quantity d α) (-2) (Quantity (-2•d) α) where
    hIntPow := hInvSquare

def hInv [Inv α] (q : Quantity d α) : Quantity (-d) α :=
    { val := q.val⁻¹ }

instance [Inv α] : HIntPow (Quantity d α) (-1) (Quantity (-d) α) where
    hIntPow := hInv


def hSquare [Mul α] (q : Quantity d α) : Quantity (2•d) α :=
    { val := q.val * q.val }

instance [Mul α] : HIntPow (Quantity d α) 2 (Quantity (2•d) α) where
    hIntPow := hSquare

def hCubic [Mul α] (q : Quantity d α) : Quantity (3•d) α :=
    { val := q.val * q.val * q.val }

instance [Mul α] : HIntPow (Quantity d α) 3 (Quantity (3•d) α) where
    hIntPow := hCubic

def hQuartic [Mul α] (q : Quantity d α) : Quantity (4•d) α :=
    { val := q.val * q.val * q.val * q.val }

instance [Mul α] : HIntPow (Quantity d α) 4 (Quantity (4•d) α) where
    hIntPow := hQuartic

def hQuintic [Mul α] (q : Quantity d α) : Quantity (5•d) α :=
    { val := q.val * q.val * q.val * q.val * q.val }

instance [Mul α] : HIntPow (Quantity d α) 5 (Quantity (5•d) α) where
    hIntPow := hQuintic

-- square root
def hSqrt [HSqrt α α] (q : Quantity d α) : Quantity ((1/2:ℚ)•d) α :=
    { val := √q.val }

instance [HSqrt α α] : HSqrt (Quantity d α) (Quantity ((1/2:ℚ)•d) α) where
    hSqrt := hSqrt

def lt [LT α] (q1 q2 : Quantity d α) : Prop :=
    q1.val < q2.val

instance [LT α] : LT (Quantity d α) where
    lt := lt

def le [LE α] (q1 q2 : Quantity d α) : Prop :=
    q1.val ≤ q2.val

instance [LE α] : LE (Quantity d α) where
    le := le

def cast {d d' : Dimension} (q : Quantity d α) (_ : d' = d := by module) : Quantity d' α :=
  ⟨q.val⟩

-- cast operator prefix
prefix:100 (priority := high) "↑" => cast

end Quantity

abbrev SI (dim : Dimension) := Quantity dim Float

instance : Inv Float where
  inv v := 1.0 / v


section si_base_units
set_option linter.style.commandStart false
set_option allowUnsafeReducibility true
unseal Rat

@[inline] def one       : SI Dimension.dimensionless := ⟨1.0⟩ -- 1 scalar
@[inline] def meter     : SI Dimension.Length := ⟨1.0⟩ -- 1 meter
@[inline] def kilogram  : SI Dimension.Mass := ⟨1.0⟩ -- 1 kilogram
@[inline] def second    : SI Dimension.Time := ⟨1.0⟩ -- 1 second
@[inline] def ampere    : SI Dimension.Current := ⟨1.0⟩ -- 1 ampere
@[inline] def kelvin    : SI Dimension.Temperature := ⟨1.0⟩ -- 1 kelvin
@[inline] def mole      : SI Dimension.AmountOfSubstance := ⟨1.0⟩ -- 1 mole
@[inline] def candela   : SI Dimension.LuminousIntensity := ⟨1.0⟩ -- 1 candela

unseal Rat.add Rat.mul Rat.sub Rat.neg Rat.inv Rat.div

def speed_of_light: SI Dimension.Speed := ↑(299792458.0 • meter * second⁻¹)
#eval! speed_of_light

def gravitational_constant: SI (3•Dimension.Length - (Dimension.Mass + 2•Dimension.Time)) :=
  6.67430e-11 • (meter³ / (kilogram * second²))
#eval gravitational_constant

def pi := 3.14159265358979323846

def solar_mass_kepler_formula
(period : SI Dimension.Time) (semi_major_axis : SI Dimension.Length): SI Dimension.Mass :=
  ↑(4.0 * pi^2  * semi_major_axis³ / (gravitational_constant*period²))

def earth_semi_major_axis := 1.496e11 • meter
def minute := 60.0 • second
def hour := 60.0 • minute
def day := 24.0 • hour
def year := 365.25 • day

def Currency := Dimension.ofString "C"
def dollar : SI Currency := ⟨1.0⟩

def earning_rate : SI (Currency - Dimension.Time) := (50.0 • dollar / second)
#eval earning_rate

def non_computable := kilogram/second + ↑(second/kilogram)
def computable := kilogram/second + ↑(second/kilogram)⁻¹


#eval solar_mass_kepler_formula year earth_semi_major_axis


end si_base_units

end Units
