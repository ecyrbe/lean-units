import LeanUnits.Dimensions.Normal
import LeanUnits.Math

namespace Units

structure Quantity (dim : Dimension) (α : Type) where
  val : α
  deriving Inhabited, BEq, DecidableEq

namespace Quantity
open Units.Math

instance {α : Type} [Repr α] (dim : Dimension) :
  Repr (Quantity dim α) where
  reprPrec q _ := s!"{repr q.val} ({repr dim})"

instance {α : Type} [Repr α] (dim : Dimension) :
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

def hMul [Mul α] (q1 : Quantity d₁ α) (q2 : Quantity d₂ α) : Quantity (d₁ * d₂) α :=
    { val := q1.val * q2.val }

instance [Mul α] : HMul (Quantity d₁ α) (Quantity d₂ α) (Quantity (d₁ * d₂) α) where
  hMul := hMul

instance [Mul α] : HMul (Quantity d₁ α) (Quantity d₂ α) (Quantity (d₁ * d₂) α) where
  hMul := hMul

def hDiv [Div α] (q1 : Quantity d₁ α) (q2 : Quantity d₂ α) : Quantity (d₁ / d₂) α :=
    { val := q1.val / q2.val }

instance [Div α] : HDiv (Quantity d₁ α) (Quantity d₂ α) (Quantity (d₁ / d₂) α) where
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

def sDiv [Div α] (s : α) (q : Quantity d α) : Quantity (d^(-1:ℚ)) α :=
    { val := s / q.val }

instance [Div α] : HDiv α (Quantity d α) (Quantity (d^(-1:ℚ)) α) where
    hDiv := sDiv

def hInvSquare [Inv α] [Mul α] (q : Quantity d α) : Quantity (d^(-2:ℚ)) α :=
    let inverse := q.val⁻¹
    { val := inverse * inverse }

instance [Inv α] [Mul α] : HIntPow (Quantity d α) (-2) (Quantity (d^(-2:ℚ)) α) where
    hIntPow := hInvSquare

def hInv [Inv α] (q : Quantity d α) : Quantity (d^(-1:ℚ)) α :=
    { val := q.val⁻¹ }

instance [Inv α] : HIntPow (Quantity d α) (-1) (Quantity (d^(-1:ℚ)) α) where
    hIntPow := hInv


def hSquare [Mul α] (q : Quantity d α) : Quantity (d^(2:ℚ)) α :=
    { val := q.val * q.val }

instance [Mul α] : HIntPow (Quantity d α) 2 (Quantity (d^(2:ℚ)) α) where
    hIntPow := hSquare

def hCubic [Mul α] (q : Quantity d α) : Quantity (d^(3:ℚ)) α :=
    { val := q.val * q.val * q.val }

instance [Mul α] : HIntPow (Quantity d α) 3 (Quantity (d^(3:ℚ)) α) where
    hIntPow := hCubic

def hQuartic [Mul α] (q : Quantity d α) : Quantity (d^(4:ℚ)) α :=
    { val := q.val * q.val * q.val * q.val }

instance [Mul α] : HIntPow (Quantity d α) 4 (Quantity (d^(4:ℚ)) α) where
    hIntPow := hQuartic

def hQuintic [Mul α] (q : Quantity d α) : Quantity (d^(5:ℚ)) α :=
    { val := q.val * q.val * q.val * q.val * q.val }

instance [Mul α] : HIntPow (Quantity d α) 5 (Quantity (d^(5:ℚ)) α) where
    hIntPow := hQuintic

-- square root
def hSqrt [HSqrt α α] (q : Quantity d α) : Quantity (d^(1/2:ℚ)) α :=
    { val := √q.val }

instance [HSqrt α α] : HSqrt (Quantity d α) (Quantity (d^(1/2:ℚ)) α) where
    hSqrt := hSqrt

def lt [LT α] (q1 q2 : Quantity d α) : Prop :=
    q1.val < q2.val

instance [LT α] : LT (Quantity d α) where
    lt := lt

def le [LE α] (q1 q2 : Quantity d α) : Prop :=
    q1.val ≤ q2.val

instance [LE α] : LE (Quantity d α) where
    le := le

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

def speed_of_light: SI Dimension.Speed := 299792458.0 • meter * second⁻¹
#eval! speed_of_light

end si_base_units

end Units
