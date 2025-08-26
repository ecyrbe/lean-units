import LeanUnits.Framework.Dimensions.Basic
import LeanUnits.Framework.Units.Basic
import LeanUnits.Framework.Units.Tactic
import LeanUnits.Framework.Conversion
import LeanUnits.Math
-- import ring tactic
import Mathlib

namespace Units

variable {α δ : Type} [AddCommGroup δ] [SMul ℚ δ] [Repr δ] [UnitSystem δ]

structure Quantity (dim : δ) (α : Type) where
    val : α
    deriving Inhabited, BEq, DecidableEq

namespace Quantity
open Units.Math

-- ### Operations on Quantities
variable {d d₁ d₂ : δ}

unsafe instance [Repr α] : Repr (Quantity d α) where
  reprPrec q _ := s!"{repr q.val} ({repr d})"

unsafe instance [Repr α] : ToString (Quantity d α) where
  toString q := reprStr q

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

def dimension (_ : Quantity d α) : Dimension := UnitSystem.dimension d

def units (_ : Quantity d α) : δ := d

def cast (q : Quantity d₁ α) (_ : d₁ = d₂ := by module) : Quantity d₂ α :=
  ⟨q.val⟩

def convert [Coe ℚ α] [Mul α] [Add α] (q : Quantity d₁ α)
 (_ : UnitSystem.dimension d₁ = UnitSystem.dimension d₂ := by dimension_check) :
 Quantity d₂ α := ⟨((UnitSystem.conversion d₁).div (UnitSystem.conversion d₂) ).apply q.val⟩

def into [Coe ℚ α] [Mul α] [Add α] (q : Quantity d α) (target : δ)
 (_ : UnitSystem.dimension d = UnitSystem.dimension target := by dimension_check) :
 Quantity target α := ⟨((UnitSystem.conversion d).div (UnitSystem.conversion target)).apply q.val⟩

-- cast operator prefix
prefix:100 (priority := high) "↑" => cast

-- convert operator postfix
postfix:100 (priority := high) "→" => convert

end Quantity

end Units
