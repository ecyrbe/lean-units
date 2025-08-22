/-
 SI system in Lean.
 Implement a generic unit system that can be used to define units of measurement.
-/
import Mathlib
import LeanUnits.Math

/-!
# A Type-Safe Unit System in Lean 4

This file implements a generic system for handling physical quantities with units.
The core design principle is to leverage Lean's dependent type system to ensure
dimensional correctness at compile time.

- `BaseDimension`: The 7 SI base dimensions.
- `Dimension`: A type representing the exponents of each base dimension.
- `Quantity`: A structure `Quantity α d` holding a value of type `α` with a
  dimension `d`.

Operations like addition and subtraction are only defined for quantities of the
same dimension. Multiplication and division compute the resulting dimension in
the type.
-/

-- custom operators for dimensions and quantities


namespace Units

open Math

-- ## 1. Defining the Base Dimensions

class BaseDimension (β : Type) where
  symbol : β → String
  units : β → String
  all : List β
  all_is_exhaustive : ∀ (b : β), b ∈ all

def Dimension (β : Type) [BaseDimension β] : Type := (β → ℤ)

namespace Dimension

def base {β : Type} (b : β) [BEq β] [BaseDimension β] : Dimension β :=
  fun b' => if b == b' then 1 else 0


instance instRepr {β : Type} [BaseDimension β] : Repr (Dimension β) where
  reprPrec d _ :=
    let parts := BaseDimension.all
      |>.map (fun b => (BaseDimension.symbol b, d b))
      |>.filter (fun (_, exp) => exp != 0)
      |>.map (fun (sym, exp) => s!"{sym}: {repr exp}")
    if parts.isEmpty then "dimensionless" else "{" ++ (String.intercalate ", " parts) ++ "}ᵈ"

def unitsRepr {β : Type} [BaseDimension β] (d : Dimension β) : String :=
  let parts := BaseDimension.all
    |>.map (fun b => (BaseDimension.units b, d b))
    |>.filter (fun (_, exp) => exp != 0)
    |>.map (fun (unit, exp) => if exp=1 then s!"{unit}" else s!"{unit}^{repr exp}")
  if parts.isEmpty then "scalar" else String.intercalate "•" parts

instance instBEq {β : Type} [BaseDimension β] : BEq (Dimension β) where
  beq d1 d2 := BaseDimension.all.all (fun b => d1 b == d2 b)

instance instInhabited {β : Type} [BaseDimension β] : Inhabited (Dimension β) where
  default := fun _ => 0

instance instLawfulBEq {β : Type} [BaseDimension β] [BEq β] : LawfulBEq (Dimension β) where
  eq_of_beq {d1 d2} h := by
    apply funext
    intro b
    simp [BEq.beq] at h
    apply h
    exact BaseDimension.all_is_exhaustive b
  rfl {d} := by
    simp [BEq.beq]

#check propext
#check Equiv

instance instDecidableEq {β : Type} [BEq β] [BaseDimension β] : DecidableEq (Dimension β) :=
fun x y =>
  match h : x == y with
  | false => .isFalse (not_eq_of_beq_eq_false h)
  | true => .isTrue (eq_of_beq h)

-- ## 2. Defining a Generic Dimension
def one {β : Type} [BaseDimension β] : Dimension β := fun _ => 0

instance instOne {β : Type} [BaseDimension β] : One (Dimension β) where
  one := one

def mul {β : Type} [BaseDimension β] (d1 d2 : Dimension β) : Dimension β :=
  fun b => d1 b + d2 b

instance instMul {β : Type} [BaseDimension β] : Mul (Dimension β) where
  mul := mul

def div {β : Type} [BaseDimension β] (d1 d2 : Dimension β) : Dimension β :=
  fun b => d1 b - d2 b

instance instDiv {β : Type} [BaseDimension β] : Div (Dimension β) where
  div := div

def pow {β : Type} [BaseDimension β] (d : Dimension β) (n : ℤ) : Dimension β :=
  fun b => d b * n

instance instPow {β : Type} [BaseDimension β] : Pow (Dimension β) ℤ where
  pow := pow

def inv {β : Type} [BaseDimension β] (d : Dimension β) : Dimension β :=
  fun b => -d b

instance instInv {β : Type} [BaseDimension β] : Inv (Dimension β) where
  inv := inv

def invSquare {β : Type} [BaseDimension β] (d : Dimension β) : Dimension β :=
  fun b => (d b) * -2

instance {β : Type} [BaseDimension β] : HIntPow (Dimension β) (-2) (Dimension β) where
  hIntPow := invSquare

def square {β : Type} [BaseDimension β] (d : Dimension β) : Dimension β :=
  fun b => (d b) * 2

instance {β : Type} [BaseDimension β] : HIntPow (Dimension β) 2 (Dimension β) where
  hIntPow  := square

def cubic {β : Type} [BaseDimension β] (d : Dimension β) : Dimension β :=
  fun b => (d b) * 3

instance {β : Type} [BaseDimension β] : HIntPow (Dimension β) 3 (Dimension β) where
  hIntPow := cubic

def quartic {β : Type} [BaseDimension β] (d : Dimension β) : Dimension β :=
  fun b => (d b) * 4

instance {β : Type} [BaseDimension β] : HIntPow (Dimension β) 4 (Dimension β) where
  hIntPow := quartic

def quintic {β : Type} [BaseDimension β] (d : Dimension β) : Dimension β :=
  fun b => (d b) * 5

instance {β : Type} [BaseDimension β] : HIntPow (Dimension β) 5 (Dimension β) where
  hIntPow := quintic

def sqrt {β : Type} [BaseDimension β] (d : Dimension β) : Dimension β :=
  fun b => (d b) / 2

instance {β : Type} [BaseDimension β] : HSqrt (Dimension β) (Dimension β) where
  hSqrt := sqrt

/-
  Proofs for dimension operations.
  Allows to define commutative, associative, and inverse properties for dimensions.
-/
theorem dim_mul_comm' {β : Type} [BaseDimension β] (d1 d2 : Dimension β) :
    mul d1 d2 = mul d2 d1 := by
  funext b
  repeat rw [mul]
  exact add_comm (d1 b) (d2 b)

theorem dim_mul_comm {β : Type} [BaseDimension β] (d1 d2 : Dimension β) :
    d1 * d2 = d2 * d1 := by
  apply dim_mul_comm'

theorem dim_mul_assoc' {β : Type} [BaseDimension β] (d1 d2 d3 : Dimension β) :
    mul (mul d1 d2) d3 = mul d1 (mul d2 d3) := by
  funext b
  repeat rw [mul]
  exact add_assoc (d1 b) (d2 b) (d3 b)

theorem dim_mul_assoc {β : Type} [BaseDimension β] (d1 d2 d3 : Dimension β) :
    d1 * d2 * d3 = d1 * (d2 * d3) := by
  apply dim_mul_assoc'

theorem dim_mul_inv_cancel' {β : Type} [BaseDimension β] (d : Dimension β) :
    mul d (inv d) = one := by
  funext b
  rw [mul, inv, one]
  exact sub_self (d b)

theorem dim_mul_inv_cancel {β : Type} [BaseDimension β] (d : Dimension β) :
    d * d⁻¹ = 1 := by
  apply dim_mul_inv_cancel'

theorem dim_inv_mul_cancel' {β : Type} [BaseDimension β] (d : Dimension β) :
    mul (inv d) d = one := by
  funext b
  rw [ mul, inv, one, add_comm]
  exact sub_self (d b)

theorem dim_inv_mul_cancel {β : Type} [BaseDimension β] (d : Dimension β) :
    d⁻¹ * d = 1 := by
  apply dim_inv_mul_cancel'

theorem dim_mul_one' {β : Type} [BaseDimension β] (d : Dimension β) :
    mul d one = d := by
  funext b
  rw [mul, one]
  exact add_zero (d b)

theorem dim_mul_one {β : Type} [BaseDimension β] (d : Dimension β) :
    d * 1 = d := by
  apply dim_mul_one'

theorem dim_one_mul' {β : Type} [BaseDimension β] (d : Dimension β) :
    mul one d = d := by
  funext b
  rw [mul, one]
  exact zero_add (d b)

theorem dim_one_mul {β : Type} [BaseDimension β] (d : Dimension β) :
    1 * d = d := by
  apply dim_one_mul'

theorem dim_mul_div_cancel' {β : Type} [BaseDimension β] (d1 d2 : Dimension β) :
    mul d1 (div d2 d1) = d2 := by
  funext b
  rw [mul, div]
  simp

theorem dim_mul_div_cancel {β : Type} [BaseDimension β] (d1 d2 : Dimension β) :
    d1 * (d2 / d1) = d2 := by
  apply dim_mul_div_cancel'

theorem dim_mul_inv_eq_div' {β : Type} [BaseDimension β] (d1 d2 : Dimension β) :
    mul d1 (inv d2) = div d1 d2 := by
  funext b
  rw [mul, inv, div]
  rfl

theorem dim_mul_inv_eq_div {β : Type} [BaseDimension β] (d1 d2 : Dimension β) :
    d1 * d2⁻¹ = d1 / d2 := by
  apply dim_mul_inv_eq_div'

theorem dim_mul_self_eq_pow_2' {β : Type} [BaseDimension β] (d : Dimension β) :
    mul d d = square d := by
  funext b
  rw [square, mul, mul_two]

theorem dim_mul_div_assoc' {β : Type} [BaseDimension β] (d1 d2 d3 : Dimension β) :
    mul d1 (div d2 d3) = div (mul d1 d2) d3 := by
  funext b
  rw [mul, div,div,mul]
  exact add_sub_assoc' (d1 b) (d2 b) (d3 b)

theorem dim_mul_div_assoc {β : Type} [BaseDimension β] (d1 d2 d3 : Dimension β) :
    d1 * (d2 / d3) = d1 * d2 / d3 := by
  apply dim_mul_div_assoc'

theorem dim_mul_self_eq_pow_2 {β : Type} [BaseDimension β] (d : Dimension β) :
    d * d = d² := by
  apply dim_mul_self_eq_pow_2'

theorem dim_aggreg_div_pow_2' {β : Type} [BaseDimension β] (d1 d2 : Dimension β) :
    square (div d1 d2) = div (square d1) (square d2) := by
  funext b
  rw [square, div, div, square, square]
  ring

theorem dim_aggreg_div_pow_2 {β : Type} [BaseDimension β] (d1 d2 : Dimension β) :
    (d1 / d2)² = d1² / d2² := by
  apply dim_aggreg_div_pow_2'

theorem dim_cubic_eq_mul_mul_self' {β : Type} [BaseDimension β] (d : Dimension β) :
    cubic d = mul (mul d d) d  := by
  funext b
  rw [cubic, mul, mul]
  ring

theorem dim_cubic_eq_mul_mul_self {β : Type} [BaseDimension β] (d : Dimension β) :
    d³ = d * d * d := by
  apply dim_cubic_eq_mul_mul_self'

theorem dim_quartic_eq_mul_mul_mul_self' {β : Type} [BaseDimension β] (d : Dimension β) :
    quartic d = mul (mul (mul d d) d) d := by
  funext b
  rw [quartic, mul, mul, mul]
  ring

theorem dim_quartic_eq_mul_mul_mul_self {β : Type} [BaseDimension β] (d : Dimension β) :
    d⁴ = d * d * d * d := by
  apply dim_quartic_eq_mul_mul_mul_self'

theorem dim_div_div_eq_div_mul' {β : Type} [BaseDimension β] (d1 d2 d3 : Dimension β) :
    div (div d1 d2) d3 = div d1 (mul d2 d3) := by
  funext b
  rw [div, div, div, mul]
  exact Int.sub_sub (d1 b) (d2 b) (d3 b)

theorem dim_div_div_eq_div_mul {β : Type} [BaseDimension β] (d1 d2 d3 : Dimension β) :
    d1 / d2 / d3 = d1 / (d2 * d3) := by
  apply dim_div_div_eq_div_mul'

theorem dim_div_of_div_eq_div_mul' {β : Type} [BaseDimension β] (d1 d2 d3 : Dimension β) :
    div d1 (div d2 d3) = div (mul d1 d3) d2 := by
  funext b
  rw [div, div, div, mul]
  exact sub_sub_eq_add_sub (d1 b) (d2 b) (d3 b)

theorem dim_div_of_div_eq_div_mul {β : Type} [BaseDimension β] (d1 d2 d3 : Dimension β) :
    d1 / (d2 / d3) = (d1 * d3) / d2 := by
  apply dim_div_of_div_eq_div_mul'

section simp_dim
open Lean Elab Tactic Meta

macro "simp_dim" : tactic =>
  `(tactic| simp_all [
    dim_mul_one,
    dim_one_mul,
    dim_inv_mul_cancel,
    dim_mul_div_cancel,
    dim_mul_div_assoc,
    dim_mul_inv_cancel,
    dim_mul_inv_eq_div,
    dim_mul_self_eq_pow_2,
    dim_aggreg_div_pow_2,
    ← dim_cubic_eq_mul_mul_self,
    ← dim_quartic_eq_mul_mul_mul_self,
    dim_div_div_eq_div_mul,
    dim_div_of_div_eq_div_mul,
    ← dim_mul_assoc
    ])

end simp_dim

instance {β : Type} [BaseDimension β] : MulOneClass (Dimension β) where
  one_mul := dim_one_mul
  mul_one := dim_mul_one

instance {β : Type} [BaseDimension β] : Semigroup (Dimension β) where
  mul_assoc := dim_mul_assoc

instance {β : Type} [BaseDimension β] : Monoid (Dimension β) where
  -- already has mul_one and one_mul from `MulOneClass` and mul_assoc from `Semigroup`

instance {β : Type} [BaseDimension β] : CommSemigroup (Dimension β) where
  mul_comm := dim_mul_comm

instance {β : Type} [BaseDimension β] : CommMonoid (Dimension β) where
  -- already has commutative monoid properties from `CommSemigroup`

instance {β : Type} [BaseDimension β] : DivInvMonoid (Dimension β) where
  -- already has div and inv from `Div` and `Inv`

instance {β : Type} [BaseDimension β] : Group (Dimension β) where
  inv_mul_cancel := dim_inv_mul_cancel

instance {β : Type} [BaseDimension β] : CommGroup (Dimension β) where
  -- already has commutative group properties from `CommMonoid`

end Dimension

-- ## 3. Defining a Quantity with a Dimension

structure Quantity {β : Type} [BaseDimension β] (dim : Dimension β) (α : Type) where
  val : α
  deriving Inhabited, BEq

namespace Quantity

instance {α : Type} [Repr α] {β : Type} [BaseDimension β] (dim : Dimension β) :
  Repr (Quantity dim α) where
  reprPrec q _ := s!"{repr q.val} ({Dimension.unitsRepr dim})"

instance {α : Type} [Repr α] {β : Type} [BaseDimension β] (dim : Dimension β) :
  ToString (Quantity dim α) where
  toString q := reprStr q

-- ### Operations on Quantities
variable {α : Type} {β : Type} [BaseDimension β] {d d₁ d₂ : Dimension β}

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

def sDiv [Div α] (s : α) (q : Quantity d α) : Quantity d⁻¹ α :=
    { val := s / q.val }

instance [Div α] : HDiv α (Quantity d α) (Quantity d⁻¹ α) where
    hDiv := sDiv

def hInvSquare [Inv α] [Mul α] (q : Quantity d α) : Quantity d⁻² α :=
    let inverse := q.val⁻¹
    { val := inverse * inverse }

instance [Inv α] [Mul α] : HIntPow (Quantity d α) (-2) (Quantity d⁻² α) where
    hIntPow := hInvSquare

def hInv [Inv α] (q : Quantity d α) : Quantity d⁻¹ α :=
    { val := q.val⁻¹ }

instance [Inv α] : HIntPow (Quantity d α) (-1) (Quantity d⁻¹ α) where
    hIntPow := hInv


def hSquare [Mul α] (q : Quantity d α) : Quantity d² α :=
    { val := q.val * q.val }

instance [Mul α] : HIntPow (Quantity d α) 2 (Quantity d² α) where
    hIntPow := hSquare

def hCubic [Mul α] (q : Quantity d α) : Quantity d³ α :=
    { val := q.val * q.val * q.val }

instance [Mul α] : HIntPow (Quantity d α) 3 (Quantity d³ α) where
    hIntPow := hCubic

def hQuartic [Mul α] (q : Quantity d α) : Quantity d⁴ α :=
    { val := q.val * q.val * q.val * q.val }

instance [Mul α] : HIntPow (Quantity d α) 4 (Quantity d⁴ α) where
    hIntPow := hQuartic

def hQuintic [Mul α] (q : Quantity d α) : Quantity d⁵ α :=
    { val := q.val * q.val * q.val * q.val * q.val }

instance [Mul α] : HIntPow (Quantity d α) 5 (Quantity d⁵ α) where
    hIntPow := hQuintic

-- square root
def hSqrt [HSqrt α α] (q : Quantity d α) : Quantity √d α :=
    { val := √q.val }

instance [HSqrt α α] : HSqrt (Quantity d α) (Quantity √d α) where
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

-- ## 4. Defining the SI System
inductive SIBaseDimension
  | Length | Mass | Time | Current | Temperature | Amount | LuminousIntensity
  deriving Repr, BEq, Hashable, Inhabited

instance : BaseDimension SIBaseDimension where
  symbol base := match base with
    | .Length => "L"
    | .Mass => "M"
    | .Time => "T"
    | .Current => "I"
    | .Temperature => "Θ"
    | .Amount => "N"
    | .LuminousIntensity => "J"

  units base := match base with
    | .Length => "m"
    | .Mass => "kg"
    | .Time => "s"
    | .Current => "A"
    | .Temperature => "K"
    | .Amount => "mol"
    | .LuminousIntensity => "cd"

  all := [.Length, .Mass, .Time, .Current, .Temperature, .Amount, .LuminousIntensity]
  all_is_exhaustive := by
    intro b
    cases b <;> simp


abbrev SIDimension := Dimension SIBaseDimension
abbrev SI (dim : SIDimension) := Quantity dim Float

instance : Inv Float where
  inv v := 1.0 / v

instance : HSqrt Float Float where
  hSqrt v := v.sqrt


-- ### SI Base Dimensions

/-- dimensionless -/
def O𝓭 : SIDimension := Dimension.one
/-- length dimension -/
def L𝓭 : SIDimension := Dimension.base .Length
/-- mass dimension -/
def M𝓭 : SIDimension := Dimension.base .Mass
/-- time dimension -/
def T𝓭 : SIDimension := Dimension.base .Time
/-- electric current dimension -/
def I𝓭 : SIDimension := Dimension.base .Current
/-- thermodynamic temperature dimension -/
def Θ𝓭 : SIDimension := Dimension.base .Temperature
/-- amount of substance dimension -/
def N𝓭 : SIDimension := Dimension.base .Amount
/-- luminous intensity dimension -/
def J𝓭 : SIDimension := Dimension.base .LuminousIntensity

#eval O𝓭
#eval L𝓭
#eval M𝓭
#eval T𝓭
#eval I𝓭
#eval Θ𝓭
#eval N𝓭
#eval J𝓭

def accel1 := L𝓭 / T𝓭 * L𝓭/L𝓭
def accel2 := L𝓭 * T𝓭.inv
#eval accel1 == accel2 -- should be true
#eval accel1 = accel2 -- should be true
section  prefixes
open Lean Elab Tactic Meta
set_option linter.style.commandStart false

def quetta := 1e30 -- 10^30
def ronna  := 1e27 -- 10^27
def yotta  := 1e24 -- 10^24
def zetta  := 1e21 -- 10^21
def exa    := 1e18 -- 10^18
def peta   := 1e15 -- 10^15
def tera   := 1e12 -- 10^12
def giga   := 1e9  -- 10^9
def mega   := 1e6  -- 10^6
def kilo   := 1e3  -- 10^3
def hecto  := 1e2  -- 10^2
def deca   := 1e1  -- 10^1
def deci   := 1e-1 -- 10^-1
def centi  := 1e-2 -- 10^-2
def milli  := 1e-3 -- 10^-3
def micro  := 1e-6 -- 10^-6
def nano   := 1e-9 -- 10^-9
def pico   := 1e-12 -- 10^-12
def femto  := 1e-15 -- 10^-15
def atto   := 1e-18 -- 10^-18
def zepto  := 1e-21 -- 10^-21
def yocto  := 1e-24 -- 10^-24
def ronto  := 1e-27 -- 10^-27
def quecto := 1e-30 -- 10^-30
def _one   := 1.0 -- 10^0

/--
  Define SI prefixes for a given unit symbol and dimension.
  Generates definitions for all SI prefixes with the specified dimension.

  Example:
  `define_si_prefixes m L𝓭` will create definitions for
  `mm`, `cm`, `km`, etc. for the meter unit symbol `m` and dimension `L𝓭`.
-/
macro "define_si_prefixes" unit_symbol:ident dim:ident : command => do
  let prefixes := #[
    ("Q", "quetta"), ("R", "ronna"), ("Y", "yotta"), ("Z", "zetta"),
    ("E", "exa"), ("P", "peta"), ("T", "tera"), ("G", "giga"),
    ("M", "mega"), ("k", "kilo"), ("h", "hecto"), ("da", "deca"), ("", "_one"),
    ("d", "deci"), ("c", "centi"), ("m", "milli"), ("μ", "micro"),
    ("n", "nano"), ("p", "pico"), ("f", "femto"), ("a", "atto"),
    ("z", "zepto"), ("y", "yocto"), ("r", "ronto"), ("q", "quecto")
  ]
  let defs ← prefixes.mapM fun (sym, val) =>
    let name := Name.mkSimple s!"{sym}{unit_symbol.getId}"
    let valIdent := mkIdent (Name.mkSimple val)
    `(@[inline] def $(mkIdent name) : SI $dim := ⟨$valIdent⟩)
  return TSyntax.mk <| mkNullNode defs

/--
  Define SI prefixes with an offset for a given unit symbol and dimension.
  Generates definitions for all SI prefixes with the specified dimension and an offset.
  The offset is applied to the value of the prefix.

  Example:
  `define_si_prefixes_with_offset g M𝓭 milli` will create definitions for
  `mg`, `cg`, `kg`, etc. for the gram unit symbol `g` and dimension `M𝓭`, with an offset of `milli`.
  This means that `g` will be defined as `⟨0.001 * 1.0⟩` relative to the base unit `kg`.
-/
macro "define_si_prefixes_with_offset" unit_symbol:ident dim:ident offset:ident : command => do
  let prefixes := #[
    ("Q", "quetta"), ("R", "ronna"), ("Y", "yotta"), ("Z", "zetta"),
    ("E", "exa"), ("P", "peta"), ("T", "tera"), ("G", "giga"),
    ("M", "mega"), ("k", "kilo"), ("h", "hecto"), ("da", "deca"), ("", "_one"),
    ("d", "deci"), ("c", "centi"), ("m", "milli"), ("μ", "micro"),
    ("n", "nano"), ("p", "pico"), ("f", "femto"), ("a", "atto"),
    ("z", "zepto"), ("y", "yocto"), ("r", "ronto"), ("q", "quecto")
  ]
  let defs ← prefixes.mapM fun (sym, val) =>
    let name := Name.mkSimple s!"{sym}{unit_symbol.getId}"
    let valIdent := mkIdent (Name.mkSimple val)
    `(@[inline] def $(mkIdent name) : SI $dim := ⟨$offset * $valIdent⟩)
  return TSyntax.mk <| mkNullNode defs

end prefixes

-- ### SI Base Units (as quantities with value 1.0)
section si_base_units
set_option linter.style.commandStart false

@[inline] def one       : SI O𝓭 := ⟨1.0⟩ -- 1 scalar
@[inline] def meter     : SI L𝓭 := ⟨1.0⟩ -- 1 meter
@[inline] def kilogram  : SI M𝓭 := ⟨1.0⟩ -- 1 kilogram
@[inline] def second    : SI T𝓭 := ⟨1.0⟩ -- 1 second
@[inline] def ampere    : SI I𝓭 := ⟨1.0⟩ -- 1 ampere
@[inline] def kelvin    : SI Θ𝓭 := ⟨1.0⟩ -- 1 kelvin
@[inline] def mole      : SI N𝓭 := ⟨1.0⟩ -- 1 mole
@[inline] def candela   : SI J𝓭 := ⟨1.0⟩ -- 1 candela

-- ## SI base Units prefixes

-- meters
define_si_prefixes m L𝓭
-- kilograms
define_si_prefixes_with_offset g M𝓭 milli
-- seconds
define_si_prefixes s T𝓭
@[inline] def minute : SI T𝓭 := ⟨60.0⟩ -- 1 minute
@[inline] def hour : SI T𝓭 := ⟨3600.0⟩ -- 1 hour
@[inline] def day : SI T𝓭 := ⟨86400.0⟩ -- 1 day = 24 hours
@[inline] def week : SI T𝓭 := ⟨604800.0⟩ -- 1 week = 7 days
-- amperes
define_si_prefixes A I𝓭
-- kelvins
define_si_prefixes K Θ𝓭
-- moles
define_si_prefixes mol N𝓭
-- candelas
define_si_prefixes cd J𝓭

-- ### SI Derived Dimensions
def frequency𝓭    : SIDimension := T𝓭.inv -- f = 1 / t
def velocity𝓭     : SIDimension := L𝓭 / T𝓭 -- v = d / t
def acceleration𝓭 : SIDimension := L𝓭 / T𝓭² -- a = v / t
def force𝓭        : SIDimension := M𝓭 * L𝓭 / T𝓭² -- F = m * a
def energy𝓭       : SIDimension := M𝓭 * L𝓭² / T𝓭²      -- E = M v²
def power𝓭        : SIDimension := M𝓭 * L𝓭² / T𝓭³       -- P = E / t
def charge𝓭       : SIDimension := I𝓭 * T𝓭 -- C = A·s
def voltage𝓭      : SIDimension := M𝓭 * L𝓭² / (T𝓭³ * I𝓭) -- V = P / I
def permeability𝓭 : SIDimension := M𝓭 * L𝓭 / (T𝓭 * I𝓭)² -- μ = F / I²
def farad𝓭        : SIDimension := T𝓭⁴ * I𝓭² / (M𝓭 * L𝓭²) -- F = C / V
def permittivity𝓭 : SIDimension := (T𝓭² * I𝓭)² / (M𝓭 * L𝓭³) -- ε = F / m

theorem velocity_def : velocity𝓭 = L𝓭 / T𝓭 := by
  rw [velocity𝓭]

theorem frequency_def : frequency𝓭 = T𝓭.inv := by
  rw [frequency𝓭]

#eval frequency𝓭
#eval velocity𝓭
#eval acceleration𝓭
#eval force𝓭
#eval energy𝓭
#eval power𝓭
#eval charge𝓭
#eval voltage𝓭
#eval permeability𝓭
#eval farad𝓭
#eval permittivity𝓭

-- ### SI Derived Units
def hertz    : SI frequency𝓭  := ⟨1.0⟩ -- 1 Hz = 1/s
def newton   : SI force𝓭      := ⟨1.0⟩ -- 1 N = 1 kg·m/s²
def joule    : SI energy𝓭     := ⟨1.0⟩ -- 1 J = 1 N·m = 1 kg·m²/s²
def watt     : SI power𝓭      := ⟨1.0⟩ -- 1 W = 1 J/s = 1 kg·m²/s³
def coulomb  : SI charge𝓭     := ⟨1.0⟩ -- 1 C = 1 A·s
def volt     : SI voltage𝓭    := ⟨1.0⟩ -- 1 V = 1 W/A = 1 kg·m²/(s³·A)

define_si_prefixes Hz frequency𝓭 -- Hertz
define_si_prefixes N force𝓭 -- Newton
define_si_prefixes J energy𝓭 -- Joule
define_si_prefixes W power𝓭 -- Watt
define_si_prefixes C charge𝓭 -- Coulomb
define_si_prefixes V voltage𝓭 -- Volt

-- ## 5. Some physical constants
def π     : Float := 3.14159265358979323846 -- π
def euler : Float := 2.71828182845904523536 -- e
def c   : SI (L𝓭 / T𝓭)  := ⟨299792458.0⟩ -- Speed of light in m/s
def g₀  : SI acceleration𝓭 := ⟨9.81⟩ -- Gravitational acceleration in m/s²
def h   : SI energy𝓭 := ⟨6.62607015e-34⟩ -- Planck's constant in J·s
def e   : SI charge𝓭 := ⟨1.602176634e-19⟩ -- Elementary charge in C
def N_A : SI N𝓭.inv := ⟨6.02214076e23⟩ -- Avogadro's number in mol⁻¹
def μ₀  : SI permeability𝓭 := ⟨4.0 * π * 1e-7⟩ -- Permeability of free space in N/A²
def ε₀  : SI permittivity𝓭 := ⟨1.0 / ((4.0 * π * 1e-7) * 299792458.0^2)⟩ -- Permittivity of free space in F/m
def K_B : SI (energy𝓭 / Θ𝓭) := ⟨1.380649e-23⟩ -- Boltzmann's constant in J/K

end si_base_units

open Lean Elab Tactic

def speedOfLightDeriv:= (1.0/√(ε₀*μ₀)) -- Speed of light in m/s
#eval speedOfLightDeriv -- Should yield 299792458.0 m/s
#eval c
def mass := 2.5 * kg  -- 2.5 kg
#eval mass
def distance := 10.0 * m      -- 10 m
#eval distance
def time := 2.0 * s      -- 2 s
#eval time
def frequency := 50.0 * Hz -- 50 Hz
#eval frequency
def force := mass * distance * time⁻² -- F = m * a
#eval force
def energy := force * distance -- W = F * d
#eval energy
def power := energy / time -- P = W / t
#eval power
def velocity := distance / time -- v = d / t
#eval velocity
def acceleration := velocity / time -- a = v / t
#eval acceleration
def current := 5.0 * A -- 5 A
#eval current
def temperature := 300.0 * K -- 300 K
#eval temperature
def luminousIntensity := 100.0 * cd -- 100 cd
#eval luminousIntensity
def energyInJoules := 1000.0 * J -- 1000 J
#eval energyInJoules
def powerInWatts := 1500.0 * W -- 1500 W
#eval powerInWatts
def forceInNewtons := 100.0 * N -- 100 N
#eval forceInNewtons
def velocityInMetersPerSecond := 20.0 * (m / s) -- 20 m/s
#eval velocityInMetersPerSecond
def charge := 1.0 * C -- 1 C (coulomb)
#eval charge
def speedOfLight := 299792458.0 * (m / s) -- Speed of light in m/s
#eval speedOfLight
def try_cast : SI acceleration𝓭 := m / s²
--  cast (by rw[velocity𝓭]; simp_dim) (meter * (((second* second)/second)/second) * second⁻¹)
#eval try_cast -- Should yield 1.0 m/s
def cinetic_energy (m : SI M𝓭) (v : SI velocity𝓭) : SI energy𝓭 :=
  cast (by rw [velocity𝓭, energy𝓭]; simp_dim) ((m * v²)/2.0)

end Units
