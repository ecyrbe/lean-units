import LeanUnits.Framework.Dimensions.Basic
import LeanUnits.Framework.Dimensions.Tactic
import LeanUnits.Framework.Conversions.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
namespace Units

variable {α δ : Type} [AddCommGroup δ] [Repr δ]

structure Quantity (dim : δ) (α : Type) [AddCommGroup δ] where
    val : α
    deriving Inhabited, BEq, DecidableEq

namespace Quantity

-- ### Operations on Quantities
variable {d d₁ d₂ : δ}

unsafe instance [Repr α] : Repr (Quantity d α) where
  reprPrec q _ := s!"{repr q.val} • {repr d}"

unsafe instance [Repr α] : ToString (Quantity d α) where
  toString q := reprStr q

instance [Zero α] : Zero (Quantity d α) where
  zero := ⟨ 0 ⟩

instance [One α] : One (Quantity d α) where
  one := ⟨ 1 ⟩

def add [Add α] (q1 q2 : Quantity d α) : Quantity d α := ⟨ q1.val + q2.val ⟩

instance [Add α] : Add (Quantity d α) where
  add := add

def sub [Sub α] (q1 q2 : Quantity d α) : Quantity d α := ⟨ q1.val - q2.val ⟩

instance [Sub α] : Sub (Quantity d α) where
  sub := sub

def neg [Neg α] (q : Quantity d α) : Quantity d α := ⟨ - q.val ⟩

instance [Neg α] : Neg (Quantity d α) where
  neg := neg

def hMul [Mul α] (q1 : Quantity d₁ α) (q2 : Quantity d₂ α) : Quantity (d₁ + d₂) α :=
  ⟨ q1.val * q2.val ⟩

instance [Mul α] : HMul (Quantity d₁ α) (Quantity d₂ α) (Quantity (d₁ + d₂) α) where
  hMul := hMul

def hDiv [Div α] (q1 : Quantity d₁ α) (q2 : Quantity d₂ α) : Quantity (d₁ - d₂) α :=
    ⟨ q1.val / q2.val ⟩

instance [Div α] : HDiv (Quantity d₁ α) (Quantity d₂ α) (Quantity (d₁ - d₂) α) where
  hDiv := hDiv

def sMul [SMul α α] (s : α) (q : Quantity d α) : Quantity d α := ⟨ s • q.val ⟩

instance [SMul α α] : SMul α (Quantity d α) where
    smul := sMul

def npow [Pow α ℕ] (q : Quantity d α) (n : ℕ) : Quantity (n•d) α := ⟨ q.val ^ n ⟩

def zpow [Pow α ℤ] (q : Quantity d α) (n : ℤ) : Quantity (n•d) α := ⟨ q.val ^ n ⟩

def qpow [Pow α ℚ] [SMul ℚ δ] (q : Quantity d α) (n : ℚ) : Quantity (n•d) α := ⟨ q.val ^ n ⟩

instance [Pow α ℕ] : DPow (Quantity d α) ℕ (fun n => Quantity (n • d) α) where
  pow := npow

instance [Pow α ℤ] : DPow (Quantity d α) ℤ (fun n => Quantity (n • d) α) where
  pow := zpow

instance [Pow α ℚ] [SMul ℚ δ] : DPow (Quantity d α) ℚ (fun n => Quantity (n • d) α) where
  pow := qpow

def inv [Inv α] (q : Quantity d α) : Quantity (-d) α := ⟨ q.val⁻¹ ⟩

def fun_to_val (f : Quantity d₁ α → Quantity d₂ α) : α → α := fun x => (f ⟨x⟩).val

-- derivative
noncomputable def deriv [NontriviallyNormedField α]
  (f : Quantity d₁ α → Quantity d₂ α) (x : Quantity d₁ α) : Quantity (d₂-d₁) α :=
  ⟨_root_.deriv (fun_to_val f) x.val⟩

-- integral
noncomputable def integral [NormedAddCommGroup α] [NormedSpace ℝ α] [MeasurableSpace α]
  (f : Quantity d₁ α → Quantity d₂ α) (μ : MeasureTheory.Measure α) : Quantity (d₁+d₂) α :=
  ⟨MeasureTheory.integral μ (fun_to_val f)⟩

-- order
def lt [LT α] (q1 q2 : Quantity d α) : Prop := q1.val < q2.val

instance [LT α] : LT (Quantity d α) where
    lt := lt

def le [LE α] (q1 q2 : Quantity d α) : Prop := q1.val ≤ q2.val

instance [LE α] : LE (Quantity d α) where
    le := le

def dimension [HasDimension δ] (_ : Quantity d α) : Dimension := 𝒟 d
def conversion [HasConversion δ] (_ : Quantity d α) : Conversion := 𝒞 d
def units (_ : Quantity d α) : δ := d

instance [HasDimension δ] : HasDimension (Quantity d α) where
  dimension := dimension

instance [HasConversion δ] : HasConversion (Quantity d α) where
  conversion := conversion

-- cast operator prefix
/--
Preferred notation for casting: write `↑x` instead of `cast x`.

- Purpose: `↑x` is equivalent to `cast x` and is the idiomatic, preferred syntax
    throughout this library. Please use this notation in new code and docs.
- Precedence: the operator has high priority and binds tightly; use parentheses
    when needed, e.g. `↑(f x)` or `(↑x).field`.
- Typing the symbol: in Lean/VSCode, type `\uparrow` then space to get `↑`.

Examples:
- `let q' : Quantity β := ↑q`    -- preferred
- -- instead of: `cast q`
-/
def cast [HasEquiv δ] (q : Quantity d₁ α) (_ : d₁ ≈ d₂ := by auto_equiv) : Quantity d₂ α := ⟨q.val⟩

/--
convert from one quantity to another of the same dimension

Preferred notation for convert: write `q →` instead of `convert q`.
- Purpose: `q →` is equivalent to `convert q` and is the idiomatic, preferred syntax
    throughout this library. Please use this notation in new code and docs.

Examples:
- `let q' : Quantity d₂ α := q →`    -- preferred
- -- instead of: `convert q`
-/
def convert [RatCast α] [Mul α] [Add α] [HasDimension δ] [HasConversion δ]
 (q : Quantity d₁ α) (_ : 𝒟 d₁ = 𝒟 d₂ := by auto_dim) : Quantity d₂ α :=
  ⟨Conversion.convert (𝒞 d₁) (𝒞 d₂) q.val⟩

/--
convert and cast in one step from one quantity to another of the same dimension
the target is a unit

Examples:
 convert constant c from natural unit to meter per second: c.into (Unit.meter-Unit.second)
-/
def into [RatCast α] [Mul α] [Add α] [HasDimension δ] [HasConversion δ]
 (q : Quantity d α) (target : δ) (_ : 𝒟 d = 𝒟 target := by auto_dim) : Quantity target α :=
  ⟨Conversion.convert (𝒞 d) (𝒞 target) q.val⟩

/--
convert and cast in one step from one quantity to another of the same dimension
the target is another quantity

Examples:
- `let q' : Quantity (Unit.meter-Unit.second) Float := q.as (m/s)`
-/
def as [RatCast α] [Mul α] [Add α] [HasDimension δ] [HasConversion δ]
 (q : Quantity d₁ α) (_ : Quantity d₂ α) (_ : 𝒟 d₁ = 𝒟 d₂ := by auto_dim) : Quantity d₂ α :=
  ⟨Conversion.convert (𝒞 d₁) (𝒞 d₂) q.val⟩


@[inherit_doc cast]
prefix:100 (priority := high) "↑" => cast

@[inherit_doc convert]
postfix:100 (priority := high) "→" => convert

-- notation for dependent power
-- example (q : Quantity d ℝ) (n : ℕ) : q^ᵈn = q.npow n := rfl
-- example (q : Quantity d ℝ) (n : ℤ) : q^ᵈn = q.zpow n := rfl
-- example [Pow ℝ ℚ] [SMul ℚ δ] (q : Quantity d ℝ) (n : ℚ) : q ^ᵈ n * q = q.qpow n * q := rfl

-- positive powers as superscript
postfix:max (priority := high) "²" => npow (n := 2)
postfix:max (priority := high) "³" => npow (n := 3)
postfix:max (priority := high) "⁴" => npow (n := 4)
postfix:max (priority := high) "⁵" => npow (n := 5)
postfix:max (priority := high) "⁶" => npow (n := 6)
postfix:max (priority := high) "⁷" => npow (n := 7)
postfix:max (priority := high) "⁸" => npow (n := 8)
postfix:max (priority := high) "⁹" => npow (n := 9)
-- negative powers as superscript
postfix:max (priority := high) "⁻²" => zpow (n := -2)
postfix:max (priority := high) "⁻³" => zpow (n := -3)
postfix:max (priority := high) "⁻⁴" => zpow (n := -4)
postfix:max (priority := high) "⁻⁵" => zpow (n := -5)
postfix:max (priority := high) "⁻⁶" => zpow (n := -6)
postfix:max (priority := high) "⁻⁷" => zpow (n := -7)
postfix:max (priority := high) "⁻⁸" => zpow (n := -8)
postfix:max (priority := high) "⁻⁹" => zpow (n := -9)
-- inverse as superscript
postfix:max (priority := high) "⁻¹" => inv

end Quantity

end Units
