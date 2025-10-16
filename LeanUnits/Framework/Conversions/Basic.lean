import Batteries.Data.Rat
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Init
import Mathlib.Data.Rat.Lemmas

namespace Units

/--
Affine conversion between units.

⚠️ Warning : Affine composition works when offset is zero `or` factor is 1
ie :
abbrev Affinable (c1 c2 : Conversion) : Prop :=
  (c1.factor = 1 ∧ c2.factor = 1) ∨ (c1.offset = 0 ∧ c2.offset = 0)

instance (c₁ c₂ : Conversion) : Decidable (Affinable c₁ c₂) := by infer_instance

But we can't eforce it in the instances below because there is no way to attach
the proof to the standard typeclasses.
We could attach it to `Conversion` but that would restrict it too much.
Indeed, it would prevent converting from celsius to fahrenheit directly.
-/
@[ext]
structure Conversion where
  factor : ℚ
  offset : ℚ
  factor_ne_zero : factor ≠ 0
deriving Repr, DecidableEq, BEq

class HasConversion (μ : Type) where
  conversion (u : μ) : Conversion

alias 𝒞 := HasConversion.conversion

namespace Conversion

def identity : Conversion := ⟨1,0, by decide⟩

instance : Inhabited Conversion where
  default := identity

def scale (s : ℚ) (h : s ≠ 0 := by simp) : Conversion := ⟨s,0, h⟩
def translate (t : ℚ) : Conversion := ⟨1,t, by decide⟩

def Scalable (c : Conversion) : Prop := c.offset = 0

instance instDecidableScalable (c : Conversion) : Decidable (Scalable c) := by
  dsimp [Scalable]
  infer_instance

-- proper affine transformations
def mul (c1 c2 : Conversion) : Conversion :=
  ⟨c1.factor * c2.factor, c1.offset * c2.factor + c2.offset, by
    simp only [ne_eq, mul_eq_zero, not_or]; exact ⟨c1.factor_ne_zero, c2.factor_ne_zero⟩
  ⟩

def inv (c : Conversion) : Conversion :=
  ⟨1/c.factor, -c.offset / c.factor, by
    simp only [one_div, ne_eq, inv_eq_zero]; exact c.factor_ne_zero
  ⟩

def div (c1 c2 : Conversion) : Conversion := mul c1 (inv c2)

@[simp]
instance : Mul Conversion where
  mul := mul

@[simp]
instance : Div Conversion where
  div := div

@[simp]
instance : Inv Conversion where
  inv := inv

/--
Apply the conversion to a value x
-/
def apply {α} [RatCast α] [Mul α] [Add α] (c : Conversion) (x : α) : α := x * c.factor  + c.offset

/--
Convert x from c1 to c2
-/
def convert {α} [RatCast α] [Mul α] [Add α] (c1 c2 : Conversion) (x : α) : α :=
  (c1 / c2).apply x

/-
AddCommGroup operations
-/

def add (c1 c2 : Conversion) : Conversion :=
  ⟨c1.factor * c2.factor, c1.offset + c2.offset, by
    simp only [ne_eq, mul_eq_zero, not_or]; exact ⟨c1.factor_ne_zero, c2.factor_ne_zero⟩
  ⟩

def neg (c : Conversion) : Conversion := ⟨1/c.factor, -c.offset, by
  simp only [one_div, ne_eq, inv_eq_zero]; exact c.factor_ne_zero⟩

def sub (c1 c2 : Conversion) : Conversion :=
  ⟨c1.factor / c2.factor, c1.offset - c2.offset, by
    simp only [ne_eq]
    apply div_ne_zero
    · exact c1.factor_ne_zero
    · exact c2.factor_ne_zero
  ⟩

def nsmul (s : ℕ) (c : Conversion) : Conversion :=
  ⟨c.factor ^ s, s*c.offset, by
    apply pow_ne_zero
    exact c.factor_ne_zero
  ⟩

def zsmul (s : ℤ) (c : Conversion) : Conversion :=
  ⟨c.factor ^ s, s*c.offset, by
    apply zpow_ne_zero
    exact c.factor_ne_zero
  ⟩

instance : Neg Conversion where
  neg c := neg c

instance : Zero Conversion where
  zero := identity

instance : Add Conversion where
  add := add

instance : Sub Conversion where
  sub := sub

instance : SMul ℕ Conversion where
  smul := nsmul

instance : SMul ℤ Conversion where
  smul := zsmul

theorem zero_add' (c : Conversion) : add identity c = c := by
  simp only [add, identity, one_mul, zero_add]

theorem zero_add (c : Conversion) : 0 + c = c := by
  apply zero_add'

theorem add_zero' (c : Conversion) : add c identity = c := by
  simp only [add, identity, mul_one, add_zero]

theorem add_zero (c : Conversion) : c + 0 = c := by
  apply add_zero'

theorem add_comm' (c1 c2 : Conversion) : add c1 c2 = add c2 c1 := by
  simp only [add, Rat.mul_comm, Rat.add_comm]

theorem add_comm (c1 c2 : Conversion) : c1 + c2 = c2 + c1 := by
  apply add_comm'

theorem add_assoc' (c1 c2 c3 : Conversion) : add (add c1 c2) c3 = add c1 (add c2 c3) := by
  simp only [add, Rat.mul_assoc, Rat.add_assoc]

theorem add_assoc (c1 c2 c3 : Conversion) : (c1 + c2) + c3 = c1 + (c2 + c3) := by
  apply add_assoc'

theorem neg_add_cancel' (c : Conversion) : add (neg c) c = identity := by
  simp only [add, neg, one_div, ne_eq, c.factor_ne_zero, not_false_eq_true, inv_mul_cancel₀,
    neg_add_cancel, identity]

theorem neg_add_cancel (c : Conversion) : -c + c = 0 := by
  apply neg_add_cancel'


theorem nsmul_zero (c : Conversion) : nsmul (0: Nat) c = identity := by
  simp only [nsmul, pow_zero, Nat.cast_zero, zero_mul, identity]

theorem nsmul_succ (s : Nat) (c : Conversion) : nsmul (s+1) c = add (nsmul s c) c := by
  ext
  · simp only [nsmul, pow_succ, Nat.cast_add, Nat.cast_one, add]
  · simp only [nsmul, Nat.cast_add, Nat.cast_one, add_mul, one_mul, add]

theorem sub_eq_add_neg' (c1 c2 : Conversion) : sub c1 c2 = add c1 (neg c2) := by
  ext
  · simp only [sub, div_eq_mul_inv, add, neg, one_mul]
  · simpa only [sub, add, neg] using (sub_eq_add_neg (c1.offset) (c2.offset))

theorem sub_eq_add_neg (c1 c2 : Conversion) : c1 - c2 = c1 + (neg c2) := by
  apply sub_eq_add_neg'

theorem zsmul_zero' (c : Conversion) : zsmul (0: Int) c = identity := by
  ext
  · simp only [zsmul, zpow_zero, Int.cast_zero, zero_mul, identity]
  · simp only [zsmul, zpow_zero, Int.cast_zero, zero_mul, identity]

theorem zsmul_add_one (s : Int) (c : Conversion) : zsmul (s+1) c = add (zsmul s c) c := by
  ext
  · have h : c.factor ^ (s + 1) = c.factor ^ s * c.factor :=
      zpow_add_one₀ (a := c.factor) (n := s) (by exact c.factor_ne_zero)
    simpa only [zsmul, add] using h
  · simp only [zsmul, Int.cast_add, Int.cast_one, add_mul, one_mul, add]

theorem zsmul_succ' (n : Nat) (c : Conversion) : zsmul (↑n.succ) c = zsmul (↑n) c + c := by
  simpa only [add] using (zsmul_add_one (s := (n : Int)) (c := c))

theorem zsmul_neg' (n : Nat) (c : Conversion) :
  zsmul (Int.negSucc n) c = (zsmul (↑n.succ) c).neg := by
  ext
  · simp only [zsmul, zpow_negSucc, pow_succ, mul_inv_rev, Int.cast_negSucc, Nat.cast_add,
    Nat.cast_one, neg_add_rev, neg, Nat.succ_eq_add_one, zpow_add_one₀ c.factor_ne_zero,
    zpow_natCast, Int.cast_add, Int.cast_natCast, Int.cast_one, one_div]
  · simp only [zsmul, neg, Int.cast_negSucc, neg_mul, Nat.cast_succ,
     Int.cast_add, Int.cast_natCast, Int.cast_one]

instance : AddCommGroup Conversion  where
  add := add
  zero := identity
  neg := neg
  sub := sub
  nsmul := nsmul
  zsmul := zsmul
  zero_add := zero_add
  add_zero := add_zero
  add_assoc := add_assoc
  add_comm := add_comm
  neg_add_cancel := neg_add_cancel
  nsmul_zero := nsmul_zero
  nsmul_succ := nsmul_succ
  sub_eq_add_neg := sub_eq_add_neg
  zsmul_zero' := zsmul_zero'
  zsmul_succ' := zsmul_succ'
  zsmul_neg' := zsmul_neg'

end Conversion

end Units
