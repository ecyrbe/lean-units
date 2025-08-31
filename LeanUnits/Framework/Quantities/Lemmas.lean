import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.InjSurj
import LeanUnits.Framework.Quantities.Basic

/-!
Credit to @TerrenceTao for these lemmas about Fomalizing quantities into the AddMonoidAlgebra.
The original source code under Apache License is there :
https://github.com/teorth/analysis/blob/18d4fd7253ff17a05133d9b6b120b5f08f5ce6ad/analysis/Analysis/Misc/UnitsSystem.lean
Permission was given to use his lemmas and definitions as a starting point for the formal
side of the library.
-/

namespace Units.Quantity

set_option linter.unusedSectionVars false

-- for Formal we work over a Field like ℝ or ℚ or ℂ
variable {α : Type} [Field α]
-- we require δ to be an AddCommGroup with an equivalence relation
variable {δ : Type} [AddCommGroup δ] [Setoid δ]
-- here d, d₁, d₂, d₃ can be any dimensions or units in δ
variable {d d₁ d₂ d₃ : δ}

/--
A Quantity can be formalized into an AddMonoidAlgebra
`Formal δ α = AddMonoidAlgebra α δ`
where
- δ is the type of dimensions or units, which is an AddCommGroup with an equivalence relation
- α is the type of scalars, which is a Semiring (we use a Field here for convenience)

This allows to use the machinery of AddMonoidAlgebra to prove lemmas about quantities.
For example, the multiplication of quantities is associative up to equivalence
-/
abbrev Formal (δ α) [Field α] [AddCommGroup δ] [Setoid δ] := AddMonoidAlgebra α δ

theorem eq_imp_equiv {μ} [Setoid μ] {u1 u2 : μ} (h : u1 = u2) : u1 ≈ u2 := by
  rw [h]

@[simp]
theorem val_inj (q₁ q₂ : Quantity d α) :
  q₁.val = q₂.val ↔ q₁ = q₂ := by
  constructor
  · intro h; cases q₁; cases q₂; congr
  · intro h; rw [h]

theorem cast_eq (q₁ : Quantity d₁ α) (q₂ : Quantity d₂ α) (h : d₁ = d₂ := by module)
  : q₁.val = q₂.val ↔ q₁ = q₂.cast (eq_imp_equiv h.symm) := by
  aesop


theorem cast_eq_symm (q₁ : Quantity d₁ α) (q₂ : Quantity d₂ α) (h : d₁ ≈ d₂ := by module)
  : q₁ = q₂.cast (Setoid.symm h) ↔ q₂ = q₁.cast h := by aesop

@[simp]
theorem cast_val (q : Quantity d₁ α) (h : d₁ = d₂ := by module)
  : (q.cast (eq_imp_equiv h)).val = q.val := by
  subst h
  rfl

@[coe]
noncomputable def toFormal (q : Quantity d α) : Formal δ α :=
  AddMonoidAlgebra.single d q.val

noncomputable instance instCoeFormal : CoeOut (Quantity d α) (Formal δ α) where
  coe := toFormal

@[simp]
theorem toFormal_inj (q₁ q₂: Quantity d α) :
  (q₁ : Formal δ α) = (q₂ : Formal δ α) ↔ q₁ = q₂ := by
  constructor
  · simp only [toFormal, ← val_inj]
    intro h
    replace h := congr($h d)
    repeat rw [Finsupp.single_eq_same] at h
    exact h
  · intro h
    rw [h]

@[simp]
theorem toFormal_cast (q : Quantity d₁ α) (h : d₁ = d₂ := by module) :
  ((q.cast (eq_imp_equiv h)):Formal δ α) = (q:Formal δ α) := by
  subst h
  rw [cast]

@[simp]
theorem val_zero : (0:Quantity d α).val = 0 := rfl

theorem neZero_iff (q : Quantity d α) : NeZero q ↔ q.val ≠ 0 := by
  simp only [_root_.neZero_iff, ne_eq, ← val_inj, val_zero]

@[simp, norm_cast]
theorem toFormal_zero : ((0:Quantity d α): Formal δ α) = 0 := by
  simp only [toFormal, val_zero, Finsupp.single_zero]

@[simp]
theorem val_add (q₁ q₂ : Quantity d α) : (q₁ + q₂).val = q₁.val + q₂.val := rfl

@[simp, norm_cast]
theorem toFormal_add (q₁ q₂ : Quantity d α) :
  ((q₁ + q₂:Quantity d α):Formal δ α) = (q₁:Formal δ α) + (q₂:Formal δ α) := by
  simp only [toFormal, val_add, Finsupp.single_add]

@[simp]
theorem val_neg (q : Quantity d α) : (-q).val = -q.val := rfl

instance instNeZero_neg (q : Quantity d α) [h : NeZero q] : NeZero (-q) := by
  rw [neZero_iff] at h ⊢
  simp only [val_neg, ne_eq, neg_eq_zero, h, not_false_eq_true]

@[simp, norm_cast]
theorem toFormal_neg (q : Quantity d α) :
  ((-q:Quantity d α):Formal δ α) = -(q:Formal δ α) := by
  simp only [toFormal, val_neg, Finsupp.single_neg]

@[simp]
theorem val_sub (q₁ q₂ : Quantity d α) : (q₁ - q₂).val = q₁.val - q₂.val := rfl

@[simp, norm_cast]
theorem toFormal_sub (q₁ q₂ : Quantity d α) :
  ((q₁ - q₂ :Quantity d α):Formal δ α) = (q₁:Formal δ α) - q₂ := by
  simp only [toFormal, val_sub, Finsupp.single_sub]

@[simp]
theorem val_smul [SMul α α] (n : α) (q : Quantity d α) : (n • q).val = n • q.val := rfl

instance instAddGroup : AddGroup (Quantity d α) where
  zero := Zero.zero
  add := Add.add
  neg := Neg.neg
  sub := Sub.sub
  nsmul n q := { val := n • q.val }
  zsmul n q := { val := n • q.val }
  zero_add := by
    intro q
    rw [← val_inj]
    simp only [val_add, val_zero, zero_add]
  add_zero := by
    intro q
    rw [← val_inj]
    simp only [val_add, val_zero, add_zero]
  add_assoc := by
    intro a b c
    rw [← val_inj]
    simp only [val_add, add_assoc]
  sub_eq_add_neg := by
    intro a b
    rw [← val_inj]
    simp only [val_sub, sub_eq_add_neg, val_add, val_neg]
  neg_add_cancel := by
    intro a
    rw [← val_inj]
    simp only [val_add, val_neg, neg_add_cancel, val_zero]
  nsmul_zero := by
    intro a
    rw [← val_inj]
    simp only [zero_nsmul, val_zero]
  nsmul_succ := by
    intro n a
    rw [← val_inj]
    simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one, add_mul, one_mul, val_add]
  zsmul_zero' := by
    intro a
    rw [← val_inj]
    simp only [zero_smul, val_zero]
  zsmul_succ' := by
    intro n a
    rw [← val_inj]
    simp only [zsmul_eq_mul, Int.cast_natCast, val_add,Nat.cast_succ, add_mul,
    val_add,add_mul, zsmul_eq_mul, Int.cast_add, Int.cast_natCast, Nat.succ_eq_add_one]
    ring
  zsmul_neg' := by
    intro n a
    rw [← val_inj]
    simp only [Int.negSucc_eq, zsmul_eq_mul, Int.cast_add, Int.cast_neg,
      Int.cast_natCast, Nat.succ_eq_add_one, Nat.cast_add, val_neg, neg_mul,Nat.cast_one]

instance : AddCommGroup (Quantity d α) where
  add_comm := by
    intro a b
    rw [← val_inj]
    simp only [val_add, add_comm]

@[coe]
def ofField {α} [Field α] (a : α) : Quantity (0: δ) α := ⟨ a ⟩

instance instCoeField : Coe α (Quantity (0: δ) α) where
  coe := ofField

@[simp]
theorem coe_val (a : α) : (a:Quantity (0: δ) α).val = a := rfl

@[norm_cast, simp]
theorem coe_zero : ((0:α):Quantity (0: δ) α) = 0 := rfl

theorem neZero_coe_iff {a : α} : NeZero (a: Quantity (0: δ) α) ↔ a ≠ 0 := by
  simp only [neZero_iff, coe_val, ne_eq]

@[simp]
theorem coe_inj {a b : α} :
  (a:Quantity (0: δ) α) = (b:Quantity (0: δ) α) ↔ a = b := by
  rw [ofField, ofField, mk.injEq]


theorem hMul_assoc (a : Quantity d₁ α) (b : Quantity d₂ α) (c : Quantity d₃ α) :
  a * (b * c) = ((a * b) * c).cast := by
  rw [←toFormal_inj, toFormal_cast]
  ring
  sorry

end Units.Quantity
