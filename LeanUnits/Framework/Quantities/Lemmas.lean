import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.InjSurj
import LeanUnits.Framework.Quantities.Basic
import Mathlib.Tactic

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
variable {d d₁ d₂ d₃ d₄ : δ}

theorem dim_eq_dim {d : δ} [HasDimension δ] (q : Quantity d α) :
  𝒟 q = 𝒟 d := by rfl



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

@[simp]
theorem val_zero : (0:Quantity d α).val = 0 := rfl

@[simp]
theorem val_one : (1:Quantity d α).val = 1 := rfl

theorem neZero_iff (q : Quantity d α) : NeZero q ↔ q.val ≠ 0 := by
  simp only [_root_.neZero_iff, ne_eq, ← val_inj, val_zero]

@[simp]
theorem val_add (q₁ q₂ : Quantity d α) : (q₁ + q₂).val = q₁.val + q₂.val := rfl

@[simp]
theorem val_neg (q : Quantity d α) : (-q).val = -q.val := rfl

instance instNeZero_neg (q : Quantity d α) [h : NeZero q] : NeZero (-q) := by
  rw [neZero_iff] at h ⊢
  simp only [val_neg, ne_eq, neg_eq_zero, h, not_false_eq_true]

@[simp]
theorem val_sub (q₁ q₂ : Quantity d α) : (q₁ - q₂).val = q₁.val - q₂.val := rfl

@[simp]
theorem val_smul [SMul α α] (n : α) (q : Quantity d α) : (n • q).val = n • q.val := rfl

theorem smul_def [SMul α α] (n : α) (q : Quantity d α) : (n • q) = ⟨n • q.val⟩ := rfl

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

@[simp]
theorem val_mul [Mul α] (q₁ : Quantity d₁ α) (q₂ : Quantity d₂ α) :
  (q₁ * q₂).val = q₁.val * q₂.val := rfl

@[simp]
theorem val_div [Div α] (q₁ : Quantity d₁ α) (q₂ : Quantity d₂ α) :
  (q₁ / q₂).val = q₁.val / q₂.val := rfl

@[simp]
theorem val_inv [Inv α] (q : Quantity d α) : (q⁻¹).val = Inv.inv q.val := rfl

@[simp]
theorem val_npow [Pow α ℕ] (q : Quantity d α) (n : ℕ) :
  (q.npow n).val = q.val ^ n := rfl

@[simp]
theorem val_zpow [Pow α ℤ] (q : Quantity d α) (n : ℤ) :
  (q.zpow n).val = q.val ^ n := rfl

@[simp]
theorem Scalar.val_pow (q : Quantity d α) (n : ℕ) :
  (q ^ᵈ n).val = q.val ^ n := rfl

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
  rw [ofField, ofField, ←val_inj]

@[norm_cast, simp]
theorem coe_add (a b : α) :
  ((a+b:α):Quantity (0: δ) α) = (a:Quantity (0: δ) α) + (b:Quantity (0: δ) α) := rfl

@[norm_cast, simp]
theorem coe_neg (a : α) : ((-a:α):Quantity (0: δ) α) = -(a: Quantity (0:δ) α) := rfl

@[norm_cast, simp]
theorem coe_sub (a b : α) :
  ((a-b:α):Quantity (0:δ) α) = (a:Quantity (0:δ) α) - (b:Quantity (0:δ) α) := by
  simp only [ofField]
  rfl

def differentiable [NontriviallyNormedField α]
  (f : Quantity d₁ α → Quantity d₂ α) : Prop := Differentiable α (fun t : α => (f ⟨t⟩).val)

theorem differentiable_fun_id [NontriviallyNormedField α] :
  differentiable (fun t : Quantity d₁ α => t) := by
  rw [differentiable]
  exact _root_.differentiable_fun_id

theorem deriv_qconst [NontriviallyNormedField α] (x : Quantity d₁ α) (c : Quantity d₂ α) :
  deriv (fun _ => c ) x = 0 := by
  rw [← val_inj]
  simp only [deriv]
  exact _root_.deriv_const x.val c.val

theorem deriv_id [NontriviallyNormedField α] (x : Quantity d₁ α) :
  deriv (fun t => t) x = 1 := by
  rw [← val_inj]
  simp only [deriv]
  exact _root_.deriv_id x.val

-- to do generalize to α, but we get errors for now
theorem deriv_const_smul_real
  {f : Quantity d₁ ℝ → Quantity d₂ ℝ} {x : Quantity d₁ ℝ}
  (c : ℝ) (h_f_diff : differentiable f) :
  deriv (fun t => c • f t) x = c • deriv f x := by
  rw [← val_inj]
  simp only [deriv, val_smul]
  exact deriv_const_smul c h_f_diff.differentiableAt

theorem deriv_qconst_mul_real
  (c : Quantity d₃ ℝ) (f : Quantity d₁ ℝ → Quantity d₂ ℝ) (x : Quantity d₁ ℝ)
  (h_f_diff : differentiable f) :
  deriv (fun t => c * (f t) ) x = ↑(c * deriv f x) := by
  rw [← val_inj]
  simp only [deriv]
  exact deriv_const_mul c.val h_f_diff.differentiableAt

theorem deriv_add_real
  (f g : Quantity d₁ ℝ → Quantity d₂ ℝ) (x : Quantity d₁ ℝ)
  (h_f_diff : differentiable f) (h_g_diff : differentiable g) :
  deriv (f + g) x = deriv f x + deriv g x := by
  rw [← val_inj]
  simp only [deriv, val_add]
  exact deriv_add (h_f_diff.differentiableAt) (h_g_diff.differentiableAt)

theorem deriv_mul_real
  (f : Quantity d₁ ℝ → Quantity d₂ ℝ) (g : Quantity d₁ ℝ → Quantity d₃ ℝ) (x : Quantity d₁ ℝ)
  (h_f_diff : differentiable f) (h_g_diff : differentiable g) :
  deriv (fun t => (f t) * (g t)) x = ↑(deriv f x * g x + ↑(f x * deriv g x)) := by
  rw [← val_inj]
  simp only [deriv]
  exact deriv_mul (h_f_diff.differentiableAt) (h_g_diff.differentiableAt)

theorem deriv_div_real
  (f : Quantity d₁ ℝ → Quantity d₂ ℝ) (g : Quantity d₁ ℝ → Quantity d₃ ℝ) (x : Quantity d₁ ℝ)
  (h_f_diff : differentiable f) (h_g_diff : differentiable g) [h_gx : NeZero (g x)] :
  deriv (fun t => (f t) / (g t)) x =
    ↑((deriv f x * g x - ↑(f x * deriv g x)) / (g x)²) := by
  rw [← val_inj]
  simp [deriv, cast]
  rw [neZero_iff] at h_gx
  exact deriv_div (h_f_diff.differentiableAt) (h_g_diff.differentiableAt) h_gx

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

namespace Formal


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

@[simp, norm_cast]
theorem toFormal_zero : ((0:Quantity d α): Formal δ α) = 0 := by
  simp only [toFormal, val_zero, Finsupp.single_zero]

@[simp, norm_cast]
theorem toFormal_one : ((1:Quantity (0:δ) α): Formal δ α) = 1 := by
  simp only [toFormal, val_one]
  rfl

@[simp, norm_cast]
theorem toFormal_add (q₁ q₂ : Quantity d α) :
  ((q₁ + q₂:Quantity d α):Formal δ α) = (q₁:Formal δ α) + (q₂:Formal δ α) := by
  simp only [toFormal, val_add, Finsupp.single_add]

@[simp, norm_cast]
theorem toFormal_neg (q : Quantity d α) :
  ((-q:Quantity d α):Formal δ α) = -(q:Formal δ α) := by
  simp only [toFormal, val_neg, Finsupp.single_neg]

@[simp, norm_cast]
theorem toFormal_sub (q₁ q₂ : Quantity d α) :
  ((q₁ - q₂ :Quantity d α):Formal δ α) = (q₁:Formal δ α) - (q₂:Formal δ α) := by
  simp only [toFormal, val_sub, Finsupp.single_sub]

@[norm_cast, simp]
theorem toFormal_pow (q : Quantity d α) (n : ℕ) :
  ((q ^ᵈ n):Formal δ α) = (q:Formal δ α) ^ n := by
  simp [toFormal, AddMonoidAlgebra.single_pow]

@[norm_cast, simp]
theorem toFormal_sq (q : Quantity d α) :
  ((q²):Formal δ α) = (q:Formal δ α) ^ 2 := by
  simp [toFormal, AddMonoidAlgebra.single_pow]

@[norm_cast, simp]
theorem toFormal_cube (q : Quantity d α) :
  ((q³):Formal δ α) = (q:Formal δ α) ^ 3 := by
  simp [toFormal, AddMonoidAlgebra.single_pow]


@[simp]
theorem pow_inv (q : Quantity d α) (n : ℕ) : (q ^ᵈ n)⁻¹ = ↑(q⁻¹ ^ᵈ n) := by
  simp [←toFormal_inj, toFormal]

noncomputable instance instCoeReal : Coe α (Formal δ α) where
  coe a := ((a:Quantity (0:δ) α):Formal δ α)

@[norm_cast, simp]
theorem coe_zero : ((0:α): Formal δ α) = 0 := by
  simp only [Quantity.coe_zero, toFormal_zero]

@[norm_cast, simp]
theorem coe_one : ((1:α):Formal δ α) = 1 := by
  rfl

@[norm_cast, simp]
theorem coe_nat (n : ℕ) : ((n:α):Formal δ α) = (n:Formal δ α) := by
  rfl

@[norm_cast, simp]
theorem coe_int (n : ℤ) : ((n:α):Formal δ α) = (n:Formal δ α) := by
  rfl

@[norm_cast, simp]
theorem toFormal_smul (c : α) (q : Quantity d α)
  : ((c • q:Quantity d α):Formal δ α) = (c:Formal δ α) * (q:Formal δ α) := by
  simp only [toFormal, val_smul, _root_.smul_eq_mul, coe_val, AddMonoidAlgebra.single_mul_single,
    zero_add]

@[simp]
theorem smul_eq_mul (c : α) (x : Formal δ α) : c • x = (c:Formal δ α) * x := by
  ext n
  rw [toFormal, coe_val]
  rw [Finsupp.smul_apply, AddMonoidAlgebra.single_zero_mul_apply, _root_.smul_eq_mul]

@[simp]
theorem nsmul_eq_mul (c : ℕ) (x : Formal δ α) : c • x = (c:Formal δ α) * x := by
  rw [_root_.nsmul_eq_mul]

@[simp]
theorem zsmul_eq_mul (c : ℤ) (x : Formal δ α) : c • x = (c : Formal δ α) * x := by
  rw [_root_.zsmul_eq_mul]

end Formal

@[norm_cast, simp]
theorem coe_mul (a b : α) : ((a*b:α):Quantity (0: δ) α) = a • (b:Quantity (0:δ) α) := by
  simp only [ofField]
  rfl

instance instModule : Module α (Quantity d α) where
  smul_add c q₁ q₂ := by simp [←Formal.toFormal_inj]; ring
  add_smul c1 c2 q := by simp [←Formal.toFormal_inj]; ring
  one_smul q := by simp [←Formal.toFormal_inj]
  zero_smul q := by simp [←Formal.toFormal_inj]
  mul_smul c1 c2 q := by simp [←Formal.toFormal_inj]; ring
  smul_zero c := by simp [←Formal.toFormal_inj]

instance instMulAction : MulAction α (Quantity d α) where
  smul := (· • ·)
  one_smul := by simp only [one_smul, implies_true]
  mul_smul := by simp only [mul_smul, implies_true]

@[simp]
theorem val_nsmul (c : ℕ) (q : Quantity d α) : (c • q).val = c * q.val := by
  simp [←Nat.cast_smul_eq_nsmul α]

@[simp]
theorem val_zsmul (c : ℤ) (q : Quantity d α) : (c • q).val = c * q.val := by
  simp [←Int.cast_smul_eq_zsmul α]

@[norm_cast, simp]
theorem toFormal_nsmul (c : ℕ) (q : Quantity d α)
  : ((c • q:Quantity d α):Formal δ α) = (c:Formal δ α) * (q:Formal δ α) := by
  simp [←Nat.cast_smul_eq_nsmul α]

@[norm_cast, simp]
theorem toFormal_zsmul (c : ℤ) (q : Quantity d α)
  : ((c • q:Quantity d α):Formal δ α) = (c:Formal δ α) * (q:Formal δ α) := by
  simp [←Int.cast_smul_eq_zsmul α]

@[norm_cast, simp]
theorem toFormal_mul (q₁ : Quantity d₁ α) (q₂ : Quantity d₂ α) :
  ((q₁ * q₂:Quantity (d₁+d₂) α):Formal δ α) = (q₁:Formal δ α) * (q₂:Formal δ α) := by
  simp [Formal.toFormal, AddMonoidAlgebra.single_mul_single]

theorem mul_one (a : Quantity d₁ α) (h : d₁ = d₁ + d₂ := by module) :
  a * (1: Quantity (d₂:δ) α) = a.cast (eq_imp_equiv h) := by
  rw [←val_inj,val_mul, val_one,_root_.mul_one]
  rfl

theorem mul_one' (a : Quantity d α) :
  a * (1: Quantity (0:δ) α) = ↑a := by
  rw [mul_one]

theorem one_mul (a : Quantity d₂ α) (h : d₂ = d₁ + d₂ := by module) :
  (1: Quantity (d₁:δ) α) * a = a.cast (eq_imp_equiv h) := by
  rw [← val_inj, val_mul, val_one, _root_.one_mul]
  rfl

theorem one_mul' (a : Quantity d α) :
  (1: Quantity (0:δ) α) * a = ↑a := by
  rw [one_mul]

theorem mul_zero (a : Quantity d₁ α) (h : d₁ = d₁ + d₂ := by module) :
  a * (0: Quantity (d₂:δ) α) = (0: Quantity d₁ α).cast (eq_imp_equiv h) := by
  rw [← val_inj, val_mul, val_zero, MulZeroClass.mul_zero]
  rfl

theorem mul_zero' (a : Quantity d α) :
  a * (0: Quantity (0:δ) α) = ↑(0: Quantity d α) := by
  rw [mul_zero]

theorem zero_mul (a : Quantity d₂ α) (h : d₂ = d₁ + d₂ := by module) :
  (0: Quantity (d₁:δ) α) * a = (0: Quantity d₂ α).cast (eq_imp_equiv h) := by
  rw [← val_inj, val_mul, val_zero, MulZeroClass.zero_mul]
  rfl

theorem zero_mul' (a : Quantity d α) :
  (0: Quantity (0:δ) α) * a = ↑(0: Quantity d α) := by
  rw [zero_mul]

theorem mul_eq_zero {a : Quantity d₁ α} {b : Quantity d₂ α} :
  a * b = 0 ↔ a = 0 ∨ b = 0 := by
  simp only [← val_inj, val_mul, val_zero, _root_.mul_eq_zero]

@[simp]
theorem mul_inv_cancel (a : Quantity d α) [h : NeZero a] :
  a * a⁻¹ = ↑(1: Quantity (0:δ) α) := by
  rw [neZero_iff] at h
  rw [← val_inj, val_mul, val_inv, cast_val, val_one]
  exact mul_inv_cancel₀ h

@[simp]
theorem inv_mul_cancel (a : Quantity d α) [h : NeZero a] :
  a⁻¹ * a = ↑(1: Quantity (0:δ) α) := by
  rw [neZero_iff] at h
  rw [← val_inj, val_mul, val_inv, cast_val, val_one]
  exact inv_mul_cancel₀ h

theorem mul_comm (a : Quantity d₁ α) (b : Quantity d₂ α) :
  a * b = ↑(b * a) := by
  rw [←Formal.toFormal_inj, Formal.toFormal_cast]
  repeat rw [toFormal_mul]
  ring

theorem mul_assoc (a : Quantity d₁ α) (b : Quantity d₂ α) (c : Quantity d₃ α) :
  a * (b * c) = ↑((a * b) * c) := by
  rw [←Formal.toFormal_inj, Formal.toFormal_cast]
  repeat rw [toFormal_mul]
  ring

theorem conj_eq_self (a : Quantity d₁ α) (b : Quantity d₂ α) [h : NeZero a] :
  a⁻¹ * b * a = ↑b := by
  rw [mul_comm, mul_assoc, mul_inv_cancel, ← Formal.toFormal_inj]
  simp

theorem conj_eq_self' (a : Quantity d₁ α) (b : Quantity d₂ α) [h : NeZero a] :
  a * b * a⁻¹ = ↑b := by
  rw [mul_comm, mul_assoc, inv_mul_cancel, ← Formal.toFormal_inj]
  simp

theorem left_distrib (a : Quantity d₁ α) (b c : Quantity d₂ α) :
  a * (b + c) = ↑(a * b + a * c) := by
  simp [←Formal.toFormal_inj]
  ring

theorem right_distrib (a b : Quantity d₁ α) (c : Quantity d₂ α) :
  (a + b) * c = ↑(a * c + b * c) := by
  simp [←Formal.toFormal_inj]
  ring

theorem square_add (a b : Quantity d α) : (a + b) ^ᵈ (2:ℕ) = a ^ᵈ 2 + ↑(2 • a * b) + b ^ᵈ 2 := by
  simp only [← Formal.toFormal_inj, Formal.toFormal_pow, Formal.toFormal_add]
  rw [Formal.toFormal_cast, toFormal_mul, toFormal_nsmul, Nat.cast_ofNat]
  ring

theorem sq_add (a b : Quantity d α) : (a + b)² = a² + ↑(2 • a * b) + b² := by
  simp [← Formal.toFormal_inj]
  rw [Formal.toFormal_cast, toFormal_mul, toFormal_nsmul, Nat.cast_ofNat]
  ring

@[simp]
theorem dim_def [HasDimension δ] (q : Quantity d α) : q.dimension = HasDimension.dimension d := rfl

end Units.Quantity
