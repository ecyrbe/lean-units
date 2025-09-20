
import Mathlib.Algebra.Group.Action.Basic
import LeanUnits.Framework.Dimensions.Basic
import LeanUnits.Framework.Dimensions.Lemmas
import LeanUnits.Framework.Quantities.Basic
import LeanUnits.Framework.Quantities.Lemmas
import Mathlib.Data.Real.Basic

namespace Units.Quantity

-- for Formal we work over a Field like ℝ or ℚ or ℂ
variable {α : Type} [Field α]
-- we require δ to be an AddCommGroup with an equivalence relation
variable {δ : Type} [AddCommGroup δ] [Setoid δ]
-- here d, d₁, d₂, d₃ can be any dimensions or units in δ
variable {d d₁ d₂ d₃ d₄ : δ}


class Scaler (M : Type) where
  scale : M → M
  scale_inv: M → M
  scale_inj : Function.Injective scale
  scale_scale_inv_cancel : ∀ m, scale (scale_inv m) = m

/--
We can derive that scale_inv scales back to the original value because scale is injective.
-/
theorem Scaler.scale_inv_scale_cancel {M : Type} [Scaler M] (m : M) :
  Scaler.scale_inv (Scaler.scale m) = m := by
  apply_fun Scaler.scale
  · rw [Scaler.scale_scale_inv_cancel (Scaler.scale m)]
  · exact Scaler.scale_inj

/--
We can also derive that scale_inv is injective because scale is injective and they are inverses.
-/
theorem Scaler.scale_inv_inj {M : Type} [Scaler M] :
  Function.Injective (Scaler.scale_inv (M:=M)) := by
  intro x y h
  apply_fun Scaler.scale at h
  simpa [Scaler.scale_scale_inv_cancel] using h

class MulScaler (M : Type) [MulAction α M] extends Scaler M where
  scale_smul : ∀ (r : α) m, scale (r • m) = r • scale m

/--
A quantity is a MulScaler if it has a Dimension.
-/
noncomputable instance [HasDimension δ] : MulScaler (α:=ℝ) (Quantity d ℝ)  where
  scale q := ⟨(𝒟 q).PrimeScale * q.val⟩
  scale_inv q := ⟨q.val/ (𝒟 q).PrimeScale⟩
  scale_inj := by
    intro q1 q2 h
    simp only [dim_eq_dim, ← val_inj, mul_eq_mul_left_iff] at h
    cases h with
    | inl h1 => apply (val_inj q1 q2).mp h1
    | inr h2 => exfalso; exact Dimension.PrimeScale.scaler_ne_zero h2
  scale_scale_inv_cancel q := by
    simp only [dim_eq_dim, ← val_inj]
    rw [_root_.mul_comm,_root_.div_mul, _root_.div_self,_root_.div_one]
    exact Dimension.PrimeScale.scaler_ne_zero
  scale_smul := by
    intros r q
    simp only [smul_def, _root_.smul_eq_mul, dim_eq_dim, ← val_inj]
    ring

@[simp]
lemma Scaler.scale_apply [HasDimension δ] (q : Quantity d ℝ) :
  scale q = ⟨(𝒟 q).PrimeScale * q.val⟩ := rfl

noncomputable instance instScalerFunOut {M1 M2 : Type} [Scaler M2] : Scaler (M1 → M2) where
  scale f m1 := Scaler.scale (f m1)
  scale_inv f m1 := Scaler.scale_inv (f m1)
  scale_inj := by
    intro f1 f2 h
    funext m1
    apply Scaler.scale_inj
    exact congrFun h m1
  scale_scale_inv_cancel f := by
    funext m1
    apply Scaler.scale_scale_inv_cancel

@[simp]
lemma Scaler.scale_apply_fun_right {M1 M2 : Type} [Scaler M2] (f : M1 → M2) (m1 : M1) :
    (scale f) m1 = scale (f m1) := rfl

noncomputable instance instScalerFunIn {M1 M2 : Type} [Scaler M1] :
    Scaler (M1 → M2) where
  scale f m1 := f (Scaler.scale_inv m1)
  scale_inv f m1 := f (Scaler.scale m1)
  scale_inj := by
    intro f1 f2 h
    funext m1
    simpa [Scaler.scale_inv_scale_cancel] using congrFun h (Scaler.scale m1)
  scale_scale_inv_cancel f := by
    funext m1
    rw [Scaler.scale_scale_inv_cancel m1]

@[simp]
lemma Scaler.scale_apply_fun_left {M1 M2 : Type} [Scaler M1] (f : M1 → M2) (m1 : M1) :
    (scale f) m1 = f (scale_inv m1) := rfl

noncomputable instance instScalerFunBi {M1 M2 : Type} [Scaler M1] [Scaler M2] :
    Scaler (M1 → M2) where
  scale f m1 := Scaler.scale (f (Scaler.scale_inv m1))
  scale_inv f m1 := Scaler.scale_inv (f (Scaler.scale m1))
  scale_inj := by
    intro f1 f2 h
    funext m1
    apply Scaler.scale_inj
    simpa [Scaler.scale_inv_scale_cancel] using congrFun h (Scaler.scale m1)
  scale_scale_inv_cancel f := by
    funext m1
    repeat rw [Scaler.scale_scale_inv_cancel]

@[simp]
lemma Scaler.scale_apply_fun {M1 M2 : Type} [Scaler M1] [Scaler M2] (f : M1 → M2) (m1 : M1) :
    (scale f) m1 = scale (f (scale_inv m1)) := rfl

noncomputable instance instMulScalerFunBi
  {M1 M2 : Type} [Scaler M1] [MulAction α M2] [MulScaler (α := α) M2] :
    MulScaler (α:=α) (M1 → M2) where
      scale_smul r f := by
        funext m1
        simpa using (MulScaler.scale_smul r (f (Scaler.scale_inv m1)))

def IsDimensionallyCorrect {M : Type} [Scaler M] (m : M) : Prop :=
  Scaler.scale m = m

end Units.Quantity
