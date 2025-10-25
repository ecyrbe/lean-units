
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
@[simp]
theorem Scaler.scale_inv_scale_cancel {M : Type} [Scaler M] (m : M) :
  Scaler.scale_inv (Scaler.scale m) = m := by
  apply_fun Scaler.scale
  · rw [Scaler.scale_scale_inv_cancel]
  · exact Scaler.scale_inj

/--
This is just a restatement of scale_scale_inv_cancel to have a simp lemma.
-/
@[simp]
theorem Scaler.scale_scale_inv_cancel' {M : Type} [Scaler M] (m : M) :
  Scaler.scale (Scaler.scale_inv m) = m :=
  Scaler.scale_scale_inv_cancel m

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

theorem MulScaler.scale_smul_inv {M : Type} [MulAction α M] [MulScaler (α := α) M]
  (r : α) (m : M) :
  Scaler.scale_inv (r • m) = r • Scaler.scale_inv m := by
  apply_fun Scaler.scale
  · simp only [Scaler.scale_scale_inv_cancel, scale_smul]
  · exact Scaler.scale_inj

/--
A type `M` with an instance of `Scaler M` such that `scale` is compatible
with the `Module α M` instance on `M`.
-/
class LinearScaler (M : Type) [AddCommMonoid M] [Module α M]
  extends MulScaler (α := α) M where
  scale_add : ∀ m1 m2, scale (m1 + m2) = scale m1 + scale m2

theorem LinearScaler.scale_add_inv {M : Type} [AddCommMonoid M] [Module α M]
  [LinearScaler (α := α) M] (m1 m2 : M) :
  Scaler.scale_inv (m1 + m2) = Scaler.scale_inv m1 + Scaler.scale_inv m2 := by
  apply_fun Scaler.scale
  · simp only [Scaler.scale_scale_inv_cancel, LinearScaler.scale_add]
  · exact Scaler.scale_inj

/--
A type `M` with an instance of `Scaler M` such that `scale` is compatible
with the `Module α M` instance on `M`, and is continuous.
-/
class ContinuousLinearScaler (M : Type) [AddCommMonoid M] [Module α M] [TopologicalSpace M]
  extends LinearScaler (α := α) M where
  scale_cont : Continuous scale
  scale_inv_cont : Continuous scale_inv

/--
A quantity is a MulScaler if it has a Dimension.
-/
noncomputable instance instMulScalerQuantity [HasDimension δ] :
  MulScaler (α:=ℝ) (Quantity d ℝ)  where
  scale q := (𝒟 d).PrimeScale • q
  scale_inv q := Real.instInv.inv (𝒟 d).PrimeScale • q
  scale_inj := by
    intro q1 q2 h
    exact (Quantity.smul_inj (𝒟 d).PrimeScale q1 q2 Dimension.PrimeScale.scaler_ne_zero).mp h
  scale_scale_inv_cancel q := by
    exact smul_inv_smul₀ Dimension.PrimeScale.scaler_ne_zero q
  scale_smul := by
    intros r q
    rw [smul_comm]

@[simp]
lemma MulScaler.scale_def [HasDimension δ] (q : Quantity d ℝ) :
  Scaler.scale q = (𝒟 d).PrimeScale • q := by rfl

@[simp]
lemma MulScaler.scale_inv_def [HasDimension δ] (q : Quantity d ℝ) :
  Scaler.scale_inv q = Real.instInv.inv (𝒟 d).PrimeScale • q := rfl

lemma MulScaler.scale_def' [HasDimension δ] :
  Scaler.scale  = fun q : Quantity d ℝ => (𝒟 d).PrimeScale • q := rfl

lemma MulScaler.scale_inv_def' [HasDimension δ] :
  Scaler.scale_inv = fun q : Quantity d ℝ => Real.instInv.inv (𝒟 d).PrimeScale • q := rfl


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
lemma Scaler.scale_fun_out_def {M1 M2 : Type} [Scaler M2] (f : M1 → M2) (m1 : M1) :
    (scale f) m1 = scale (f m1) := rfl

@[simp]
lemma Scaler.scale_inv_fun_out_def {M1 M2 : Type} [Scaler M2] (f : M1 → M2) (m1 : M1) :
    (scale_inv f) m1 = scale_inv (f m1) := rfl

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
lemma Scaler.scale_fun_in_def {M1 M2 : Type} [Scaler M1] (f : M1 → M2) (m1 : M1) :
    (scale f) m1 = f (scale_inv m1) := rfl

@[simp]
lemma Scaler.scale_inv_fun_in_def {M1 M2 : Type} [Scaler M1] (f : M1 → M2) (m1 : M1) :
    (scale_inv f) m1 = f (scale m1) := rfl

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
lemma Scaler.scale_fun_def {M1 M2 : Type} [Scaler M1] [Scaler M2] (f : M1 → M2) (m1 : M1) :
    (scale f) m1 = scale (f (scale_inv m1)) := rfl

@[simp]
lemma Scaler.scale_inv_fun_def {M1 M2 : Type} [Scaler M1] [Scaler M2] (f : M1 → M2) (m1 : M1) :
    (scale_inv f) m1 = scale_inv (f (scale m1)) := rfl

noncomputable instance instMulScalerFunBi
  {M1 M2 : Type} [Scaler M1] [MulAction α M2] [MulScaler (α := α) M2] :
    MulScaler (α:=α) (M1 → M2) where
      scale_smul r f := by
        funext m1
        simpa using (MulScaler.scale_smul r (f (Scaler.scale_inv m1)))

noncomputable instance instLinearScalerQuantity [HasDimension δ] :
  LinearScaler (α:=ℝ) (Quantity d ℝ) where
  scale_add m1 m2 := by
    repeat rw [MulScaler.scale_def]
    rw [smul_add]

noncomputable instance instLinearScalerLinearMap {M1 M2 : Type} [AddCommMonoid M1] [Module α M1]
    [AddCommMonoid M2] [Module α M2] [LinearScaler (α := α) M2] :
    LinearScaler (α:=α) (M1 →ₗ[α] M2) where
  scale f := {
    toFun m1 :=  Scaler.scale (f m1)
    map_add' := by
      simp [LinearScaler.scale_add]
    map_smul' := by
      simp [MulScaler.scale_smul]
  }
  scale_inv f := {
    toFun m1 := Scaler.scale_inv (f m1)
    map_add' := by
      simp [LinearScaler.scale_add_inv]
    map_smul' := by
      simp [MulScaler.scale_smul_inv]
  }
  scale_inj := by
    intro f1 f2 h
    ext m1
    apply Scaler.scale_inj
    rw [LinearMap.mk.injEq, AddHom.mk.injEq] at h
    exact congrFun h m1
  scale_scale_inv_cancel f := by
    ext m1
    simp
  scale_add m1 m2 := by
    ext m1
    simp [LinearScaler.scale_add]
  scale_smul r f := by
    ext m1
    simp [MulScaler.scale_smul]

noncomputable instance instContinuousLinearScalerQuantity
  [HasDimension δ] [TopologicalSpace (Quantity d ℝ)] [ContinuousConstSMul ℝ (Quantity d ℝ)] :
  ContinuousLinearScaler (α:=ℝ) (Quantity d ℝ) where
  scale_cont := by
    rw [MulScaler.scale_def']
    apply Continuous.const_smul
    exact continuous_id'
  scale_inv_cont := by
    rw [MulScaler.scale_inv_def']
    apply Continuous.const_smul
    exact continuous_id'

/--
A Scaler is dimensionally correct if scaling it does not change its value.
So for example a dimensionless quantity is dimensionally correct.
-/
def IsDimensionallyCorrect {M : Type} [Scaler M] (m : M) : Prop :=
  Scaler.scale m = m

end Units.Quantity
