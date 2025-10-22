import LeanUnits.Framework.Units.Basic
import LeanUnits.Framework.Quantities.Lemmas
import LeanUnits.Framework.Quantities.Scaler
import LeanUnits.Systems.Formal
import LeanUnits.Systems.SI.Units
import Mathlib.Data.Real.Basic

namespace formal
open Units Real

abbrev WithDim (units : Dimension) := Quantity units ℝ
abbrev SI (units : Units.Unit) := Quantity units ℝ

section WithDim
variable (G : WithDim (Dimension.Length ^ 3 / (Dimension.Mass * Dimension.Time ^ 2)))
variable (c : WithDim Dimension.Speed)

theorem kepler_third_law
    (T : WithDim Dimension.Time) (a : WithDim Dimension.Length) (M m : WithDim Dimension.Mass) :
    T² =  (4•π^2) • ↑(a³/ (G *(M + m)))  := by
  sorry

theorem kepler_third_law_dim_check
    (T : WithDim Dimension.Time) (a : WithDim Dimension.Length) (M m : WithDim Dimension.Mass) :
    𝒟 T² = 𝒟 ((4•π^2) • (a³/ (G *(M + m))))  := by
    simp_dim
    module

theorem not_kepler_third_law_dim_check
    (T : WithDim Dimension.Time) (a : WithDim Dimension.Length) (M m : WithDim Dimension.Mass) :
    ¬ 𝒟 T = 𝒟 ((4•π^2) • (a³/ (G *(M + m))))  := by
    simp_dim
    decide +kernel

def NewtonsSecondWithDim' (m : WithDim Dimension.Mass) (F : WithDim Dimension.Force)
    (a : WithDim Dimension.Acceleration) : Prop :=
    F = (m * a)

lemma newtonsSecondWithDim'_isDimensionallyCorrect :
    Quantity.IsDimensionallyCorrect NewtonsSecondWithDim' := by
        funext m F a
        unfold NewtonsSecondWithDim'
        simp_dim
        rw [Quantity.smul_mul_smul,inv_eq_one_div,inv_eq_one_div,inv_eq_one_div,
            ←mul_div_mul_comm,one_mul, ←Dimension.PrimeScale.scaler_add]
        constructor
        · intro h
          apply congrArg
            ((Dimension.Mass + (Dimension.Length - 2 • Dimension.Time)).PrimeScale • · ) at h
          rw [← inv_eq_one_div,smul_smul,smul_smul,mul_inv_cancel₀] at h
          · repeat rw [one_smul] at h
            assumption
          · exact Dimension.PrimeScale.scaler_ne_zero
        · intro h
          rw [h]

theorem e_equal_mc2 (E : WithDim Dimension.Energy) (m : WithDim Dimension.Mass) :
    E =  ↑(m * c²) := by
    sorry

theorem not_e_equal_mc_dim_check (E : WithDim Dimension.Energy) (m : WithDim Dimension.Mass) :
   ¬ 𝒟 E =  𝒟 (m * c) := by
    simp_dim
    decide +kernel

end WithDim

section SI

variable (G : SI (Unit.meter ^ 3 / (Unit.kilogram * Unit.second ^ 2)))
variable (c : SI (Unit.meter / Unit.second))

theorem kepler_third_law_unit_check
    (T : SI Unit.second) (a : SI Unit.meter) (M m : SI Unit.kilogram) :
    𝒟 T² = 𝒟 ((4•π^2) • (a³/ (G *(M + m))))  := by
    simp_dim
    module

end SI

end formal
