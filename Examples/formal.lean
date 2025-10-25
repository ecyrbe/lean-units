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

def kepler_third_law
    (T : WithDim Dimension.Time)
    (a : WithDim Dimension.Length)
    (M m : WithDim Dimension.Mass) : Prop :=
    T² =  (4•π^2) • ↑(a³/ (G *(M + m)))

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

def newtons_second_law
    (F : WithDim Dimension.Force)
    (m : WithDim Dimension.Mass)
    (a : WithDim Dimension.Acceleration) : Prop :=
    F = m * a

lemma newtons_second_law_dim_check
    (F : WithDim Dimension.Force)
    (m : WithDim Dimension.Mass)
    (a : WithDim Dimension.Acceleration) :
    𝒟 F =  𝒟 (m * a) := by
    simp_dim

lemma newtons_second_law_isDimensionallyCorrect :
    Quantity.IsDimensionallyCorrect newtons_second_law := by
    funext m F a
    unfold newtons_second_law
    simp_dim
    repeat rw [←Dimension.PrimeScale.scaler_neg]
    rw [Quantity.smul_mul_smul, ←Dimension.PrimeScale.scaler_add, ←neg_add]
    apply smul_right_inj
    exact Dimension.PrimeScale.scaler_ne_zero

def einstein_mass_energy_equivalence_val
    (m : WithDim Dimension.Mass)
    (E : WithDim Dimension.Energy)
    (c : WithDim Dimension.Speed) : Prop :=
  E.val = m.val * c.val ^ 2

lemma einstein_mass_energy_equivalence_isDimensionallyCorrect :
    Quantity.IsDimensionallyCorrect einstein_mass_energy_equivalence_val := by
        funext m E c
        unfold einstein_mass_energy_equivalence_val
        simp_dim
        have h_m : (Real.instInv.inv Dimension.Mass.PrimeScale) * m.val =
            (Real.instInv.inv Dimension.Mass.PrimeScale) • m.val := by
          rw [Quantity.val_smul_eq_mul]
        have h_c : ((Real.instInv.inv (Dimension.Length - Dimension.Time).PrimeScale) * c.val) ^ 2 =
            (Real.instInv.inv (Dimension.Length - Dimension.Time).PrimeScale)^2 • c.val ^ 2 := by
            rw [←smul_pow, Quantity.val_smul_eq_mul]
        rw [←Quantity.val_smul_eq_mul , h_m, h_c,_root_.smul_mul_smul]
        repeat rw [←Dimension.PrimeScale.scaler_neg]
        rw [←Dimension.PrimeScale.scaler_nsmul, ←Dimension.PrimeScale.scaler_add ]
        have h_p1 : -(Dimension.Mass + (Dimension.Length - 2 • Dimension.Time) + Dimension.Length) =
            -(Dimension.Mass + 2 • (Dimension.Length - Dimension.Time)) := by
            module
        have h_p2 : -Dimension.Mass + 2 • -(Dimension.Length - Dimension.Time) =
            -(Dimension.Mass + 2 • (Dimension.Length - Dimension.Time)) := by
            module
        rw [h_p1, h_p2]
        apply smul_right_inj
        exact Dimension.PrimeScale.scaler_ne_zero

def einstein_mass_energy_equivalence
    (E : WithDim Dimension.Energy)
    (m : WithDim Dimension.Mass) : Prop :=
    E =  ↑(m * c²)

lemma einstein_mass_energy_equivalence_dim_check
    (E : WithDim Dimension.Energy)
    (m : WithDim Dimension.Mass) :
    𝒟 E = 𝒟 (m * c²) := by
    simp_dim
    module

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
