import LeanUnits.Framework.Units.Basic
import LeanUnits.Framework.Quantities.Lemmas
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

theorem e_equal_mc2 (E : WithDim Dimension.Energy) (m : WithDim Dimension.Mass) :
    E =  ↑(m * c²) := by
    sorry

-- theorem e_equal_mc (E : SI Dimension.Energy) (m : SI Dimension.Mass) :
--     E =  ↑(m * c) := by -- statement is wrong and is directly catched by the type checker
--     sorry
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
