import LeanUnits.Systems.Formal
import Mathlib.Data.Real.Basic

namespace formal
open Units Real

abbrev SI {μ} (units : μ) := Quantity units ℝ


variable (G : SI (Dimension.Length ^ 3 / (Dimension.Mass * Dimension.Time ^ 2)))
variable (c : SI Dimension.Speed)

theorem kepler_third_law
    (T : SI Dimension.Time) (a : SI Dimension.Length) (M m : SI Dimension.Mass) :
    T² =  (4•π^2) • ↑(a³/ (G *(M + m)))  := by
  sorry

theorem e_equal_mc2 (E : SI Dimension.Energy) (m : SI Dimension.Mass) :
    E =  ↑(m * c²) := by
    sorry

-- theorem e_equal_mc (E : SI Dimension.Energy) (m : SI Dimension.Mass) :
--     E =  ↑(m * c) := by -- statement is wrong and is directly catched by the type checker
--     sorry

end formal
