import LeanUnits.Systems.Formal

namespace formal
open Units

abbrev SI {μ} (units : μ) := Quantity units ℝ

variable (G : SI (3 • Dimension.Length - Dimension.Mass - 2 • Dimension.Time))
variable (π : ℝ)
variable (c : SI Dimension.Speed)

theorem kepler_third_law
    (T : SI Dimension.Time) (a : SI Dimension.Length) (M m : SI Dimension.Mass) :
    T² =  (4:ℝ) • π^2 • ↑(a³/ (G *(M + m)))  := by
  sorry

theorem e_equal_mc2 (E: SI Dimension.Energy) (m : SI Dimension.Mass) :
    E =  ↑(m * c²) := by
    sorry

theorem e_equal_mc (E: SI Dimension.Energy) (m : SI Dimension.Mass) :
    E =  ↑(m * c) := by -- statement is wrong and is directly catched by the type checker
    sorry

end formal
