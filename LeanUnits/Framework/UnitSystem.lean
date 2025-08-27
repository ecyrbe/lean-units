import LeanUnits.Framework.Dimensions.Basic
import LeanUnits.Framework.Conversion

namespace Units

class UnitSystem (μ : Type) [AddCommGroup μ] where
  dimension (u : μ) : Dimension
  conversion (u : μ) : Conversion

alias 𝒞 := UnitSystem.conversion
alias 𝒟 := UnitSystem.dimension

end Units
