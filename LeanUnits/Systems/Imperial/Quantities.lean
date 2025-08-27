import LeanUnits.Framework.Quantities.Basic
import LeanUnits.Systems.Utils
import LeanUnits.Systems.Imperial.Units

namespace Units

abbrev Imperial {μ} (units : μ) := Quantity units Float

@[inline] def F₀ : Imperial Unit.fahrenheit := ⟨1.0⟩ -- 1 degree Fahrenheit

end Units
