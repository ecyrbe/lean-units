import LeanUnits.Framework.Units.Basic
import LeanUnits.Systems.Dimensions
import LeanUnits.Systems.SI.Units

namespace Units.Unit

abbrev fahrenheit := defineDerivedUnit "°F" Unit.kelvin
  ((Conversion.scale (5/9) (by simp)) + Conversion.translate (45967 / 100 * 5/9 ))

end Units.Unit
