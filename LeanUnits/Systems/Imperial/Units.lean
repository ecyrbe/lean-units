import LeanUnits.Framework.Units.Basic
import LeanUnits.Systems.Dimensions
import LeanUnits.Systems.SI.Units

namespace Units.Unit

@[simp] def fahrenheit := defineDerivedUnit "°F" kelvin
  ((Conversion.scale (5/9) (by simp)) + Conversion.translate (45967 / 100 * 5/9 ))

-- Length
@[simp] def inch := defineDerivedUnit "in" meter (Conversion.scale (254/10000) (by simp))
@[simp] def foot := defineDerivedUnit "ft" inch (Conversion.scale (12) (by simp))
@[simp] def yard := defineDerivedUnit "yd" foot (Conversion.scale (3) (by simp))
@[simp] def mile := defineDerivedUnit "mi" yard (Conversion.scale (1760) (by simp))
-- Mass
@[simp] def ounce := defineDerivedUnit "oz" Unit.kilogram (Conversion.scale (28349523125 / 10^11) (by simp))
@[simp] def pound := defineDerivedUnit "lb" ounce (Conversion.scale (16) (by simp))
@[simp] def ton := defineDerivedUnit "ton" pound (Conversion.scale (2000) (by simp))
@[simp] def stone := defineDerivedUnit "st" pound (Conversion.scale (14) (by simp))
-- Volume
@[simp] def gallon := defineDerivedUnit "gal" (meter^3) (Conversion.scale (231 * 254^3 / 10^12) (by simp))
@[simp] def quart := defineDerivedUnit "qt" gallon (Conversion.scale (1/4) (by simp))
@[simp] def pint := defineDerivedUnit "pt" quart (Conversion.scale (1/2) (by simp))
@[simp] def cup := defineDerivedUnit "cup" pint (Conversion.scale (1/2) (by simp))
@[simp] def fluid_ounce := defineDerivedUnit "fl oz" gallon (Conversion.scale (1/128) (by simp))

end Units.Unit
