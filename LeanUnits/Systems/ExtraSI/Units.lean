import LeanUnits.Framework.Units.Basic
import LeanUnits.Systems.Dimensions
import LeanUnits.Systems.SI.Units

-- non SI units, but used a lot
namespace Units.Unit

abbrev liter := defineDerivedUnit "L" (meter^3) (Conversion.scale (1/1000) (by simp))
abbrev tonne := defineDerivedUnit "t" kilogram (Conversion.scale (10^3) (by simp))
abbrev dalton := defineDerivedUnit "Da" kilogram (Conversion.scale (166053906892 / 10^38) (by simp))
abbrev bar := defineDerivedUnit "bar" pascal (Conversion.scale (10^5) (by simp))
abbrev atmosphere := defineDerivedUnit "atm" pascal (Conversion.scale (101325) (by simp))
abbrev hectare := defineDerivedUnit "ha" (meter^2) (Conversion.scale (10^4) (by simp))
abbrev electronvolt := defineDerivedUnit "eV" joule (Conversion.scale (1602176634/10^28) (by simp))

end Units.Unit
