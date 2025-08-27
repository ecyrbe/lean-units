import LeanUnits.Framework.Units.Basic
import LeanUnits.Systems.Dimensions
import LeanUnits.Systems.SI.Units

-- non SI units, but used a lot
namespace Units.Unit

def liter := defineDerivedUnit "L" (meter^3) (Conversion.scale (1/1000) (by simp))
def tonne := defineDerivedUnit "t" kilogram (Conversion.scale (10^3) (by simp))
def dalton := defineDerivedUnit "Da" kilogram (Conversion.scale (166053906892 / 10^38) (by simp))
def bar := defineDerivedUnit "bar" pascal (Conversion.scale (10^5) (by simp))
def atmosphere := defineDerivedUnit "atm" pascal (Conversion.scale (101325) (by simp))
def hectare := defineDerivedUnit "ha" (meter^2) (Conversion.scale (10^4) (by simp))
def electronvolt := defineDerivedUnit "eV" joule (Conversion.scale (1602176634/10^28) (by simp))

end Units.Unit
