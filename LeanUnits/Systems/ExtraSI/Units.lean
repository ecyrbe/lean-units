import LeanUnits.Framework.Units.Basic
import LeanUnits.Systems.Dimensions
import LeanUnits.Systems.SI.Units

-- non SI units, but used a lot
namespace Units.Unit

-- length
def astronomical_unit := defineDerivedUnit "au" meter (Conversion.scale (149597870700) (by simp))
-- area
def hectare := defineDerivedUnit "ha" (meter^2) (Conversion.scale (10^4) (by simp))
-- volume
def liter := defineDerivedUnit "L" (meter^3) (Conversion.scale (1/1000) (by simp))
-- time
def minute := defineDerivedUnit "min" second (Conversion.scale 60 (by simp))
def hour := defineDerivedUnit "h" minute (Conversion.scale 60 (by simp))
def day := defineDerivedUnit "d" hour (Conversion.scale 24 (by simp))
def week := defineDerivedUnit "wk" day (Conversion.scale 7 (by simp))
def year := defineDerivedUnit "yr" day (Conversion.scale (36525/100) (by simp))
-- mass
def tonne := defineDerivedUnit "t" kilogram (Conversion.scale (10^3) (by simp))
def dalton := defineDerivedUnit "Da" kilogram (Conversion.scale (166053906892 / 10^38) (by simp))
-- pressure
def bar := defineDerivedUnit "bar" pascal (Conversion.scale (10^5) (by simp))
def atmosphere := defineDerivedUnit "atm" pascal (Conversion.scale (101325) (by simp))
-- energy
def electronvolt := defineDerivedUnit "eV" joule (Conversion.scale (1602176634/10^28) (by simp))
-- angle
def degree := defineDerivedUnit "°" radian
  (Conversion.scale (314159265358979323846/(180*10^20) ) (by simp))
def arcminute := defineDerivedUnit "′" degree (Conversion.scale (1/60) (by simp))
def arcsecond := defineDerivedUnit "″" arcminute (Conversion.scale (1/60) (by simp))

end Units.Unit
