import LeanUnits.Framework.Units.Basic
import LeanUnits.Systems.Dimensions
import LeanUnits.Systems.SI.Units

-- non SI units, but used a lot
namespace Units.Unit
open Conversion
-- length
def_derived_unit astronomical_unit := "au" from meter with scale 149597870700
-- area
def_derived_unit hectare := "ha" from meter^2 with scale (10^4)
-- volume
def_derived_unit liter := "L" from meter^3 with scale (1/1000)
-- time
def_derived_unit minute := "min" from second with scale 60
def_derived_unit hour := "h" from minute with scale 60
def_derived_unit day := "d" from hour with scale 24
def_derived_unit week := "wk" from day with scale 7
def_derived_unit year := "yr" from day with scale (36525/100)
-- mass
def_derived_unit tonne := "t" from kilogram with scale (10^3)
def_derived_unit dalton := "Da" from kilogram with scale (166053906892 / 10^38)
-- pressure
def_derived_unit bar := "bar" from pascal with scale (10^5)
def_derived_unit atmosphere := "atm" from pascal with scale 101325
-- energy
def_derived_unit electronvolt := "eV" from joule with scale (1602176634/10^28)
-- angle
def_derived_unit degree := "°" from radian with scale (314159265358979323846/(180*10^20))
def_derived_unit arcminute := "′" from degree with scale (1/60)
def_derived_unit arcsecond := "″" from arcminute with scale (1/60)

end Units.Unit
