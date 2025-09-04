import LeanUnits.Framework.Units.Basic
import LeanUnits.Systems.Dimensions
import LeanUnits.Systems.SI.Units

-- non SI units, but used a lot
namespace Units.Unit
open Conversion
-- length
def_derived_unit astronomical_unit := "au" ≈ meter with scale 149597870700
-- area
def_derived_unit hectare := "ha" ≈ meter^2 with scale (10^4)
-- volume
def_derived_unit liter := "L" ≈ meter^3 with scale (1/1000)
-- time
def_derived_unit minute := "min" ≈ second with scale 60
def_derived_unit hour := "h" ≈ minute with scale 60
def_derived_unit day := "d" ≈ hour with scale 24
def_derived_unit week := "wk" ≈ day with scale 7
def_derived_unit year := "yr" ≈ day with scale (36525/100)
-- mass
def_derived_unit tonne := "t" ≈ kilogram with scale (10^3)
def_derived_unit dalton := "Da" ≈ kilogram with scale (166053906892 / 10^38)
-- pressure
def_derived_unit bar := "bar" ≈ pascal with scale (10^5)
def_derived_unit atmosphere := "atm" ≈ pascal with scale 101325
-- energy
def_derived_unit electronvolt := "eV" ≈ joule with scale (1602176634/10^28)
-- angle
def_derived_unit degree := "°" ≈ radian with scale (314159265358979323846/(180*10^20))
def_derived_unit arcminute := "′" ≈ degree with scale (1/60)
def_derived_unit arcsecond := "″" ≈ arcminute with scale (1/60)

end Units.Unit
