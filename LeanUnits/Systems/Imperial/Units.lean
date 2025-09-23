import LeanUnits.Framework.Units.Basic
import LeanUnits.Systems.Dimensions
import LeanUnits.Systems.SI.Units

namespace Units.Unit
open Conversion

-- Length
def_derived_unit inch := "in" from meter with scale (254/10000)
def_derived_unit foot := "ft" from inch with scale 12
def_derived_unit yard := "yd" from foot with scale 3
def_derived_unit mile := "mi" from yard with scale 1760
-- Mass
def_derived_unit ounce := "oz" from kilogram with scale (28349523125 / 10^11)
def_derived_unit pound := "lb" from ounce with scale 16
def_derived_unit ton := "ton" from pound with scale 2000
def_derived_unit stone := "st" from pound with scale 14
-- Volume
def_derived_unit gallon := "gal" from meter^3 with scale (231 * 254^3 / 10^12)
def_derived_unit quart := "qt" from gallon with scale (1/4)
def_derived_unit pint := "pt" from quart with scale (1/2)
def_derived_unit cup := "cup" from pint with scale (1/2)
def_derived_unit fluid_ounce := "fl oz" from gallon with scale (1/128)
-- temperature
def_derived_unit fahrenheit := "℉" from kelvin with scale (5/9) + translate (45967 / 100 * 5/9)

end Units.Unit
