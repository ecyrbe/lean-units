import LeanUnits.Framework.Units.Basic
import LeanUnits.Systems.Dimensions
import LeanUnits.Systems.Macros

namespace Units.Unit
open Conversion

-- base SI units
def_base_unit meter := "m" from Dimension.Length
def_base_unit second := "s" from Dimension.Time
def_base_unit kilogram := "kg" from Dimension.Mass
def_base_unit ampere := "A" from Dimension.Current
def_base_unit kelvin := "K" from Dimension.Temperature
def_base_unit mole := "mol" from Dimension.AmountOfSubstance
def_base_unit candela := "cd" from Dimension.LuminousIntensity
def_base_unit radian := "rad" from Dimension.dimensionless
def_base_unit steradian := "sr" from Dimension.dimensionless

-- derived SI units
def_derived_unit hertz := "Hz" from second⁻¹
def_derived_unit newton := "N" from kilogram * meter / second^2
def_derived_unit pascal := "Pa" from newton / meter^2
def_derived_unit joule := "J" from newton * meter
def_derived_unit watt := "W" from joule / second
def_derived_unit coulomb := "C" from ampere * second
def_derived_unit volt := "V" from watt / ampere
def_derived_unit ohm := "Ω" from volt / ampere
def_derived_unit farad := "F" from coulomb / volt
def_derived_unit weber := "Wb" from volt * second
def_derived_unit tesla := "T" from weber / meter^2
def_derived_unit henry := "H" from ohm * second
def_derived_unit lumen := "lm" from candela * steradian
def_derived_unit lux := "lx" from lumen / meter^2
def_derived_unit becquerel := "Bq" from second⁻¹
def_derived_unit gray := "Gy" from joule / kilogram
def_derived_unit sievert := "Sv" from joule / kilogram
def_derived_unit katal := "kat" from mole * second
def_derived_unit celsius := "°C" from kelvin with translate (27315/100)

end Units.Unit
