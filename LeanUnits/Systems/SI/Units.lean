import LeanUnits.Framework.Units.Basic
import LeanUnits.Systems.Dimensions
import LeanUnits.Systems.Macros

namespace Units.Unit
open Conversion

-- base SI units
def_base_unit meter := "m" Dimension.Length
def_base_unit second := "s" Dimension.Time
def_base_unit kilogram := "kg" Dimension.Mass
def_base_unit ampere := "A" Dimension.Current
def_base_unit kelvin := "K" Dimension.Temperature
def_base_unit mole := "mol" Dimension.AmountOfSubstance
def_base_unit candela := "cd" Dimension.LuminousIntensity
def_base_unit radian := "rad" Dimension.dimensionless
def_base_unit steradian := "sr" Dimension.dimensionless

-- derived SI units
def_derived_unit hertz := "Hz" second⁻¹
def_derived_unit newton := "N" kilogram * meter / second^2
def_derived_unit pascal := "Pa" newton / meter^2
def_derived_unit joule := "J" newton * meter
def_derived_unit watt := "W" joule / second
def_derived_unit coulomb := "C" ampere * second
def_derived_unit volt := "V" watt / ampere
def_derived_unit ohm := "Ω" volt / ampere
def_derived_unit farad := "F" coulomb / volt
def_derived_unit weber := "Wb" volt * second
def_derived_unit tesla := "T" weber / meter^2
def_derived_unit henry := "H" ohm * second
def_derived_unit lumen := "lm" candela * steradian
def_derived_unit lux := "lx" lumen / meter^2
def_derived_unit becquerel := "Bq" second⁻¹
def_derived_unit gray := "Gy" joule / kilogram
def_derived_unit sievert := "Sv" joule / kilogram
def_derived_unit katal := "kat" mole * second
def_derived_unit celsius := "°C" kelvin with translate (27315/100)

end Units.Unit
