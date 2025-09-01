import LeanUnits.Framework.Units.Basic
import LeanUnits.Systems.Dimensions

namespace Units.Unit
-- base SI units
def meter := defineUnit "m" Dimension.Length
def second := defineUnit "s" Dimension.Time
def kilogram := defineUnit "kg" Dimension.Mass
def ampere := defineUnit "A" Dimension.Current
def kelvin := defineUnit "K" Dimension.Temperature
def mole := defineUnit "mol" Dimension.AmountOfSubstance
def candela := defineUnit "cd" Dimension.LuminousIntensity
def radian := defineUnit "rad" Dimension.dimensionless
def steradian := defineUnit "sr" Dimension.dimensionless

-- derived SI units
@[simp] def hertz := defineDerivedUnit "Hz" (second⁻¹)
@[simp] def newton := defineDerivedUnit "N" (kilogram * meter / second^2)
@[simp] def pascal := defineDerivedUnit "Pa" (newton / meter^2)
@[simp] def joule := defineDerivedUnit "J" (newton * meter)
@[simp] def watt := defineDerivedUnit "W" (joule / second)
@[simp] def coulomb := defineDerivedUnit "C" (ampere * second)
@[simp] def volt := defineDerivedUnit "V" (watt / ampere)
@[simp] def ohm := defineDerivedUnit "Ω" (volt / ampere)
@[simp] def farad := defineDerivedUnit "F" (coulomb / volt)
@[simp] def weber := defineDerivedUnit "Wb" (volt * second)
@[simp] def tesla := defineDerivedUnit "T" (weber / meter^2)
@[simp] def henry := defineDerivedUnit "H" (ohm * second)
@[simp] def lumen := defineDerivedUnit "lm" (candela * steradian)
@[simp] def lux := defineDerivedUnit "lx" (lumen / meter^2)
@[simp] def becquerel := defineDerivedUnit "Bq" (second⁻¹)
@[simp] def gray := defineDerivedUnit "Gy" (joule / kilogram)
@[simp] def sievert := defineDerivedUnit "Sv" (joule / kilogram)
@[simp] def katal := defineDerivedUnit "kat" (mole * second)
@[simp] def celsius := defineDerivedUnit "°C" kelvin (Conversion.translate (273.15))

end Units.Unit
