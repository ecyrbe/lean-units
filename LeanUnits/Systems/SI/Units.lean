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
def hertz := defineDerivedUnit "Hz" (second⁻¹)
def newton := defineDerivedUnit "N" (kilogram * meter / second^2)
def pascal := defineDerivedUnit "Pa" (newton / meter^2)
def joule := defineDerivedUnit "J" (newton * meter)
def watt := defineDerivedUnit "W" (joule / second)
def coulomb := defineDerivedUnit "C" (ampere * second)
def volt := defineDerivedUnit "V" (watt / ampere)
def ohm := defineDerivedUnit "Ω" (volt / ampere)
def farad := defineDerivedUnit "F" (coulomb / volt)
def weber := defineDerivedUnit "Wb" (volt * second)
def tesla := defineDerivedUnit "T" (weber / meter^2)
def henry := defineDerivedUnit "H" (ohm * second)
def lumen := defineDerivedUnit "lm" (candela * steradian)
def lux := defineDerivedUnit "lx" (lumen / meter^2)
def becquerel := defineDerivedUnit "Bq" (second⁻¹)
def gray := defineDerivedUnit "Gy" (joule / kilogram)
def sievert := defineDerivedUnit "Sv" (joule / kilogram)
def katal := defineDerivedUnit "kat" (mole * second)
def celsius := defineDerivedUnit "°C" kelvin (Conversion.translate (273.15))

end Units.Unit
