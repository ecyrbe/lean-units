import LeanUnits.Framework.Units.Basic
import LeanUnits.Systems.Dimensions

namespace Units.Unit
-- base SI units
abbrev meter := defineUnit "m" Dimension.Length
abbrev second := defineUnit "s" Dimension.Time
abbrev kilogram := defineUnit "kg" Dimension.Mass
abbrev ampere := defineUnit "A" Dimension.Current
abbrev kelvin := defineUnit "K" Dimension.Temperature
abbrev mole := defineUnit "mol" Dimension.AmountOfSubstance
abbrev candela := defineUnit "cd" Dimension.LuminousIntensity
abbrev steradian := defineUnit "sr" Dimension.dimensionless

-- derived SI units
abbrev hertz := defineDerivedUnit "Hz" (second⁻¹)
abbrev newton := defineDerivedUnit "N" (kilogram * meter / second^2)
abbrev pascal := defineDerivedUnit "Pa" (newton / meter^2)
abbrev joule := defineDerivedUnit "J" (newton * meter)
abbrev watt := defineDerivedUnit "W" (joule / second)
abbrev coulomb := defineDerivedUnit "C" (ampere * second)
abbrev volt := defineDerivedUnit "V" (watt / ampere)
abbrev ohm := defineDerivedUnit "Ω" (volt / ampere)
abbrev farad := defineDerivedUnit "F" (coulomb / volt)
abbrev weber := defineDerivedUnit "Wb" (volt * second)
abbrev tesla := defineDerivedUnit "T" (weber / meter^2)
abbrev henry := defineDerivedUnit "H" (ohm * second)
abbrev lumen := defineDerivedUnit "lm" (candela * steradian)
abbrev lux := defineDerivedUnit "lx" (lumen / meter^2)
abbrev becquerel := defineDerivedUnit "Bq" (second⁻¹)
abbrev gray := defineDerivedUnit "Gy" (joule / kilogram)
abbrev sievert := defineDerivedUnit "Sv" (joule / kilogram)
abbrev katal := defineDerivedUnit "kat" (mole * second)
abbrev celsius := defineDerivedUnit "°C" kelvin (Conversion.translate (273.15))

end Units.Unit
