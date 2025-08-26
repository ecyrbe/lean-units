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

-- derived SI units
abbrev hertz := defineUnit "Hz" (-Dimension.Time)
abbrev newton := defineUnit "N" (Dimension.Force)
abbrev pascal := defineUnit "Pa" (Dimension.Pressure)
abbrev watt := defineUnit "W" (Dimension.Power)
abbrev coulomb := defineUnit "C" (Dimension.Charge)
abbrev volt := defineUnit "V" (Dimension.Voltage)
abbrev ohm := defineUnit "Ω" (Dimension.Resistance)
abbrev farad := defineUnit "F" (-Dimension.Capacitance)
abbrev weber := defineUnit "Wb" (Dimension.MagneticFlux)
abbrev joule := defineUnit "J" (Dimension.Energy)
abbrev tesla := defineUnit "T" (Dimension.MagneticInduction)
abbrev henry := defineUnit "H" (Dimension.Inductance)
abbrev lumen := defineUnit "lm" Dimension.LuminousIntensity
abbrev lux := defineUnit "lx" (Dimension.LuminousIntensity - 2•Dimension.Length)
abbrev becquerel := defineUnit "Bq" (-Dimension.Time)
abbrev gray := defineUnit "Gy" (Dimension.Energy - Dimension.Mass)
abbrev sievert := defineUnit "Sv" (Dimension.Energy - Dimension.Mass)
abbrev katal := defineUnit "kat" (Dimension.AmountOfSubstance-Dimension.Time)
abbrev celsius := defineDerivedUnit "°C" Dimension.Temperature (Conversion.translate (273.15))

end Units.Unit
