import LeanUnits.Framework.Dimensions.Basic

namespace Units.Dimension

-- base dimensions
def Length : Dimension := ofString "L"
def Time : Dimension := ofString "T"
def Mass : Dimension := ofString "M"
def Current : Dimension := ofString "I"
def Temperature : Dimension := ofString "Θ"
def AmountOfSubstance : Dimension := ofString "N"
def LuminousIntensity : Dimension := ofString "J"


-- we can derive some new dimensions from the base ones
abbrev Area := Length^2
abbrev Volume := Length^3
abbrev Speed := Length / Time
abbrev Acceleration := Length / Time^2
abbrev Jerk := Length / Time^3
abbrev Snap := Length / Time^4
abbrev Momentum := Mass * Speed
abbrev AngularMomentum := Momentum * Length
abbrev Force := Mass * Acceleration
abbrev Pressure := Force / Area
abbrev Energy := Force * Length
abbrev Action := Energy * Time
abbrev Power := Energy / Time
abbrev Charge := Current * Time
abbrev Frequency := Time^(-1)
abbrev Voltage := Power / Current
abbrev Capacitance := Charge / Voltage
abbrev Resistance := Voltage / Current
abbrev Conductance := Current / Voltage
abbrev Inductance := Resistance * Time
abbrev MagneticFlux := Voltage * Time
abbrev MagneticInduction := MagneticFlux / Area

end Units.Dimension
