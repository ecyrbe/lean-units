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
abbrev Area := 2 • Length
abbrev Volume := 3 • Length
abbrev Speed := Length - Time
abbrev Acceleration := Length - 2•Time
abbrev Jerk := Length - 3•Time
abbrev Snap := Length - 4•Time
abbrev Momentum := Mass + Speed
abbrev AngularMomentum := Momentum + Length
abbrev Force := Mass + Acceleration
abbrev Pressure := Force - Area
abbrev Energy := Force + Length
abbrev Action := Energy + Time
abbrev Power := Energy - Time
abbrev Charge := Current + Time
abbrev Frequency := -Time
abbrev Voltage := Power - Current
abbrev Capacitance := Charge - Voltage
abbrev Resistance := Voltage - Current
abbrev Conductance := Current - Voltage
abbrev Inductance := Resistance + Time
abbrev MagneticFlux := Voltage + Time
abbrev MagneticInduction := MagneticFlux - Area

end Units.Dimension
