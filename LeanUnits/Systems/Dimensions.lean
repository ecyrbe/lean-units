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


/-!
we can derive some new dimensions from the base ones
simp is mandatory to allow dsimp to unfold these definitions
-/
@[simp] def Area := Length^2
@[simp] def Volume := Length^3
@[simp] def Speed := Length / Time
@[simp] def Acceleration := Length / Time^2
@[simp] def Jerk := Length / Time^3
@[simp] def Snap := Length / Time^4
@[simp] def Momentum := Mass * Speed
@[simp] def AngularMomentum := Momentum * Length
@[simp] def Force := Mass * Acceleration
@[simp] def Pressure := Force / Area
@[simp] def Energy := Force * Length
@[simp] def Action := Energy * Time
@[simp] def Power := Energy / Time
@[simp] def Charge := Current * Time
@[simp] def Frequency := Time^(-1)
@[simp] def Voltage := Power / Current
@[simp] def Capacitance := Charge / Voltage
@[simp] def Resistance := Voltage / Current
@[simp] def Conductance := Current / Voltage
@[simp] def Inductance := Resistance * Time
@[simp] def MagneticFlux := Voltage * Time
@[simp] def MagneticInduction := MagneticFlux / Area

end Units.Dimension
