import LeanUnits.Framework.Dimensions.Basic
import LeanUnits.Systems.Macros

namespace Units.Dimension

-- base dimensions
def_base_dimension Length := "L"
def_base_dimension Time := "T"
def_base_dimension Mass := "M"
def_base_dimension Current := "I"
def_base_dimension Temperature := "Θ"
def_base_dimension AmountOfSubstance := "N"
def_base_dimension LuminousIntensity := "J"

/-!
we can derive some new dimensions from the base ones
simp is mandatory to allow dsimp to unfold these definitions
-/
def_derived_dimension Area := Length^2
def_derived_dimension Volume := Length^3
def_derived_dimension Speed := Length / Time
def_derived_dimension Acceleration := Length / Time^2
def_derived_dimension Jerk := Length / Time^3
def_derived_dimension Snap := Length / Time^4
def_derived_dimension Momentum := Mass * Speed
def_derived_dimension AngularMomentum := Momentum * Length
def_derived_dimension Force := Mass * Acceleration
def_derived_dimension Pressure := Force / Area
def_derived_dimension Energy := Force * Length
def_derived_dimension Action := Energy * Time
def_derived_dimension Power := Energy / Time
def_derived_dimension Charge := Current * Time
def_derived_dimension Frequency := Time^(-1)
def_derived_dimension Voltage := Power / Current
def_derived_dimension Capacitance := Charge / Voltage
def_derived_dimension Resistance := Voltage / Current
def_derived_dimension Conductance := Current / Voltage
def_derived_dimension Inductance := Resistance * Time
def_derived_dimension MagneticFlux := Voltage * Time
def_derived_dimension MagneticInduction := MagneticFlux / Area

end Units.Dimension
