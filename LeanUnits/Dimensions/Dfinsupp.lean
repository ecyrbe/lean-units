import Mathlib.Data.DFinsupp.Defs
import Mathlib.Data.DFinsupp.Module
import Mathlib.Data.DFinsupp.Notation
import Batteries.Data.Rat
import Mathlib.Data.Rat.Init
import Mathlib.Data.Rat.Lemmas

abbrev Dimension := DFinsupp (fun _ : String => ℚ)

namespace Dimension

def ofString (s : String) : Dimension := DFinsupp.single s 1

def dimensionless : Dimension := 0

def Length : Dimension := ofString "L"
def Time : Dimension := ofString "T"
def Mass : Dimension := ofString "M"
def Current : Dimension := ofString "I"
def Temperature : Dimension := ofString "Θ"
def AmountOfSubstance : Dimension := ofString "N"
def LuminousIntensity : Dimension := ofString "J"

section Repr
open Lean Parser Term

private def formatExp (e : String) (n : ℚ) : String :=
  match n with
  | 1   => e
  | 2   => s!"{e}²"
  | 3   => s!"{e}³"
  | 4   => s!"{e}⁴"
  | 5   => s!"{e}⁵"
  | 6   => s!"{e}⁶"
  | 7   => s!"{e}⁷"
  | 8   => s!"{e}⁸"
  | 9   => s!"{e}⁹"
  | -1  => s!"{e}⁻¹"
  | -2  => s!"{e}⁻²"
  | -3  => s!"{e}⁻³"
  | -4  => s!"{e}⁻⁴"
  | -5  => s!"{e}⁻⁵"
  | -6  => s!"{e}⁻⁶"
  | -7  => s!"{e}⁻⁷"
  | -8  => s!"{e}⁻⁸"
  | -9  => s!"{e}⁻⁹"
  | n   => s!"{e}^{n}"

unsafe instance : Repr Dimension where
  reprPrec f _ :=
    let vals := f.support'.unquot.val.map (fun i => (i,(f i)))
      |>.unquot
      |>.filter (·.2 != 0)
      |>.dedup
      |>.mergeSort (fun a b => a.1 < b.1)
    if vals.length = 0 then
      "∅"
    else
      let parts : List String := vals.map (fun a => formatExp a.1 a.2)
      f!"{String.intercalate "•" parts}"

end Repr

-- we can derive some new dimensions from the base ones
abbrev Area := 2 • Length
#eval Area
abbrev Volume := 3 • Length
#eval Volume
abbrev Speed := Length - Time
#eval Speed
abbrev Acceleration := Length - 2•Time
#eval Acceleration
abbrev Jerk := Length - 3•Time
#eval Jerk
abbrev Snap := Length - 4•Time
#eval Snap
abbrev Momentum := Mass + Speed
#eval Momentum
abbrev AngularMomentum := Momentum + Length
#eval AngularMomentum
abbrev Force := Mass + Acceleration
#eval Force
abbrev Pressure := Force - Area
#eval Pressure
abbrev Energy := Force + Length
#eval Energy
abbrev Action := Energy + Time
#eval Action
abbrev Power := Energy - Time
#eval Power
abbrev Charge := Current + Time
#eval Charge
abbrev Frequency := -Time
#eval Frequency
abbrev Voltage := Power - Current
#eval Voltage
abbrev Capacitance := Charge - Voltage
#eval Capacitance
abbrev Resistance := Voltage - Current
#eval Resistance
abbrev Conductance := Current - Voltage
#eval Conductance
abbrev Inductance := Resistance + Time
#eval Inductance
abbrev MagneticFlux := Voltage + Time
#eval MagneticFlux
abbrev MagneticInduction := MagneticFlux - Area
#eval MagneticInduction


end Dimension
