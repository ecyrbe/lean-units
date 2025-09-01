import LeanUnits.Systems.ExtraSI
import LeanUnits.Systems.Imperial
import LeanUnits.Systems.SI.Constants

open Units
-- pretrry print Float using scientific notation
def formatScientific (x : Float) (precision : Nat := 6) : String :=
    if x.isNaN then "NaN"
    else if x.isInf then if x < 0 then "-Inf" else "Inf"
    else if x == 0 then "0.0e0"
    else
        let sign := if x < 0 then "-" else ""
        let xAbs := x.abs
        let exp := (Float.log10 xAbs).floor
        let mantissa := xAbs / (10.0 ^ exp)
        let scale : Float := (10.0:Float).pow precision.toFloat
        let mantissaRounded := (mantissa * scale).round / scale
        let (adjustedMantissa, adjustedExp) :=
            if mantissaRounded >= 10.0 then
                (mantissaRounded / 10.0, exp + 1.0)
            else
                (mantissaRounded, exp)
        let s := adjustedMantissa.toStringFull
        let parts := s.split (· == '.')
        match parts with
        | [intPart, fracPart] =>
                let fracPart := fracPart.take precision
                let fracTrimmed := fracPart.dropRightWhile (· == '0')
                let fracFinal := if fracTrimmed.isEmpty then "0" else fracTrimmed
                sign ++ intPart ++ "." ++ fracFinal ++ "e" ++ toString adjustedExp.toInt64
        | _ => sign ++ s ++ "e" ++ toString adjustedExp.toInt64

instance : Repr Float where
  reprPrec f _ := if f.abs < 1e-3 || f.abs >= 1e10 then
    formatScientific f 10
  else
    f.toString

def ev := e * V
#eval ev -- 1 (e·V)
#eval ev.units -- e·V
#eval ev.dimension -- M·L²·T⁻²
#eval (ev.as J) == eV.as J -- true
#eval ev.units ≈ eV.units -- true, they are equivalent units

def electron_mass_ev := (0.51099895069 • MeV / c²)
#eval electron_mass_ev
#eval electron_mass_ev.units
#eval electron_mass_ev.dimension

--explicit conversion to kg
def electron_mass_kg := electron_mass_ev.into Unit.kilogram
#eval electron_mass_kg
#eval electron_mass_kg.units
#eval electron_mass_kg.dimension

-- implicit conversion to kg using convert
def electron_mass_kg2 : SI Unit.kilogram := electron_mass_ev.convert
#eval electron_mass_kg2
#eval electron_mass_kg2.units
#eval electron_mass_kg2.dimension

#eval (MeV/c²).units ≈ kg.units -- false, they are not equivalent units, need conversion
#eval (MeV/c²).dimension = kg.dimension -- true, they have the same dimension

#eval c.as (m/s) -- we can also convert to another quantity

-- can't convert to joules
#check_failure electron_mass_ev.into Unit.joule-- doesn't compile

#eval eV.dimension
#eval J.dimension


#check_failure kg/s + ↑(s/kg)
def computable := kg/s + ↑(s/kg)⁻¹

@[simp] def light_year := Unit.defineDerivedUnit "ly" Unit.meter (Conversion.scale (9460728 * 10^9) (by simp))

def ly : SI light_year := ⟨1.0⟩

def distance_to_alpha_centauri : SI light_year := 4.367 • ly
#eval distance_to_alpha_centauri -- 4.367 (ly)
#eval distance_to_alpha_centauri.units -- ly
#eval distance_to_alpha_centauri.into Unit.meter -- 4.132e16 (m)
#eval distance_to_alpha_centauri.dimension -- L


-- temperature conversion

def human_body_temp := 37.8 • C₀

#eval human_body_temp
#eval human_body_temp.units
#eval human_body_temp.dimension

def human_body_temp_kelvin := human_body_temp.into Unit.kelvin
#eval human_body_temp_kelvin
#eval human_body_temp_kelvin.units
#eval human_body_temp_kelvin.dimension

def human_body_in_fahrenheit := human_body_temp.into Unit.fahrenheit
#eval human_body_in_fahrenheit
#eval human_body_in_fahrenheit.units
#eval human_body_in_fahrenheit.dimension
