import LeanUnits.Framework.Units.Basic
import LeanUnits.Systems.Dimensions

-- non SI units, but used a lot
namespace Units.Unit

abbrev liter := defineDerivedUnit "L" (3•Dimension.Length) (Conversion.scale (1/1000) (by simp))
abbrev tonne := defineDerivedUnit "t" Dimension.Mass (Conversion.scale (10^3) (by simp))
abbrev dalton := defineDerivedUnit "Da"
  Dimension.Mass (Conversion.scale (166053906892 / 10^38) (by simp))
abbrev bar := defineDerivedUnit "bar" Dimension.Pressure (Conversion.scale (10^5) (by simp))
abbrev atmosphere := defineDerivedUnit "atm"
  Dimension.Pressure (Conversion.scale (101325) (by simp))
abbrev hectare := defineDerivedUnit "ha" (2•Dimension.Length) (Conversion.scale (10^4) (by simp))
abbrev electronvolt := defineDerivedUnit "eV"
  Dimension.Energy (Conversion.scale (1602176634/10^28) (by simp))

end Units.Unit
