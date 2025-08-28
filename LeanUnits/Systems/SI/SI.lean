import LeanUnits.Framework.Quantities.Basic
import LeanUnits.Framework.Units.Basic

namespace Units

/--
Define an SI quantity as a quantity with Float values with a defined set of units.
-/
abbrev SI (units : Unit) := Quantity units Float

end Units
