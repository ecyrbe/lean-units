import LeanUnits.Framework.SimpSets
import LeanUnits.Framework.Dimensions.Basic
import LeanUnits.Framework.Units.Basic

namespace Units

section macros

section dimension
open Dimension

/--
Define a base dimension.

Example:
- `def_base_dimension Length := "L"`
-/
macro "def_base_dimension" name:ident ":=" sym:str : command => do
    `(command| def $name := ofString $sym)

/--
Define a derived dimension.

Example:
- `def_derived_dimension Area := Length^2`
-/
macro "def_derived_dimension" name:ident ":=" dim:term : command => do
    `(command| @[dimension_set] def $name := $dim)
end dimension

section unit
open Unit

/--
Define a base unit.

Example:
- `def_base_unit meter := "m" = Dimension.Length`
-/
macro "def_base_unit" name:ident ":=" sym:str "from" dim:term : command => do
    `(command| @[base_unit_set] def $name := defineUnit $sym $dim)

/--
Define a derived unit.

Example:
- `def_derived_unit newton := "N" ≈ kilogram * meter / second^2`
-/
macro "def_derived_unit" name:ident ":=" sym:str "from" base:term : command => do
  `(command| @[derived_unit_set] def $name := defineDerivedUnit $sym $base)

/--
Define a derived unit with conversion.

Example:
- `def_derived_unit celsius := "°C" ≈ kelvin with Conversion.translate (27315/100)`
-/
macro "def_derived_unit" name:ident ":=" sym:str "from" base:term "with" conv:term : command => do
  `(command| @[derived_unit_set] def $name := defineDerivedUnit $sym $base $conv)

end unit

end macros

end Units
