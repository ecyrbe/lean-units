
import Lean.Meta.Tactic.Simp.Attr

namespace Units

open Lean Meta


initialize SimpDimensionSet : SimpExtension ←
  registerSimpAttr `dimension_set
    "definitions and lemmas for dimension simplification"

initialize SimpBaseUnitSet : SimpExtension ←
  registerSimpAttr `base_unit_set
    "definitions and lemmas for base simplification"

initialize SimpDerivedUnitSet : SimpExtension ←
  registerSimpAttr `derived_unit_set
    "definitions and lemmas for base simplification"

end Units
