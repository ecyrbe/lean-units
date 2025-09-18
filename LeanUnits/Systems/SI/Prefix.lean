import Lean.Elab.Command
import LeanUnits.Framework.Quantities.Basic
import LeanUnits.Framework.Units.Basic
import LeanUnits.Framework.Conversions.Basic
import LeanUnits.Framework.Dimensions.Basic

namespace Units

def quetta : Float := 1e30 -- 10^30
def ronna : Float  := 1e27 -- 10^27
def yotta : Float  := 1e24 -- 10^24
def zetta : Float  := 1e21 -- 10^21
def exa : Float    := 1e18 -- 10^18
def peta : Float   := 1e15 -- 10^15
def tera : Float   := 1e12 -- 10^12
def giga : Float   := 1e9  -- 10^9
def mega : Float   := 1e6  -- 10^6
def kilo : Float   := 1e3  -- 10^3
def hecto : Float  := 1e2  -- 10^2
def deca : Float   := 1e1  -- 10^1
def deci : Float   := 1e-1 -- 10^-1
def centi : Float  := 1e-2 -- 10^-2
def milli : Float  := 1e-3 -- 10^-3
def micro : Float  := 1e-6 -- 10^-6
def nano : Float   := 1e-9 -- 10^-9
def pico : Float   := 1e-12 -- 10^-12
def femto : Float  := 1e-15 -- 10^-15
def atto : Float   := 1e-18 -- 10^-18
def zepto : Float  := 1e-21 -- 10^-21
def yocto : Float  := 1e-24 -- 10^-24
def ronto : Float  := 1e-27 -- 10^-27
def quecto : Float := 1e-30 -- 10^-30
def _one : Float   := 1.0 -- 10^0

namespace Prefix

open Lean Elab Tactic Meta Command


/--
  Define SI prefixes for a given unit symbol and dimension.
  Generates definitions for all SI prefixes with the specified dimension.

  Example:
  `define_si_prefixes m` will create definitions for
  `mm`, `cm`, `km`, etc. for the meter unit symbol `m`.
-/
elab "define_si_prefixes" unit_symbol:ident : command => do
  let prefixes := #[
    ("Q", "quetta"), ("R", "ronna"), ("Y", "yotta"), ("Z", "zetta"),
    ("E", "exa"), ("P", "peta"), ("T", "tera"), ("G", "giga"),
    ("M", "mega"), ("k", "kilo"), ("h", "hecto"), ("da", "deca"),
    ("d", "deci"), ("c", "centi"), ("m", "milli"), ("μ", "micro"),
    ("n", "nano"), ("p", "pico"), ("f", "femto"), ("a", "atto"),
    ("z", "zepto"), ("y", "yocto"), ("r", "ronto"), ("q", "quecto")
  ]
  for (sym, val) in prefixes do
    let newName := mkIdent (Name.mkSimple s!"{sym}{unit_symbol.getId}")
    let valIdent := mkIdent (Name.mkSimple val)
    elabCommand <| ← `(command| def $newName := ($valIdent : Float) • $unit_symbol)


/--
  Define SI prefixes with an offset for a given unit symbol and dimension.
  Generates definitions for all SI prefixes with the specified dimension and an offset.
  The offset is applied to the value of the prefix.

  Example:
  `define_si_prefixes_with_offset k g milli` will create definitions for
  `mg`, `cg`, `kg`, etc. for the gram unit symbol `g` and dimension `M𝓭`, with an offset of `milli`.
  This means that `g` will be defined as `0.001 * 1.0` relative to the base unit `kg`.
-/
elab "define_si_prefixes_with_offset"
  prefix_symbol:str unit_symbol:ident offset:ident : command => do
  let prefixes := #[
    ("Q", "quetta"), ("R", "ronna"), ("Y", "yotta"), ("Z", "zetta"),
    ("E", "exa"), ("P", "peta"), ("T", "tera"), ("G", "giga"),
    ("M", "mega"), ("k", "kilo"), ("h", "hecto"), ("da", "deca"), ("", "_one"),
    ("d", "deci"), ("c", "centi"), ("m", "milli"), ("μ", "micro"),
    ("n", "nano"), ("p", "pico"), ("f", "femto"), ("a", "atto"),
    ("z", "zepto"), ("y", "yocto"), ("r", "ronto"), ("q", "quecto")
  ]
  for (sym, val) in prefixes do
    if sym != prefix_symbol.getString then
      let newName := mkIdent (Name.mkSimple s!"{sym}{unit_symbol.getId}")
      let targetName := mkIdent (Name.mkSimple s!"{prefix_symbol.getString}{unit_symbol.getId}")
      let valIdent := mkIdent (Name.mkSimple val)
      elabCommand <| ← `(command| def $newName := (($offset * $valIdent) : Float) • $targetName)

end Prefix

end Units
