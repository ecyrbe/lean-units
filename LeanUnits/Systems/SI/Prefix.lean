namespace Units

def quetta := 1e30 -- 10^30
def ronna  := 1e27 -- 10^27
def yotta  := 1e24 -- 10^24
def zetta  := 1e21 -- 10^21
def exa    := 1e18 -- 10^18
def peta   := 1e15 -- 10^15
def tera   := 1e12 -- 10^12
def giga   := 1e9  -- 10^9
def mega   := 1e6  -- 10^6
def kilo   := 1e3  -- 10^3
def hecto  := 1e2  -- 10^2
def deca   := 1e1  -- 10^1
def deci   := 1e-1 -- 10^-1
def centi  := 1e-2 -- 10^-2
def milli  := 1e-3 -- 10^-3
def micro  := 1e-6 -- 10^-6
def nano   := 1e-9 -- 10^-9
def pico   := 1e-12 -- 10^-12
def femto  := 1e-15 -- 10^-15
def atto   := 1e-18 -- 10^-18
def zepto  := 1e-21 -- 10^-21
def yocto  := 1e-24 -- 10^-24
def ronto  := 1e-27 -- 10^-27
def quecto := 1e-30 -- 10^-30
def _one   := 1.0 -- 10^0

namespace Prefix

open Lean Elab Tactic Meta


/--
  Define SI prefixes for a given unit symbol and dimension.
  Generates definitions for all SI prefixes with the specified dimension.

  Example:
  `define_si_prefixes m` will create definitions for
  `mm`, `cm`, `km`, etc. for the meter unit symbol `m`.
-/
macro "define_si_prefixes" unit_symbol:ident : command => do
  let prefixes := #[
    ("Q", "quetta"), ("R", "ronna"), ("Y", "yotta"), ("Z", "zetta"),
    ("E", "exa"), ("P", "peta"), ("T", "tera"), ("G", "giga"),
    ("M", "mega"), ("k", "kilo"), ("h", "hecto"), ("da", "deca"),
    ("d", "deci"), ("c", "centi"), ("m", "milli"), ("μ", "micro"),
    ("n", "nano"), ("p", "pico"), ("f", "femto"), ("a", "atto"),
    ("z", "zepto"), ("y", "yocto"), ("r", "ronto"), ("q", "quecto")
  ]
  let defs ← prefixes.mapM fun (sym, val) =>
    let name := Name.mkSimple s!"{sym}{unit_symbol.getId}"
    let valIdent := mkIdent (Name.mkSimple val)
    `(@[inline] def $(mkIdent name) := $valIdent • $unit_symbol)
  return TSyntax.mk <| mkNullNode defs

/--
  Define SI prefixes with an offset for a given unit symbol and dimension.
  Generates definitions for all SI prefixes with the specified dimension and an offset.
  The offset is applied to the value of the prefix.

  Example:
  `define_si_prefixes_with_offset k g milli` will create definitions for
  `mg`, `cg`, `kg`, etc. for the gram unit symbol `g` and dimension `M𝓭`, with an offset of `milli`.
  This means that `g` will be defined as `0.001 * 1.0` relative to the base unit `kg`.
-/
macro "define_si_prefixes_with_offset" prefix_symbol:str unit_symbol:ident offset:ident : command => do
  let prefixes := #[
    ("Q", "quetta"), ("R", "ronna"), ("Y", "yotta"), ("Z", "zetta"),
    ("E", "exa"), ("P", "peta"), ("T", "tera"), ("G", "giga"),
    ("M", "mega"), ("k", "kilo"), ("h", "hecto"), ("da", "deca"), ("", "_one"),
    ("d", "deci"), ("c", "centi"), ("m", "milli"), ("μ", "micro"),
    ("n", "nano"), ("p", "pico"), ("f", "femto"), ("a", "atto"),
    ("z", "zepto"), ("y", "yocto"), ("r", "ronto"), ("q", "quecto")
  ]
  let defs ← prefixes.filter (fun (sym,_) => sym != prefix_symbol.getString)
    |>.mapM fun (sym, val) =>
      let name := mkIdent (Name.mkSimple s!"{sym}{unit_symbol.getId}")
      let target_symbol := mkIdent (Name.mkSimple s!"{prefix_symbol.getString}{unit_symbol.getId}")
      let valIdent := mkIdent (Name.mkSimple val)
      `(@[inline] def $name := $offset * $valIdent • $target_symbol)
  return TSyntax.mk <| mkNullNode defs

end Prefix

end Units
