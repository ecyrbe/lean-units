import LeanUnits.Framework.Quantities.Basic
import LeanUnits.Systems.Utils
import LeanUnits.Systems.Imperial.Units

namespace Units

abbrev Imperial (units : Unit) := Quantity units Float

@[inline] def ℉ : Imperial Unit.fahrenheit := ⟨1.0⟩ -- 1 degree Fahrenheit

-- length
@[inline] def inch : Imperial Unit.inch := ⟨1.0⟩ -- 1 inch
@[inline] def ft : Imperial Unit.foot := ⟨1.0⟩ -- 1 foot
@[inline] def yd : Imperial Unit.yard := ⟨1.0⟩ -- 1 yard
@[inline] def mi : Imperial Unit.mile := ⟨1.0⟩ -- 1 mile
-- mass
@[inline] def oz : Imperial Unit.ounce := ⟨1.0⟩ -- 1 ounce
@[inline] def lb : Imperial Unit.pound := ⟨1.0⟩ -- 1 pound
@[inline] def st : Imperial Unit.stone := ⟨1.0⟩ -- 1 stone
@[inline] def ton : Imperial Unit.ton := ⟨1.0⟩ -- 1 ton
-- volume
@[inline] def gal : Imperial Unit.gallon := ⟨1.0⟩ -- 1 gallon
@[inline] def qt : Imperial Unit.quart := ⟨1.0⟩ -- 1 quart
@[inline] def pt : Imperial Unit.pint := ⟨1.0⟩ -- 1 pint
@[inline] def cup : Imperial Unit.cup := ⟨1.0⟩ -- 1 cup
@[inline] def fl_oz : Imperial Unit.fluid_ounce := ⟨1.0⟩ -- 1 fluid ounce

end Units
