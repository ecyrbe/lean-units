import LeanUnits.Systems.ExtraSI.Units
import LeanUnits.Systems.SI.Quantities

namespace Units

@[inline] def L : SI Unit.liter := ⟨1.0⟩ -- 1 liter
@[inline] def t : SI Unit.tonne := ⟨1.0⟩ -- 1 tonne
@[inline] def Da : SI Unit.dalton := ⟨1.0⟩ -- 1 dalton
@[inline] def bar : SI Unit.bar := ⟨1.0⟩ -- 1 bar
@[inline] def atm : SI Unit.atmosphere := ⟨1.0⟩ -- 1 atmosphere
@[inline] def ha : SI Unit.hectare := ⟨1.0⟩ -- 1 hectare
@[inline] def eV : SI Unit.electronvolt := ⟨1.0⟩ -- 1 electronvolt

define_si_prefixes L
define_si_prefixes bar
define_si_prefixes eV
-- Other SI prefixes don't make sense for these units

end Units
