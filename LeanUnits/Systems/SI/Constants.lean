import LeanUnits.Systems.SI.Quantities
import LeanUnits.Framework.Units.Basic

-- these 7 SI Constants are defined as quantities with their own unit.
-- So that they are not reduced away by default.
namespace Units

namespace Internal

abbrev speed_of_light := Unit.defineDerivedUnit "c"
    (Dimension.Speed) (Conversion.scale (299792458))

end Internal

@[inline] abbrev c : SI Internal.speed_of_light := ⟨1.0⟩ -- 1 speed of light

end Units
