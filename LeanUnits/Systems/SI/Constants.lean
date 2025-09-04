import LeanUnits.Systems.SI.SI
import LeanUnits.Systems.SI.Units
import LeanUnits.Systems.Macros

-- these 7 SI Constants are defined as quantities with their own unit.
-- So that they are not reduced away by default.
namespace Units

namespace Internal
open Unit Conversion

def_derived_unit speed_of_light := "c" ≈ meter/second with scale 299792458
def_derived_unit planck_constant := "h" ≈ joule*second with scale (662607015/10^42)
def_derived_unit hyperfine_transition_cesium := "Δν_Cs" ≈ second^(-1) with scale 9192631770
def_derived_unit elementary_charge := "e" ≈ coulomb with scale (1602176634/10^28)
def_derived_unit boltzmann_constant := "k" ≈ joule/kelvin with scale (1380649/10^29)
def_derived_unit avogadro_constant := "N_A" ≈ mole^(-1) with scale (602214076/10^31)
def_derived_unit luminous_efficacy := "K_cd" ≈ lumen/watt with scale 683

end Internal

@[inline] def c : SI Internal.speed_of_light := ⟨1.0⟩
@[inline] def h : SI Internal.planck_constant := ⟨1.0⟩
@[inline] def Δν_Cs : SI Internal.hyperfine_transition_cesium := ⟨1.0⟩
@[inline] def e : SI Internal.elementary_charge := ⟨1.0⟩
@[inline] def k : SI Internal.boltzmann_constant := ⟨1.0⟩
@[inline] def N_A : SI Internal.avogadro_constant := ⟨1.0⟩
@[inline] def K_cd : SI Internal.luminous_efficacy := ⟨1.0⟩

end Units
