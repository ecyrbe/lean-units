import LeanUnits.Systems.SI.SI
import LeanUnits.Systems.SI.Units

-- these 7 SI Constants are defined as quantities with their own unit.
-- So that they are not reduced away by default.
namespace Units

namespace Internal
open Unit

@[simp] def speed_of_light := Unit.defineDerivedUnit "c" (meter / second)
  (Conversion.scale (299792458))
@[simp] def planck_constant := Unit.defineDerivedUnit "h"
  (joule * second) (Conversion.scale (662607015/10^42) (by simp))
@[simp] def hyperfine_transition_frequency_cesium := Unit.defineDerivedUnit "Δν_Cs"
  (second^(-1)) (Conversion.scale (9192631770))
@[simp] def elementary_charge := Unit.defineDerivedUnit "e"
  (coulomb) (Conversion.scale (1602176634/10^28) (by simp))
@[simp] def boltzmann_constant := Unit.defineDerivedUnit "k"
  (joule / kelvin) (Conversion.scale (1380649/10^29) (by simp))
@[simp] def avogadro_constant := Unit.defineDerivedUnit "N_A"
  (mole^(-1)) (Conversion.scale (602214076/10^31) (by simp))
@[simp] def luminous_efficacy := Unit.defineDerivedUnit "K_cd"
  (lumen/watt) (Conversion.scale (683))

end Internal

@[inline] def c : SI Internal.speed_of_light := ⟨1.0⟩
@[inline] def h : SI Internal.planck_constant := ⟨1.0⟩
@[inline] def Δν_Cs : SI Internal.hyperfine_transition_frequency_cesium := ⟨1.0⟩
@[inline] def e : SI Internal.elementary_charge := ⟨1.0⟩
@[inline] def k : SI Internal.boltzmann_constant := ⟨1.0⟩
@[inline] def N_A : SI Internal.avogadro_constant := ⟨1.0⟩
@[inline] def K_cd : SI Internal.luminous_efficacy := ⟨1.0⟩

end Units
