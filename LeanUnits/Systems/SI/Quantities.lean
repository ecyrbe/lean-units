import LeanUnits.Framework.Units.Basic
import LeanUnits.Framework.Dimensions.Basic
import LeanUnits.Systems.Dimensions
import LeanUnits.Systems.SI.SI
import LeanUnits.Systems.SI.Units
import LeanUnits.Systems.SI.Prefix
import LeanUnits.Systems.Utils

namespace Units
set_option allowUnsafeReducibility true
set_option linter.style.commandStart false

-- base SI units quantities
@[inline] def m   : SI Unit.meter := ⟨1.0⟩ -- 1 meter
@[inline] def kg  : SI Unit.kilogram := ⟨1.0⟩ -- 1 kilogram
@[inline] def s   : SI Unit.second := ⟨1.0⟩ -- 1 second
@[inline] def A   : SI Unit.ampere := ⟨1.0⟩ -- 1 ampere
@[inline] def K   : SI Unit.kelvin := ⟨1.0⟩ -- 1 kelvin
@[inline] def mol : SI Unit.mole := ⟨1.0⟩ -- 1 mole
@[inline] def cd  : SI Unit.candela := ⟨1.0⟩ -- 1 candela

-- derived SI units quantities
@[inline] def Hz : SI Unit.hertz := ⟨1.0⟩ -- 1 hertz
@[inline] def N : SI Unit.newton := ⟨1.0⟩ -- 1 newton
@[inline] def Pa : SI Unit.pascal := ⟨1.0⟩ -- 1 pascal
@[inline] def J : SI Unit.joule := ⟨1.0⟩ -- 1 joule
@[inline] def W : SI Unit.watt := ⟨1.0⟩ -- 1 watt
@[inline] def C : SI Unit.coulomb := ⟨1.0⟩ -- 1 coulomb
@[inline] def V : SI Unit.volt := ⟨1.0⟩ -- 1 volt
@[inline] def Ω : SI Unit.ohm := ⟨1.0⟩ -- 1 ohm
@[inline] def F : SI Unit.farad := ⟨1.0⟩ -- 1 farad
@[inline] def Wb : SI Unit.weber := ⟨1.0⟩ -- 1 weber
@[inline] def T : SI Unit.tesla := ⟨1.0⟩ -- 1 tesla
@[inline] def H : SI Unit.henry := ⟨1.0⟩ -- 1 henry
@[inline] def C₀ : SI Unit.celsius := ⟨1.0⟩ -- 1 degree Celsius
@[inline] def lm : SI Unit.lumen := ⟨1.0⟩ -- 1 lumen
@[inline] def lx : SI Unit.lux := ⟨1.0⟩ -- 1 lux
@[inline] def Bq : SI Unit.becquerel := ⟨1.0⟩ -- 1 becquerel
@[inline] def Gy : SI Unit.gray := ⟨1.0⟩ -- 1 gray
@[inline] def Sv : SI Unit.sievert := ⟨1.0⟩ -- 1 sievert
@[inline] def kat : SI Unit.katal := ⟨1.0⟩ -- 1 katal

-- SI prefixes for base units
define_si_prefixes m -- cmm, km, etc.
define_si_prefixes_with_offset "k" g milli -- mg, cg, etc.
define_si_prefixes s -- ms, μs, ns, etc.
define_si_prefixes A
define_si_prefixes K
define_si_prefixes mol
define_si_prefixes cd

-- SI prefixes for derived units
define_si_prefixes Hz
define_si_prefixes N
define_si_prefixes Pa
define_si_prefixes J
define_si_prefixes W
define_si_prefixes C
define_si_prefixes V
define_si_prefixes Ω
define_si_prefixes F
define_si_prefixes Wb
define_si_prefixes T
define_si_prefixes H
define_si_prefixes C₀
define_si_prefixes lm
define_si_prefixes lx
define_si_prefixes Bq
define_si_prefixes Gy
define_si_prefixes Sv
define_si_prefixes kat

unseal Rat.add Rat.mul Rat.sub Rat.neg Rat.inv Rat.div

end Units
