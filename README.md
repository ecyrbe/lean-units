# lean-units

lean-units is a small Lean library that provides:
- dimension definitions (length, time, mass, temperature, ...),
- unit definitions for SI, ExtraSI and Imperial systems,
- quantities built on top of units so you can represent typed physical values.

Build / install
- Build the project with Lake:
```sh
lake build
```
See [lakefile.toml](lakefile.toml).

Quick overview
- A compile-time checked dimensional analysis framework.
- Compute with physical quantities in a type-safe manner.
- Support for safe compile-time checked conversions
- Allow Formal verification of physics statements relying on Dimensional Analysis (more work on this part to be done)

Basic usage (Lean)

```lean
import LeanUnits.Systems.SI

open Units

def solar_mass_kepler_formula
(period : SI Unit.second) (semi_major_axis : SI Unit.meter): SI Unit.kilogram :=
  ↑(4.0 * pi^2  * semi_major_axis³ / (G * period²))

#eval solar_mass_kepler_formula year earth_semi_major_axis
-- 1.9884098707065004e30 (kg)
```
- Allow for easy conversion between units:

```lean

abbrev MeV : SI Unit.electronvolt := ⟨10^6⟩ -- 1 MeV

def electron_mass_ev := (0.51099895069 • MeV / c²)
#eval electron_mass_ev -- 510998.950690 (c⁻²•eV)
#eval electron_mass_ev.units -- c⁻²•eV
#eval electron_mass_ev.dimension -- M

--explicit conversion to kg
def electron_mass_kg := electron_mass_ev.into Unit.kilogram
#eval electron_mass_kg -- 9.109383701528e-31 (kg)
#eval electron_mass_kg.units -- kg
#eval electron_mass_kg.dimension -- M
```

- defining new dimensions :

```lean
-- base dimensions
def Length : Dimension := ofString "L"
def Time : Dimension := ofString "T"
def Mass : Dimension := ofString "M"

-- derived dimensions
@[simp] def Acceleration := Length / Time^2
@[simp] def Force := Mass * Acceleration
```

- defining new units:

```lean
def light_year := defineDerivedUnit "ly" meter (Conversion.scale (9460728 * 10^9) (by simp))
```
- defining new quantities:

```lean
abbrev SI {μ} (units : μ) := Quantity units Float

def ly : SI light_year := ⟨1.0⟩

def distance_to_alpha_centauri : SI light_year := 4.367 • ly
#eval distance_to_alpha_centauri -- 4.367 (ly)
#eval distance_to_alpha_centauri.units -- ly
#eval distance_to_alpha_centauri.dimension -- L
```

Examples
- See the example files for working code and common tasks:
  - Basic computations: [Examples/compute.lean](Examples/compute.lean)
  - Unit conversions and derived units: [Examples/conversion.lean](Examples/conversion.lean)
  - Using the library in formal proofs / tactics: [Examples/formal.lean](Examples/formal.lean)

Notes and pointers
- The library separates systems (SI, ExtraSI, Imperial, Natural). SI units and prefixes are implemented under `LeanUnits.Systems.SI.*`.
- If you need to define a new unit or derived unit, inspect the framework in [LeanUnits/Framework/Units/Basic.lean](LeanUnits/Framework/Units/Basic.lean).

