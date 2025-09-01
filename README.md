# lean-units

lean-units is a small Lean library that provides:
- dimension definitions (length, time, mass, temperature, ...),
- unit definitions for SI, ExtraSI and Imperial systems,
- quantities built on top of units so you can represent typed physical values.

## Build / install
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

## Basic usage

- Compute with physical quantities:

```lean
import LeanUnits.Systems.SI

open Units

def solar_mass_kepler_formula
(period : SI Unit.second) (semi_major_axis : SI Unit.meter): SI Unit.kilogram :=
  ↑(4.0 * pi^2  * semi_major_axis³ / (G * period²))

#eval solar_mass_kepler_formula year earth_semi_major_axis
-- 1.9884098707065004e30 (kg)
```
- Converting between units:

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

-- derived dimensions should be marked with @[simp] to allow casting
@[simp] def Acceleration := Length / Time^2
@[simp] def Force := Mass * Acceleration
```

- defining new units:

```lean
-- derived units should be marked with @[simp] to allow casting and conversions
@[simp] def light_year := defineDerivedUnit "ly" meter (Conversion.scale (9460728 * 10^9) (by simp))
```
- defining new quantities:

```lean
abbrev SI (units : Unit) := Quantity units Float

def ly : SI light_year := ⟨1.0⟩

def distance_to_alpha_centauri : SI light_year := 4.367 • ly
#eval distance_to_alpha_centauri -- 4.367 (ly)
#eval distance_to_alpha_centauri.units -- ly
#eval distance_to_alpha_centauri.into Unit.meter -- 4.132e16 (m)
#eval distance_to_alpha_centauri.dimension -- L
```

## Casting between units or dimensions

### Dimensions

The library provides a way to cast between two dimensions that guaranty that their dimensions are propositionaly the same by using the tactic `auto_equiv`.

### Units

The library provides a way to cast between two units that guaranty that :
- their dimensions are the same (propositionaly)
- their conversions are the same (propositionaly)
These two rules form an equivalence relation on units.

It uses by default the tactic `auto_equiv` to automatically prove that the units are the equivalent.
You can provide your own proof if needed.

## Conversion between units

The library provides a way to convert between two units that guaranty that :
- their dimensions are the same (propositionaly)

Their conversions don't have to be the same, since the conversion is what we want to compute.

It uses by default the tactic `auto_dim` to automatically prove that the dimensions are the same.
You can provide your own proof if needed.

## Internal representation

Internal representation of units and dimensions use Mathlib's `DFinsupp` (dependent finitely supported functions).
This allows to represent dimension or units as products of base dimensions or units raised to rational powers.

### Dimensions

A dimension is a product of base dimensions raised to rational powers.
For example, the dimension of force is `Mass•Length•Time⁻²` and is represented as:
- `force = {"M" ↦ 1, "L" ↦ 1, "T" ↦ -2}`

DFinsupp then gives us a natural way to combine dimensions by addition of the exponents since we get a `AddCommGroup` structure on dimensions.

And we can define as many base dimensions as we want, since they are just string identifiers mapped to rational exponents.

### Units

Units represent a choice of metric in a given dimension.

Choosing a metric involves choosing
- a power factor (it's one for base and derived units)
- an affine conversion (to convert between units of the same dimension)
- a dimension (to ensure dimensional correctness)

A unit is a product of base units raised to rational powers.
For example, the unit of force in the SI system is `kg•m/s²`
can be represented as :
- `force₁ = {"kg" ↦ (1,0,Mass), "m" ↦ (1,0,Length), "s" ↦ (-2,0,Time⁻²)}`

or when using derived units:
- `force₂={"N" ↦ (1,0,Mass•Length•Time⁻²)}`

Converting between these two representations is possible because
their dimensions are the same under product:
- `Π 𝒟(force₁) = Mass•Length•Time⁻² = Π 𝒟(force₂)`

### Quantities

A quantity is a value associated with a Unit or a Dimension.
Lean units allows you to work with quantities associated with either a unit or a dimension. Both ways are represented by the same structure `Quantity` allowing to transition your proofs on dimensional analysis to computations with physical quantities with a real unit system (like SI standard).

#### For engineering computations

When computing a quantity, you usually want to work with a value associated with a unit.
For example, `9.81 (m/s²)` is a quantity representing the acceleration due to gravity at the surface of the Earth.

Usually, in engineering you mostly only work with quantities associated with units.
And units are just a way to ensure dimensional correctness and perform conversions.

#### For formal proofs

When doing formal proofs, you usually want to work with quantities associated with a dimension. And don't care about the units.
Formal proof side of the library is still a work in progress, but you can already define dimensions and prove statements about them.

## Examples
- See the example files for working code and common tasks:
  - Basic computations: [Examples/compute.lean](Examples/compute.lean)
  - Unit conversions and derived units: [Examples/conversion.lean](Examples/conversion.lean)
  - Using the library in formal proofs / tactics: [Examples/formal.lean](Examples/formal.lean)

## Notes and pointers
- The library separates systems (SI, ExtraSI, Imperial, Natural). SI units and prefixes are implemented under `LeanUnits.Systems.SI.*`.
- If you need to define a new unit or derived unit, inspect the framework in [LeanUnits/Framework/Units/Basic.lean](LeanUnits/Framework/Units/Basic.lean).

## LICENSE
- The project is licensed under the MIT License. See [LICENSE](LICENSE).
- Copyright 2025 ecyrbe

## Acknowledgements
- Thanks to the authors of Mathlib for providing a solid foundation for formalizing mathematics in Lean.
- Thanks to the Lean community for their support and contributions to the ecosystem.
- Special thanks to [Terrence Tao](https://github.com/teorth) for the formal [source code here](https://github.com/teorth/analysis/blob/18d4fd7253ff17a05133d9b6b120b5f08f5ce6ad/analysis/Analysis/Misc/UnitsSystem.lean). He gave the permission to use his lemmas and definitions as a starting point for the formal side of the library.
  The adaptation can be seen in [LeanUnits/Framework/Quantities/Lemmas.lean](LeanUnits/Framework/Quantities/Lemmas.lean).