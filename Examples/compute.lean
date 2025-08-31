import LeanUnits.Systems.SI

open Units

def G := 6.67430e-11 • (m³ / (kg * s²))
#eval G
#eval G.val -- we can get back the value
#eval G.units -- we can get back the units
#eval G.dimension -- we can get back the dimension

def pi := 3.14159265358979323846

def solar_mass_kepler_formula
(period : SI Unit.second) (semi_major_axis : SI Unit.meter) : SI Unit.kilogram :=
  ↑(4.0 * pi^2  * semi_major_axis³ / (G * period²))

-- we cast to transform `kg·(m/s)²` to `J`
-- no need to use `into` or `convert` that would involve more computations for the conversion
def cinetic_energy (mass : SI Unit.kilogram) (velocity : SI (Unit.meter - Unit.second))
 : SI Unit.joule :=
  ↑(0.5 * mass * velocity²)

def earth_semi_major_axis := 1.496e11 • m
def minute := 60.0 • s
def hour := 60.0 • minute
def day := 24.0 • hour
def year := 365.25 • day

#eval solar_mass_kepler_formula year earth_semi_major_axis
