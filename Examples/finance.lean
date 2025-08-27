import LeanUnits.Systems.SI

open Units

-- dimensions
def Currency := Dimension.ofString "C"

-- units
def USD := Unit.defineUnit "$" Currency
def EUR := Unit.defineDerivedUnit "€" USD (Conversion.scale (116/100) (by simp)) -- 1 € = 1.16 $
def GBP := Unit.defineDerivedUnit "£" USD (Conversion.scale (134/100) (by simp)) -- 1 £ = 1.34 $

-- quantities
abbrev Money {μ} (units : μ) := Quantity units Float

def dollar : Money USD := ⟨1.0⟩
def euro : Money EUR := ⟨1.0⟩
def pound : Money GBP := ⟨1.0⟩

#eval (5.0•dollar).into EUR -- 4.310345 (€)
#eval (5.0•euro).into USD -- 5.8 ($)
#eval (5.0•pound).into USD -- 6.7 ($)
#eval (5.0•dollar).into GBP -- 3.731343 (£)
#eval (5.0•euro).into GBP -- 4.328358 (£)
#eval (5.0•pound).into EUR -- 5.747126 (€)
