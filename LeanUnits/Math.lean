namespace Units

namespace Math

/-- Heterogeneous power helpers for Units -/
class HIntPow.{u} (α : Type u) (n: Int) (β : outParam (Type u)) where
  /-- Raise an element of α to the power of n, denoted by `a^n`. -/
  hIntPow : α → β

postfix:max "⁻²" => HIntPow.hIntPow (n:=-2)

postfix:max "⁻¹" => HIntPow.hIntPow (n:=-1)

postfix:max "²" => HIntPow.hIntPow (n:=2)

postfix:max "³" => HIntPow.hIntPow (n:=3)

postfix:max "⁴" => HIntPow.hIntPow (n:=4)

postfix:max "⁵" => HIntPow.hIntPow (n:=5)

/-- Heterogeneous square root helper for Units -/
class HSqrt.{u} (α : Type u) (β : outParam (Type u)) where
  /-- Square root of an element of α, denoted by `sqrt a`. -/
  hSqrt : α → β

prefix:max "√" => HSqrt.hSqrt

end Math
namespace Units
