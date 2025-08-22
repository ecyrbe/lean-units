import Batteries.Data.Rat
import Mathlib.Data.Rat.Init
import Batteries.Data.HashMap
import Std.Data.HashMap
import Std.Data.DHashMap

namespace Std.HashMap

@[inline]
def unionWith {α β} [OfNat β 0] [BEq α] [Hashable α] (f : β → β → β) (m₁ m₂ : HashMap α β) :
  HashMap α β := m₂.fold (init := m₁) fun acc k v₂ =>
    let v₁ := acc.getD k 0
    acc.insert k <| f v₁ v₂

@[inline]
def mapValues {α β γ} [BEq α] [Hashable α] (f : β → γ) (self : HashMap α β) : HashMap α γ :=
  self.map (fun _ v => f v)

@[inline]
def filterValues {α β} [BEq α] [Hashable α] (p : β → Bool) (self : HashMap α β) : HashMap α β :=
  self.filter (fun _ v => p v)

end Std.HashMap

@[ext]
structure BaseDimension where
  name : String
  deriving Repr, DecidableEq, Hashable

namespace BaseDimension

def dimensionless : BaseDimension := ⟨"∅"⟩
def length : BaseDimension := ⟨"L"⟩
def mass : BaseDimension := ⟨"M"⟩
def time : BaseDimension := ⟨"T"⟩
def temperature : BaseDimension := ⟨"Θ"⟩
def current : BaseDimension := ⟨"I"⟩
def amount_of_substance : BaseDimension := ⟨"N"⟩
def luminous_intensity : BaseDimension := ⟨"J"⟩

instance : EmptyCollection BaseDimension where
  emptyCollection := dimensionless

instance : Inhabited BaseDimension where
  default := dimensionless

instance : Repr BaseDimension where
  reprPrec := fun b _ => b.name

end BaseDimension

inductive Dimension : Type
  | base : BaseDimension → Dimension
  | mul : Dimension → Dimension → Dimension
  | pow : Dimension → ℚ → Dimension
deriving Repr

namespace Dimension

instance : One Dimension where
  one := base ∅

instance : Mul Dimension where
  mul := Dimension.mul

instance : Div Dimension where
  div d₁ d₂ := Dimension.mul d₁ (Dimension.pow d₂ (-1))

instance : Pow Dimension ℚ where
  pow := Dimension.pow

instance : Inhabited Dimension where
  default := 1

def mk (b : BaseDimension) (n : ℚ := 1) : Dimension :=
  match n with
  | 0 => 1
  | 1 => base b
  | _ => (base b) ^ n

def isDimensionless (d : Dimension) : Bool :=
  match d with
  | base b => b == ∅
  | _ => false

open Std in
def toExponentMap : Dimension → HashMap BaseDimension ℚ
  | base b =>
    if b == ∅ then
      HashMap.emptyWithCapacity
    else
      HashMap.emptyWithCapacity.insert b 1
  | mul d₁ d₂ =>
    let m₁ := toExponentMap d₁
    let m₂ := toExponentMap d₂
    HashMap.unionWith (· + ·) m₁ m₂
  | pow d n =>
    match n with
    | 0 => HashMap.emptyWithCapacity
    | 1 => toExponentMap d
    | _ => toExponentMap d |>.mapValues (· * n)

/--
Convert a dimension to a list of base dimensions with their respective exponents.
The list is sorted by the name of the base dimensions giving a canonical representation.

This guarantees that two dimensions with the same bases and exponents will yield the same list.

No proof yet, need to dig into HashMap and mergeSort to ensure that the order is stable.
-/
def toList (d : Dimension) :=
  toExponentMap d
  |>.filterValues (· != 0)
  |>.toList
  |>.mergeSort (·.1.name < ·.1.name)

def ofList : List (BaseDimension × ℚ) → Dimension
  | [] => 1
  | (b, n) :: [] => Dimension.mk b n
  | (b, n) :: xs => xs.foldl (init := Dimension.mk b n) fun d (b, n) =>
    match n with
    | 0 => d
    | 1 => d * base b
    | _ => d * (base b) ^ n

def normalize (d : Dimension) : Dimension := ofList (d.toList)

instance : BEq Dimension where
  beq d₁ d₂ := d₁.toList == d₂.toList

end Dimension


structure NormalizedDimension where
  dim : Dimension
  is_normalized : dim.normalize = dim

namespace NormalizedDimension
open Dimension

-- this should be formally proved, but it is a bit tricky
axiom base_is_norm (b : BaseDimension) : (base b).normalize = base b
axiom norm_norm_eq_nor (d : Dimension) : d.normalize.normalize = d.normalize

theorem one_is_norm : (1 : Dimension).normalize = 1 := by
  have h : 1 = (base ∅) := rfl
  rw [h, base_is_norm ∅]

instance : One NormalizedDimension where
  one := ⟨ 1, one_is_norm ⟩

instance : Inhabited NormalizedDimension where
  default := 1

def repr_dim (d : Dimension) : String :=
  match d with
  | base b => b.name
  | mul d₁ d₂ => s!"{repr_dim d₁}·{repr_dim d₂}"
  | pow d n =>
    match n with
    | 1 => repr_dim d
    | 2 => s!"{repr_dim d}²"
    | 3 => s!"{repr_dim d}³"
    | 4 => s!"{repr_dim d}⁴"
    | 5 => s!"{repr_dim d}⁵"
    | -1 => s!"{repr_dim d}⁻¹"
    | -2 => s!"{repr_dim d}⁻²"
    | -3 => s!"{repr_dim d}⁻³"
    | -4 => s!"{repr_dim d}⁻⁴"
    | -5 => s!"{repr_dim d}⁻⁵"
    | _ =>
      if n == (1/2:ℚ) then
        s!"√{repr_dim d}"
      else
        s!"{repr_dim d}^{n}"

instance : Repr NormalizedDimension where
  reprPrec nd _ := repr_dim nd.dim

instance : Mul NormalizedDimension where
  mul nd₁ nd₂ := ⟨ (nd₁.dim * nd₂.dim).normalize, by rw [norm_norm_eq_nor]⟩

instance : Div NormalizedDimension where
  div nd₁ nd₂ := ⟨ (nd₁.dim / nd₂.dim).normalize, by rw [norm_norm_eq_nor]⟩

instance : Pow NormalizedDimension ℚ where
  pow nd n := ⟨ (nd.dim ^ n).normalize, by rw [norm_norm_eq_nor]⟩

instance : BEq NormalizedDimension where
  beq nd₁ nd₂ := nd₁.dim == nd₂.dim

-- This is a hack to make sure that the BEq instance is lawful
-- This should be proved formally, but it is a bit tricky
axiom norm_eq_of_beq (nd₁ nd₂ : NormalizedDimension) : nd₁ == nd₂ → nd₁ = nd₂
axiom norm_rfl (nd : NormalizedDimension) : nd == nd

instance : LawfulBEq NormalizedDimension where
  eq_of_beq {nd₁ nd₂} h := norm_eq_of_beq nd₁ nd₂ h
  rfl {nd} := norm_rfl nd


def length : NormalizedDimension := ⟨base BaseDimension.length, by rw [base_is_norm]⟩
def mass : NormalizedDimension := ⟨base BaseDimension.mass, by rw [base_is_norm]⟩
def time : NormalizedDimension := ⟨base BaseDimension.time, by rw [base_is_norm]⟩
def temperature : NormalizedDimension := ⟨base BaseDimension.temperature, by rw [base_is_norm]⟩
def current : NormalizedDimension := ⟨base BaseDimension.current, by rw [base_is_norm]⟩
def amount_of_substance : NormalizedDimension :=
  ⟨base BaseDimension.amount_of_substance, by rw [base_is_norm]⟩
def luminous_intensity : NormalizedDimension :=
  ⟨base BaseDimension.luminous_intensity, by rw [base_is_norm]⟩


#eval length
#eval mass
#eval time
#eval temperature
#eval current
#eval amount_of_substance
#eval luminous_intensity
#eval length^(0:ℚ) -- Should yield 1
#eval length^(1:ℚ) -- Should yield L
#eval ((length ^ (1/2:ℚ)) ^(2:ℚ)) -- Should yield L
#eval (mass * length * mass * mass)
#eval (mass^(-1:ℚ)* time * length / time)
#eval length * mass * time^(-1:ℚ) -- Should
def exp := (2:ℚ)
#eval mass / time ^ exp
#eval (time  * length * time ^ (-1:ℚ)) == length -- Should yield true

end NormalizedDimension
