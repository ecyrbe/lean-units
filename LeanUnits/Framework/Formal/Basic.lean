import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.InjSurj
import LeanUnits.Framework.Quantities.Basic

/-!
Credit to @TerrenceTao for these lemmas about Fomalizing quantities into the AddMonoidAlgebra.
The original source code under Apache License is there :
https://github.com/teorth/analysis/blob/18d4fd7253ff17a05133d9b6b120b5f08f5ce6ad/analysis/Analysis/Misc/UnitsSystem.lean
Permission was given to use his lemmas and definitions as a starting point for the formal side of the library.
-/

namespace Units


abbrev Formal (δ α) [Semiring α] [AddCommGroup δ] := AddMonoidAlgebra α δ

namespace Quantity
set_option linter.unusedSectionVars false

variable {α : Type} [Semiring α]
variable {δ : Type} [AddCommGroup δ]
variable {d d₁ d₂ : δ}

theorem val_inj (q₁ q₂ : Quantity d α) :
  q₁.val = q₂.val ↔ q₁ = q₂ := by
  constructor
  · intro h; cases q₁; cases q₂; congr
  · intro h; rw [h]

theorem cast_eq (q₁ : Quantity d₁ α) (q₂ : Quantity d₂ α) (h : d₁ = d₂ := by module)
  : q₁.val = q₂.val ↔ q₁ = q₂.cast h.symm := by
  subst h
  rw [val_inj]
  rfl

theorem cast_eq_symm (q₁ : Quantity d₁ α) (q₂ : Quantity d₂ α) (h : d₁ = d₂ := by module)
  : q₁ = q₂.cast h.symm ↔ q₂ = q₁.cast h := by aesop

@[simp]
theorem cast_val (q : Quantity d₁ α) (h : d₁ = d₂ := by module)
  : (q.cast h).val = q.val := by
  subst h
  rfl

@[coe]
noncomputable def toFormal (q : Quantity d α) : Formal δ α :=
  AddMonoidAlgebra.single d q.val

end Quantity

end Units
