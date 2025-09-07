import LeanUnits.Framework.Dimensions.Basic
import LeanUnits.Framework.Units.Basic
import LeanUnits.Framework.Units.Lemmas
import Mathlib.Tactic
import Lean

open Lean Meta Elab Tactic

namespace Units

theorem eq_imp_equiv {μ} [Setoid μ] {u1 u2 : μ} (h : u1 = u2) : u1 ≈ u2 := by
  simp only [h, Setoid.refl]

set_option linter.style.nativeDecide false
/--
Helper tactic that tries to prove equalities or equivalences between dimensions or units.
It tries the following strategies in order:
1. propositional equality check using `module` tactic
2. compile time equivalence check using `native_decide` tactic that
   only works if the dimensions or units are fully instantiated (no free variables)
-/
macro "auto_equiv" : tactic =>
  `(tactic|
    (first | (first | apply eq_imp_equiv
                      module
                    | apply eq_imp_equiv
                      dsimp [instHMul, instHDiv, instHPow, dimension_set, derived_unit_set]
                      module)
             trace s!"✅ Formaly proved equivalence"
           | native_decide
             trace s!"⚠️  Checked equivalence using `native_decide`"
           ))

/--
Helper tactic that tries to prove equalities between dimensions or units.
It tries the following strategies in order:
1. propositional equality check using `rfl`
2. simplification using `simp` with the lemmas tagged with the attribute
  `dimension_set` or `derived_unit_set`. so we don't use native_decide that would
  require to trust the compiler.
-/
macro "auto_dim" : tactic =>
  `(tactic|
    (first | rfl
           | try simp [𝒟,HasDimension.dimension, instHMul, instHDiv, instHPow,
                      HasEquiv.Equiv,Unit.instSetoidUnit, derived_unit_set]
             try module
    ))

end Units
