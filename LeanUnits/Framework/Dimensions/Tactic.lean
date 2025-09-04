import LeanUnits.Framework.Dimensions.Basic
import LeanUnits.Framework.Units.Basic
import LeanUnits.Framework.Units.Lemmas
import Mathlib.Tactic
import Lean

open Lean Meta Elab Tactic

namespace Units


axiom runtime_equiv.{u} {α : Sort u} [HasEquiv α] {a b : α} : a ≈ b

theorem eq_imp_equiv {μ} [Setoid μ] {u1 u2 : μ} (h : u1 = u2) : u1 ≈ u2 := by
  simp only [h, Setoid.refl]

elab "equiv_check" : tactic => do
  let goal ← withMainContext getMainTarget
  -- print the goal for debugging
  match goal with
  | .app (.app (.app (.app (.const `HasEquiv.Equiv _) _) _) a) b => do
    let a' ← instantiateMVars a
    let b' ← instantiateMVars b
    let equivExpr ← mkAppM ``HasEquiv.Equiv #[a', b']
    let decType ← mkAppM ``Decidable #[equivExpr]
    let decInst ←
      try
        synthInstance decType
      catch _ =>
        throwError "equiv_check failed: no Decidable instance for the equivalence"
    let decideExpr ← mkAppOptM ``decide #[some equivExpr, some decInst]
    let ok ← unsafe evalExpr Bool (mkConst ``Bool) decideExpr
    if ok then
      evalTactic (← `(tactic| exact runtime_equiv))
    else
      let left ← ppExpr a'
      let right ← unsafe ppExpr b'
      throwError s!"equiv_check failed: terms are not equivalent `{left}` and `{right}`"
  | _ => throwError "Goal must be an equivalence"

/--
Helper tactic that tries to prove equalities or equivalences between dimensions or units.
It tries the following strategies in order:
1. propositional equality check using `module` tactic
2. compile time equivalence check using `equiv_check` tactic that
   only works if the dimensions or units are fully instantiated (no free variables)
-/
macro "auto_equiv" : tactic =>
  `(tactic|
    (first | (first | apply eq_imp_equiv
                      module
                    | apply eq_imp_equiv
                      dsimp [instHMul, instHDiv, instHPow, dimension_set, derived_unit_set]
                      module )
           | equiv_check ))

macro "auto_dim" : tactic =>
  `(tactic|
    (first | rfl
           | try simp [𝒟,HasDimension.dimension, instHMul, instHDiv, instHPow,
                      HasEquiv.Equiv,Unit.instSetoidUnit, derived_unit_set]
             try module
    ))

end Units
