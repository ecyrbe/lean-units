import LeanUnits.Framework.Dimensions.Basic
import Mathlib.Tactic
import Lean

open Lean Meta Elab Tactic

/--
axiom that is emitted when `dimension_check` finds two terms are equal at runtime.
-/
axiom runtime_equal.{u} {α : Sort u} {a b : α} : a = b

elab "dimension_check" : tactic => do
  let goal ← withMainContext getMainTarget
  match goal with
  | .app (.app (.app (.const `Eq _) _) a) b => do
    let a' ← instantiateMVars a
    let b' ← instantiateMVars b
    let α ← inferType a'
    let beqType ← mkAppM ``BEq #[α]
    let inst ←
      try
        synthInstance beqType
      catch _ =>
        throwError "dimension_check failed: no BEq instance for the term type"
    let beqExpr ← mkAppOptM ``BEq.beq #[some α, some inst, some a', some b']
    let ok ← unsafe evalExpr Bool (mkConst ``Bool) beqExpr
    if ok then
      evalTactic (← `(tactic| exact runtime_equal))
    else
      -- eval left and right so we can prettry print them
      let left ← ppExpr a'
      let right ← ppExpr b'
      throwError s!"dimension_check failed: terms are not equal `{left}` and `{right}`"
  | _ => throwError "Goal must be an equality"

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

macro "auto_equiv" : tactic =>
  `(tactic|
    (first |
            (first | apply eq_imp_equiv; dsimp [instHMul, instHDiv, instHPow]; module
                   | apply eq_imp_equiv; module )
           | equiv_check ))
