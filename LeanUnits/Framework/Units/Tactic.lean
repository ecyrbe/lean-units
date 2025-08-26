import LeanUnits.Framework.Dimensions.Basic
import Lean

open Lean Meta Elab Tactic

/--
axom that is emitted when `dimension_check` finds two terms are equal at runtime.
-/
axiom runtime_equal.{u} {α : Sort u} {a b : α} : a = b

elab "dimension_check" : tactic => do
  let goal ← withMainContext getMainTarget
  match goal with
  | .app (.app (.app (.const `Eq _) _) a) b => do
      -- Fall back to definitional equality
      if ← isDefEq a b then
        evalTactic (← `(tactic| exact rfl))
      else
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
          let left ← unsafe evalExpr Units.Dimension (mkConst ``Units.Dimension) a'
          let right ← unsafe evalExpr Units.Dimension (mkConst ``Units.Dimension) b'
          throwError s!"dimension_check failed: terms are not equal `{left}` and `{right}`"
  | _ => throwError "Goal must be an equality"
