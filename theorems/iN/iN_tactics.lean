import Lean

open Lean Elab Tactic Meta

/- elab "lift_poison" : tactic =>
  Tactic.withMainContext do
    let goalType ← Lean.Elab.Tactic.getMainTarget
    dbg_trace f!"goal type: {goalType}"


    goalType.eq
 -/
