import Std.Tactic.BVDecide
import Lean

open Lean Elab

elab "anything" : tactic =>
  Tactic.withMainContext do
    let ctx ← MonadLCtx.getLCtx

    let bit_params := ctx.foldl (fun bits decl =>
      let declName := decl.userName
      if declName.toString.startsWith "_bit" then
        decl :: bits
      else
        bits
    ) []

    /-
    Don't support switching when you have multiple bit params, will do case explosion.

    ```lean
    try grind
    try cases _hu <;> grind
    try simp only [bitvec_to_nat] at * <;> grind
    try simp only [bitvec_to_nat] at * <;> cases _hu <;> grind
    -- try cases _hu <;> bv_decide +acNf
    ```
    -/

    Tactic.evalTactic (← `(tactic| try grind))
    Tactic.evalTactic (← `(tactic| try simp only [bitvec_to_nat] at * <;> grind))

    /- if h: bit_params.length > 0 ∧ bit_params.length == 1 then
      let decl := bit_params[0]'h.left

      Tactic.evalTactic (← `(tactic| try cases $decl <;> grind))
      Tactic.evalTactic (← `(tactic| try simp only [bitvec_to_nat] at * <;> cases $decl <;> grind)) -/
