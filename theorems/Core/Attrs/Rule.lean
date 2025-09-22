import Lean
import theorems.iN.iN_rewrite
import theorems.iN.iN_lemmas

open Lean Meta

inductive RuleDirection where
  /-- Equivalent to `Rewrite`. -/
  | forward
  /-- Equivalent to `RewriteIff`. -/
  | iff
deriving Lean.ToJson, Repr

/-- For polymorphic bitwidth arguments.  -/
inductive BitwidthPoly : Type where
  | any
  /-- Assumes there is at most one bitwidth. -/
  | or (options : Array Nat)
deriving Lean.ToJson, Repr

/-- For literals and inline types.  -/
inductive Bitwidth : Type where
  | exact (n : Nat)
  /--
  Only `var` can appear inside the body of the rule.
  This is an index into `bit_variables` of the `ParseState` or rule environment.
  -/
  | bitvar (n : Nat)
deriving Lean.ToJson, Repr

mutual
  inductive RuleExprKind : Type where
    | const (n : Nat)
    | poison
    | app (inst : String) (args : Array RuleExpr)
    /-- Reference to inputs -/
    | input (n : Nat)
  deriving Lean.ToJson, Repr

  structure RuleExpr : Type where
    ty : Bitwidth
    kind : RuleExprKind
  deriving Lean.ToJson, Repr
end

instance : Inhabited RuleExprKind where
  default := .poison

structure Rule where
  /-- An array of bitwidths variables. -/
  bit_variables : Array BitwidthPoly
  /-- Each input has a reference to a bitwidth variable or is constant. -/
  inputs : Array Bitwidth
  /-- List of hypotheses/preconditions of the form `(expr : iN 1) ~> 1`.  -/
  hypotheses : Array RuleExpr

  direction : RuleDirection
  lhs : RuleExpr
  rhs : RuleExpr
deriving Lean.ToJson

/-- Why the fuck does Lean not have this. -/
def foldlEl (arr : Array α) (init : β) (f : β → Nat → α → β) : β := Id.run do
  let mut acc := init
  for h : i in [0:arr.size] do
    have lt : i < arr.size := h.upper
    acc := f acc i arr[i]
  acc

partial def Rule.toString (rule : Rule) : String := Id.run do
  let ty_str : Bitwidth → String
    | Bitwidth.exact v => s!"i{v}"
    | Bitwidth.bitvar v => s!"bv{v}"

  let bv_poly_str : Nat → BitwidthPoly → String
    | bv_idx, BitwidthPoly.any => s!"∀bv{bv_idx} : Nat"
    | bv_idx, BitwidthPoly.or options =>
      let pieces := s!"{options[0]!}" ++ options[1:].foldl (s!"{·}, {·}") ""
      s!"∀bv.{bv_idx} ∈ {"{"}{pieces}{"}"}"

  let rec expr_str (re : RuleExpr) : String :=
    match re.kind with
    | RuleExprKind.const v => s!"const : {ty_str re.ty} {v}"
    | RuleExprKind.poison => s!"poison : {ty_str re.ty}"
    | RuleExprKind.input v => s!"%{v}"
    | RuleExprKind.app inst args =>
      s!"({inst}" ++ (args.foldl (s!"{·} {expr_str ·}") "") ++ ")"

  let direction_str : RuleDirection → String
    | .iff => " <~> "
    | .forward => " ~> "

  /-
  rule ideal
  ∀bv0 : Nat
  %0 : bv0

  poison ~> %0
  -/
  let mut str := "rule\n"

  str := str ++ foldlEl rule.bit_variables "" fun r idx el =>
    r ++ s!"  {bv_poly_str idx el}\n"

  str := str ++ foldlEl rule.inputs "" fun r idx el =>
    r ++ s!"  %{idx} : {ty_str el}\n"

  str := str ++ foldlEl rule.hypotheses "" fun r _ el =>
    r ++ s!"  {expr_str el} ~> 1\n"

  let body_str :=
    (expr_str rule.lhs) ++ (direction_str rule.direction) ++ (expr_str rule.rhs)

  return str ++ "\n" ++ body_str

instance : ToString Rule where
  toString := Rule.toString

structure ParseConfig where
  validInstructions : Std.HashMap Name String
deriving Inhabited, Repr

structure ParseState where
  -- I don't really know how to use `ReaderT` + `StateRefT`
  config : ParseConfig

  bit_variables : Array BitwidthPoly
  /-- Index into `bit_variables`.  -/
  bit_variable_fvars : Std.HashMap FVarId Nat

  input_variables : Array Bitwidth
  /-- Index into `input_variables`.  -/
  input_variable_fvars : Std.HashMap FVarId Nat

  /-- Array of hypotheses of the form (expr : iN 1) ~> 1 -/
  hypotheses : Array RuleExpr
deriving Inhabited, Repr

abbrev M := StateRefT ParseState MetaM

namespace M

def run (config : ParseConfig) (m : M α) : MetaM α :=
  m.run' { (default : ParseState) with config }

def parseiNBitvecLit (nfExpr : Expr) : M (Option Nat) := do
  match_expr nfExpr with
  | poison _ =>
    return none

  | bitvec _ bv => match_expr bv with
    | BitVec.ofNat _ lit =>
      let nv := (← getNatValue? lit).get!
      return nv
    | _ => throwError m!"Invalid expression for bitvec literal"

  | _ => return none

def parseiN (expr : Expr) : M Bitwidth := do
  -- Lean.Expr.app (Lean.Expr.const `iN []) (Lean.Expr.lit (Lean.Literal.natVal 32))

  if expr.isAppOf ``iN then do
    -- Either extract out constant or variable bitwidth.
    let bitwidth_expr ← whnf expr.getAppArgs[0]!

    if let some v ← getNatValue? bitwidth_expr then
      return Bitwidth.exact v

    if let some fvar := bitwidth_expr.fvarId? then
      match (← get).bit_variable_fvars[fvar]? with
      | some idx => return Bitwidth.bitvar idx
      | none     => throwError "iN with non-polymorphic bitwidth"

  throwError "expected iN type, got {expr}"

end M

/-- Unfold typeclasses to their actual definitions.  -/
def unfoldProjs (e : Expr) : MetaM Expr := do
  transform e fun node => do
    if let some node' ← unfoldProjInst? node then
      return .visit (← instantiateMVars node')
    else
      return .continue

partial def RuleExpr.of (reducedExpr : Expr) : M RuleExpr := do
  go reducedExpr
where
  checkInstr (nfExpr : Expr) : M (Option RuleExprKind) := do
    if nfExpr.isApp then
      let fn := nfExpr.getAppFn
      let some name := fn.constName? | return none
      let some found := (← get).config.validInstructions[name]? | return none

      /- This is a valid instruction. Ignore the Nat arguments. -/
      let argsExpr ← nfExpr.getAppArgs.filterM
        fun (x : Expr) => do pure $ (← inferType x).isAppOf `iN

      let args ← argsExpr.mapM RuleExpr.of
      return RuleExprKind.app found args

    return none

  checkLit (nfExpr : Expr) : M (Option RuleExprKind) := do
    match_expr nfExpr with
    | poison _ =>
      return RuleExprKind.poison
    | _ =>
      return (← M.parseiNBitvecLit nfExpr).map RuleExprKind.const

  checkVar (nfExpr : Expr) : M (Option RuleExprKind) := do
    if let some fvar := nfExpr.fvarId? then
      let input_idx := (← get).input_variable_fvars.get! fvar
      return RuleExprKind.input input_idx

    return none

  go (expr : Expr) : M RuleExpr := do
    let ty ← inferType expr
    let bitwidth ← M.parseiN ty
    let expr ← whnfR expr

    let mut exprKind ← checkInstr expr

    if let none := exprKind then
      exprKind ← checkLit expr

    if let none := exprKind then
      exprKind ← checkVar expr

    if exprKind.isNone then
      throwError m!"invalid expression {expr}"

    return {
      ty := bitwidth,
      kind := exprKind.get!,
    }

namespace M

def parseHypot (nfExpr : Expr) : M RuleExpr := do
  match_expr nfExpr with
  | Rewrite _ lhs rhs =>

    let lhs_type ← inferType lhs
    let bw ← M.parseiN lhs_type
    match bw with
    | Bitwidth.exact 1 => pure
    | _ => throwError s!"Expected proposition of the form (expr : iN 1) ~> 1, got incorrect type {lhs_type}"

    let some 1 ← M.parseiNBitvecLit rhs | throwError s!"Expected proposition of the form (expr : iN 1) ~> 1, got ... ~> {rhs}"
    return ← RuleExpr.of lhs
  | _ => pure

  throwError s!"Expected proposition of the form (expr : iN 1) ~> 1, got {nfExpr}"

end M

def Rule.parseRule (type : Expr) (validInstructions : Std.HashMap Name String) : MetaM Rule := do
  /- forall {u : Nat} (a : BitVec u) (b : BitVec u) (con1 : BitVec u) (con2 : BitVec u), Eq.{1} (BitVec u) (...) (...) -/

  let config: ParseConfig := ⟨validInstructions⟩

  forallTelescope type fun fvars body => M.run config do
    /-
    Arguments in the forall:
    1. Polymorphic bitwidth, so `n : Nat`
    2. Hypotheses of the form `(expr : iN 1) ~> 1`
    3. Hypotheses that gate possible bitwidth, so `hn : Bits n`
    4. Arguments of type `iN n`

    Body of the forall is either a `~>` or `<~>` expression.
    -/
    fvars.forM fun fvar => do
      let fvar_type ← inferType fvar
      let fvar_type_type ← inferType fvar_type
      let fvar_id := fvar.fvarId!

      if fvar_type.isConstOf ``Nat then
        /- Polymorphic bitwidth -/
        modify fun s =>
          { s with
            bit_variables := s.bit_variables.push BitwidthPoly.any
            bit_variable_fvars := s.bit_variable_fvars.insert fvar_id (s.bit_variables.size)
          }
      else if fvar_type.isAppOf ``Bits64 then
        let fvar_possible ← whnf fvar_type.getAppArgs[0]!
        let some fvar := fvar_possible.fvarId? | throwError "Bits64 doesn't have an bitvar argument"
        let some bitv := (← getThe ParseState).bit_variable_fvars.get? fvar | throwError "Bits64 doesn't have an bitvar argument"

        modify fun s =>
          { s with
            bit_variables := s.bit_variables.set! bitv $ BitwidthPoly.or #[1, 8, 16, 32, 64]
          }
      else if fvar_type_type.isProp then
        /- Hypothesis of the form `(expr : iN 1) ~> 1` -/
        let reducedExpr ← unfoldProjs fvar_type
        let hypot ← M.parseHypot reducedExpr

        modify fun s =>
          { s with
            hypotheses := s.hypotheses.push hypot
          }
      else
        dbg_trace s!"we have something type {fvar_type} {repr fvar_type}"

        /- Argument of type `iN n` -/
        let bitwidth ← M.parseiN fvar_type

        modify fun s =>
          { s with
            input_variables := s.input_variables.push bitwidth
            input_variable_fvars := s.input_variable_fvars.insert fvar_id (s.input_variable_fvars.size)
          }

    /- Will convert use of `OfNat.ofNat` into `iN.bitvec (BitVec.ofNat ... )`.
       Will also unwrap `HAdd` → `iN.add` -/
    let reducedExpr ← unfoldProjs body

    /- `Rewrite` and `RewriteIff` take a `{n : Nat}` parameter first. -/
    let (lhs, dir, rhs) ← match_expr reducedExpr with
    | Rewrite _ lhs rhs =>
      let lhs' ← RuleExpr.of lhs
      let rhs' ← RuleExpr.of rhs
      pure (lhs', RuleDirection.forward, rhs')
    | RewriteIff _ lhs rhs =>
      let lhs' ← RuleExpr.of lhs
      let rhs' ← RuleExpr.of rhs
      pure (lhs', RuleDirection.iff, rhs')
    | _ => throwError "expected `~>` or `<~>` expression"

    let s := (← get)
    return {
      inputs := s.input_variables
      bit_variables := s.bit_variables
      direction := dir,
      hypotheses := s.hypotheses
      lhs := lhs,
      rhs := rhs,
    }
