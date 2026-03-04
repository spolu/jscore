/-
  JSCore₀ Taint — static taint tracking over the AST.
  taintedBy, notTaintedIn — must be Decidable (purely syntactic, finite traversal).
-/
import JSCore.Syntax

namespace JSCore

-- Pattern matching (duplicated from Trace to avoid circular imports)
private def matchesPat (target : String) (pattern : String) : Bool :=
  go (target.splitOn ".") (pattern.splitOn ".")
where
  go : List String → List String → Bool
  | _ :: _, ["*"] => true
  | t :: ts, p :: ps => (p == "*" || t == p) && go ts ps
  | [], [] => true
  | _, _ => false

-- Free variables of an expression.
-- Uses well-founded recursion with sizeOf.
mutual
  def freeVars : Expr → List String
    | .var x => [x]
    | .strLit _ => []
    | .numLit _ => []
    | .boolLit _ => []
    | .none => []
    | .letConst x e body => freeVars e ++ (freeVars body |>.filter (· != x))
    | .letMut _ e body => freeVars e ++ freeVars body
    | .assign x e body => [x] ++ freeVars e ++ freeVars body
    | .field e _ => freeVars e
    | .obj pairs => freeVarsPairs pairs
    | .spread base overrides => freeVars base ++ freeVarsPairs overrides
    | .arr exprs => freeVarsList exprs
    | .index e idx => freeVars e ++ freeVars idx
    | .push arrName valExpr => [arrName] ++ freeVars valExpr
    | .seq e1 e2 => freeVars e1 ++ freeVars e2
    | .ite c t f => freeVars c ++ freeVars t ++ freeVars f
    | .forOf x arrExpr body => freeVars arrExpr ++ (freeVars body |>.filter (· != x))
    | .whileLoop _ c body => freeVars c ++ freeVars body
    | .«break» => []
    | .ret e => freeVars e
    | .call _ argExprs resultBinder body =>
      freeVarsPairs argExprs ++ (freeVars body |>.filter (· != resultBinder))
    | .throw e => freeVars e
    | .tryCatch body errName handler =>
      freeVars body ++ (freeVars handler |>.filter (· != errName))
    | .binOp _ e1 e2 => freeVars e1 ++ freeVars e2
    | .unOp _ e => freeVars e

  def freeVarsPairs : List (String × Expr) → List String
    | [] => []
    | (_, e) :: rest => freeVars e ++ freeVarsPairs rest

  def freeVarsList : List Expr → List String
    | [] => []
    | e :: rest => freeVars e ++ freeVarsList rest
end

-- Collect all bindings that transitively use a given source variable.
-- Accumulator-based: acc starts as [source] and grows as taint propagates.
-- untaintedCalls: call targets whose results do NOT propagate taint.
mutual
  def collectTaintedBindings (untaintedCalls : List String) (acc : List String) : Expr → List String
    | .letConst x e body =>
      let newAcc := if (freeVars e).any (· ∈ acc) then x :: acc else acc
      collectTaintedBindings untaintedCalls newAcc body
    | .letMut x e body =>
      let newAcc := if (freeVars e).any (· ∈ acc) then x :: acc else acc
      collectTaintedBindings untaintedCalls newAcc body
    | .assign x e body =>
      let newAcc := if (freeVars e).any (· ∈ acc) then x :: acc else acc
      collectTaintedBindings untaintedCalls newAcc body
    | .call target args resultBinder body =>
      -- Check if any arg's freeVars intersect acc
      let argsTainted := collectTaintedBindingsPairs untaintedCalls acc args
      let callTaints := argsTainted && !(untaintedCalls.any (· == target))
      let newAcc := if callTaints then resultBinder :: acc else acc
      collectTaintedBindings untaintedCalls newAcc body
    | .seq e1 e2 =>
      let acc1 := collectTaintedBindings untaintedCalls acc e1
      collectTaintedBindings untaintedCalls acc1 e2
    | .ite c t f =>
      let accC := collectTaintedBindings untaintedCalls acc c
      let accT := collectTaintedBindings untaintedCalls accC t
      let accF := collectTaintedBindings untaintedCalls accC f
      -- Union: everything tainted in either branch
      accT ++ accF.filter (· ∉ accT)
    | .forOf _ arrExpr body =>
      let acc1 := collectTaintedBindings untaintedCalls acc arrExpr
      collectTaintedBindings untaintedCalls acc1 body
    | .whileLoop _ c body =>
      let acc1 := collectTaintedBindings untaintedCalls acc c
      collectTaintedBindings untaintedCalls acc1 body
    | .tryCatch body _ handler =>
      let acc1 := collectTaintedBindings untaintedCalls acc body
      collectTaintedBindings untaintedCalls acc1 handler
    | .ret e => collectTaintedBindings untaintedCalls acc e
    | .throw e => collectTaintedBindings untaintedCalls acc e
    | .binOp _ e1 e2 =>
      let acc1 := collectTaintedBindings untaintedCalls acc e1
      collectTaintedBindings untaintedCalls acc1 e2
    | .unOp _ e => collectTaintedBindings untaintedCalls acc e
    | _ => acc

  -- Check if any arg expression's freeVars intersect the tainted set
  def collectTaintedBindingsPairs (untaintedCalls : List String) (acc : List String) :
      List (String × Expr) → Bool
    | [] => false
    | (_, e) :: rest =>
      (freeVars e).any (· ∈ acc) || collectTaintedBindingsPairs untaintedCalls acc rest
end

-- Is expression e tainted by binding source?
def taintedBy (prog : Expr) (source : String) (untaintedCalls : List String) (e : Expr) : Bool :=
  let taintedSet := collectTaintedBindings untaintedCalls [source] prog
  (freeVars e).any (· ∈ taintedSet)

-- Collected call expressions and their argument expressions for a given pattern
structure CallExprInfo where
  target : String
  namedArgs : List (String × Expr)
  deriving Repr

-- Extract all call sites matching a pattern from an expression
mutual
  def callExprsIn : Expr → String → List CallExprInfo
    | .call target args _ body, pattern =>
      let rest := callExprsIn body pattern
      let argCalls := callExprsInPairs args pattern
      if matchesPat target pattern then
        { target := target, namedArgs := args } :: argCalls ++ rest
      else
        argCalls ++ rest
    | .letConst _ e body, pattern => callExprsIn e pattern ++ callExprsIn body pattern
    | .letMut _ e body, pattern => callExprsIn e pattern ++ callExprsIn body pattern
    | .assign _ e body, pattern => callExprsIn e pattern ++ callExprsIn body pattern
    | .seq e1 e2, pattern => callExprsIn e1 pattern ++ callExprsIn e2 pattern
    | .ite c t f, pattern =>
      callExprsIn c pattern ++ callExprsIn t pattern ++ callExprsIn f pattern
    | .forOf _ arrExpr body, pattern =>
      callExprsIn arrExpr pattern ++ callExprsIn body pattern
    | .whileLoop _ c body, pattern => callExprsIn c pattern ++ callExprsIn body pattern
    | .tryCatch body _ handler, pattern =>
      callExprsIn body pattern ++ callExprsIn handler pattern
    | .ret e, pattern => callExprsIn e pattern
    | .throw e, pattern => callExprsIn e pattern
    | .binOp _ e1 e2, pattern => callExprsIn e1 pattern ++ callExprsIn e2 pattern
    | .unOp _ e, pattern => callExprsIn e pattern
    | _, _ => []

  def callExprsInPairs : List (String × Expr) → String → List CallExprInfo
    | [], _ => []
    | (_, e) :: rest, pattern => callExprsIn e pattern ++ callExprsInPairs rest pattern
end

-- Control-flow safety: check that no conditional guarding a matching call depends on source
mutual
  def controlFlowSafe (source pattern : String) : Expr → Bool
    | .ite cond thn els =>
      let thnHasCalls := !(callExprsIn thn pattern).isEmpty
      let elsHasCalls := !(callExprsIn els pattern).isEmpty
      let condSafe := if thnHasCalls || elsHasCalls then
        !(freeVars cond).any (· == source) else true
      condSafe && controlFlowSafe source pattern cond &&
        controlFlowSafe source pattern thn && controlFlowSafe source pattern els
    | .whileLoop _ cond body =>
      let bodyHasCalls := !(callExprsIn body pattern).isEmpty
      let condSafe := if bodyHasCalls then !(freeVars cond).any (· == source) else true
      condSafe && controlFlowSafe source pattern cond &&
        controlFlowSafe source pattern body
    | .letConst _ e body =>
      controlFlowSafe source pattern e && controlFlowSafe source pattern body
    | .letMut _ e body =>
      controlFlowSafe source pattern e && controlFlowSafe source pattern body
    | .assign _ e body =>
      controlFlowSafe source pattern e && controlFlowSafe source pattern body
    | .call _ args _ body =>
      controlFlowSafePairs source pattern args && controlFlowSafe source pattern body
    | .seq e1 e2 =>
      controlFlowSafe source pattern e1 && controlFlowSafe source pattern e2
    | .forOf _ arrExpr body =>
      controlFlowSafe source pattern arrExpr && controlFlowSafe source pattern body
    | .tryCatch body _ handler =>
      controlFlowSafe source pattern body && controlFlowSafe source pattern handler
    | .ret e => controlFlowSafe source pattern e
    | .throw e => controlFlowSafe source pattern e
    | .binOp _ e1 e2 =>
      controlFlowSafe source pattern e1 && controlFlowSafe source pattern e2
    | .unOp _ e => controlFlowSafe source pattern e
    | _ => true

  def controlFlowSafePairs (source pattern : String) : List (String × Expr) → Bool
    | [] => true
    | (_, e) :: rest =>
      controlFlowSafe source pattern e && controlFlowSafePairs source pattern rest
end

-- No call matching pattern has any argument that depends on source
def notTaintedIn (prog : Expr) (source pattern : String)
    (untaintedCalls : List String := []) : Bool :=
  let taintedSet := collectTaintedBindings untaintedCalls [source] prog
  let calls := callExprsIn prog pattern
  let argsIndependent := calls.all fun ci =>
    ci.namedArgs.all fun (_, argExpr) =>
      !(freeVars argExpr).any (· ∈ taintedSet)
  let cfSafe := controlFlowSafe source pattern prog
  cfSafe && argsIndependent

end JSCore
