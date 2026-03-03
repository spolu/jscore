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
mutual
  def collectTaintedBindings (source : String) : Expr → List String
    | .letConst x e body =>
      let eTainted := collectTaintedBindings source e
      let taintedSet := source :: eTainted
      if (freeVars e).any (· ∈ taintedSet) then
        x :: collectTaintedBindings source body ++ eTainted
      else
        collectTaintedBindings source body ++ eTainted
    | .letMut x e body =>
      let eTainted := collectTaintedBindings source e
      let taintedSet := source :: eTainted
      if (freeVars e).any (· ∈ taintedSet) then
        x :: collectTaintedBindings source body ++ eTainted
      else
        collectTaintedBindings source body ++ eTainted
    | .assign x e body =>
      let eTainted := collectTaintedBindings source e
      let taintedSet := source :: eTainted
      if (freeVars e).any (· ∈ taintedSet) then
        x :: collectTaintedBindings source body ++ eTainted
      else
        collectTaintedBindings source body ++ eTainted
    | .call _ args _ body =>
      collectTaintedBindingsPairs source args ++ collectTaintedBindings source body
    | .seq e1 e2 =>
      collectTaintedBindings source e1 ++ collectTaintedBindings source e2
    | .ite c t f =>
      collectTaintedBindings source c ++ collectTaintedBindings source t ++
      collectTaintedBindings source f
    | .forOf _ arrExpr body =>
      collectTaintedBindings source arrExpr ++ collectTaintedBindings source body
    | .whileLoop _ c body =>
      collectTaintedBindings source c ++ collectTaintedBindings source body
    | .tryCatch body _ handler =>
      collectTaintedBindings source body ++ collectTaintedBindings source handler
    | .ret e => collectTaintedBindings source e
    | .throw e => collectTaintedBindings source e
    | .binOp _ e1 e2 =>
      collectTaintedBindings source e1 ++ collectTaintedBindings source e2
    | .unOp _ e => collectTaintedBindings source e
    | _ => []

  def collectTaintedBindingsPairs (source : String) : List (String × Expr) → List String
    | [] => []
    | (_, e) :: rest =>
      collectTaintedBindings source e ++ collectTaintedBindingsPairs source rest
end

-- Is expression e tainted by binding source?
def taintedBy (prog : Expr) (source : String) (e : Expr) : Bool :=
  let taintedBindings := source :: collectTaintedBindings source prog
  (freeVars e).any (· ∈ taintedBindings)

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

-- No call matching pattern has any argument that depends on source
def notTaintedIn (prog : Expr) (source pattern : String) : Bool :=
  let calls := callExprsIn prog pattern
  let argsIndependent := calls.all fun ci =>
    ci.namedArgs.all fun (_, argExpr) =>
      !taintedBy prog source argExpr
  let controlIndependent := decide (source ∉ freeVars prog)
  controlIndependent && argsIndependent

end JSCore
