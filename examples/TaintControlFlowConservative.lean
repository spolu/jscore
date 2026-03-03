import JSCore.Syntax
import JSCore.Values
import JSCore.Eval
import JSCore.Trace
import JSCore.Properties
import JSCore.Taint
import JSCore.Tactics

open JSCore

def taintControlFlowConservative_body : Expr :=
  (.seq
    (.ite
      (.var "secret")
      (.call "logger.info"
        [("arg0", (.strLit "branch-true"))]
        "__void_0"
        Expr.none)
      (.call "logger.info"
        [("arg0", (.strLit "branch-false"))]
        "__void_1"
        Expr.none))
    Expr.none)

theorem taintControlFlowConservative_baseline_unused_source
    : notTaintedIn taintControlFlowConservative_body "unused" "logger.*" = true := by
  native_decide
