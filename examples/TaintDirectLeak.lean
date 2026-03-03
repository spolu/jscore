import JSCore.Syntax
import JSCore.Values
import JSCore.Eval
import JSCore.Trace
import JSCore.Properties
import JSCore.Taint
import JSCore.Tactics

open JSCore

def taintDirectLeak_body : Expr :=
  (.call "logger.info"
    [("arg0", (.var "secret"))]
    "__void_0"
    Expr.none)

theorem taintDirectLeak_baseline_unused_source
    : notTaintedIn taintDirectLeak_body "unused" "logger.*" = true := by
  native_decide
