import JSCore.Syntax
import JSCore.Values
import JSCore.Eval
import JSCore.Trace
import JSCore.Properties
import JSCore.Taint
import JSCore.Tactics

open JSCore

def taintSafeLiteral_body : Expr :=
  (.call "logger.info"
    [("arg0", (.strLit "static log line"))]
    "__void_0"
    Expr.none)

theorem taintSafeLiteral_no_secret_leak
    : notTaintedIn taintSafeLiteral_body "secret" "logger.*" = true := by
  native_decide
