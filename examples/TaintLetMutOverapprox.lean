import JSCore.Syntax
import JSCore.Values
import JSCore.Eval
import JSCore.Trace
import JSCore.Properties
import JSCore.Taint
import JSCore.Tactics

open JSCore

def taintLetMutOverapprox_body : Expr :=
  (.letMut "msg"
    (.strLit "public")
    (.seq
      (.ite
        (.var "rare")
        (.assign "msg"
          (.var "secret")
          (.call "logger.secretPath"
            [("arg0", (.var "msg"))]
            "__void_0"
            Expr.none))
        (.call "logger.public"
          [("arg0", (.var "msg"))]
          "__void_1"
          Expr.none))
      Expr.none))

theorem taintLetMutOverapprox_baseline_unused_source
    : notTaintedIn taintLetMutOverapprox_body "unused" "logger.*" = true := by
  native_decide
