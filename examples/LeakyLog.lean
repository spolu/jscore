import JSCore.Syntax
import JSCore.Values
import JSCore.Eval
import JSCore.Trace
import JSCore.Properties
import JSCore.Taint
import JSCore.Tactics

open JSCore

def leakyLog_body : Expr :=
  (.call "unsafeHash.digest"
    [("arg0", (.var "secret"))]
    "tag"
    (.letConst "logLine"
      (.binOp .add
        (.binOp .add
          (.var "userId")
          (.strLit ":"))
        (.var "tag"))
      (.call "logger.info"
        [("arg0", (.var "logLine"))]
        "__void_0"
        Expr.none)))

theorem leakyLog_secret_leaks_to_logs
    : notTaintedIn leakyLog_body "secret" "logger.*" ["crypto.hmac"] = false := by
  native_decide
