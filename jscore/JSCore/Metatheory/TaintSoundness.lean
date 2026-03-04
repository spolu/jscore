/-
  JSCore₀ Metatheory — Taint Soundness.
  Changing a taint source's value doesn't change any matching call's arguments.
-/
import JSCore.Eval
import JSCore.Taint

namespace JSCore

-- Main taint soundness theorem:
-- If no call matching pattern has any argument tainted by source,
-- then changing source's value doesn't change any matching call's arguments.
theorem taint_soundness (fuel : Nat) (prog : Expr) (source pattern : String)
    (untaintedCalls : List String)
    (h : notTaintedIn prog source pattern untaintedCalls = true) :
    ∀ env env' store,
      (∀ x, x ≠ source → env x = env' x) →
      callsTo (eval fuel env store prog).trace pattern =
      callsTo (eval fuel env' store prog).trace pattern := by
  sorry

end JSCore
