import taintDirectLeak
import taintControlFlowConservative
import taintLetMutOverapprox

open JSCore

theorem taintDirectLeak_expected_false
    : notTaintedIn taintDirectLeak_body "secret" "logger.*" = false := by
  native_decide

theorem taintControlFlowConservative_expected_false
    : notTaintedIn taintControlFlowConservative_body "secret" "logger.*" = false := by
  native_decide

theorem taintLetMutOverapprox_expected_false
    : notTaintedIn taintLetMutOverapprox_body "secret" "logger.public" = false := by
  native_decide

