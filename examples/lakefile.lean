import Lake
open Lake DSL

package examples where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require jscore from ".." / "jscore"

@[default_target]
lean_lib ExportWorkspaceData

@[default_target]
lean_lib ReorderTasks

@[default_target]
lean_lib RotateApiKey

@[default_target]
lean_lib taintSafeLiteral

@[default_target]
lean_lib taintDirectLeak

@[default_target]
lean_lib taintControlFlowConservative

@[default_target]
lean_lib taintLetMutOverapprox

@[default_target]
lean_lib TaintTradeoffChecks
