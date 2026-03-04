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
lean_lib SignAndLog

@[default_target]
lean_lib LeakyLog

@[default_target]
lean_lib LookupProject

@[default_target]
lean_lib ScopedUpdate
