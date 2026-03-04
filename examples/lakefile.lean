import Lake
open Lake DSL

package examples where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require jscore from ".." / "jscore"

@[default_target]
lean_lib exportWorkspaceData_jscore

@[default_target]
lean_lib reorderTasks_jscore

@[default_target]
lean_lib rotateApiKey_jscore

@[default_target]
lean_lib scopedUpdate_jscore

@[default_target]
lean_lib signAndLog_jscore

@[default_target]
lean_lib taintSafeLiteral_jscore
