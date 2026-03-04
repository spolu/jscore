import JSCore.Syntax
import JSCore.Values
import JSCore.Eval
import JSCore.Trace
import JSCore.Properties
import JSCore.Taint
import JSCore.Tactics

open JSCore

def exportWorkspaceData_body : Expr :=
  (.call "db.projects.findMany"
    [("where", (.obj [
  ("workspaceId", (.field
  (.var "auth")
  "workspaceId"))
]))]
    "projects"
    (.call "db.tasks.findMany"
      [("where", (.obj [
  ("workspaceId", (.field
  (.var "auth")
  "workspaceId"))
]))]
      "tasks"
      (.ret
        (.obj [
          ("projects", (.var "projects")),
          ("tasks", (.var "tasks"))
        ]))))

theorem exportWorkspaceData_ws_isolation
    (fuel : Nat)
    (auth : Val)
    (format : Val)
    (env : Env)
    (store : Store)
    (h_env_auth : env "auth" = some auth)
    (h_env_format : env "format" = some format)
    : ∀ c ∈ callsTo (eval fuel env store exportWorkspaceData_body).trace "db.*",
      argAtPath c "where.workspaceId" = Val.field' auth "workspaceId" := by
  intro c hc
  sorry

theorem exportWorkspaceData_read_only
    : (callExprsIn exportWorkspaceData_body "db.*.update").length = 0 := by
  native_decide

theorem exportWorkspaceData_read_only_1
    : (callExprsIn exportWorkspaceData_body "db.*.create").length = 0 := by
  native_decide

theorem exportWorkspaceData_read_only_2
    : (callExprsIn exportWorkspaceData_body "db.*.delete").length = 0 := by
  native_decide
