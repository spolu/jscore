import JSCore.Syntax
import JSCore.Values
import JSCore.Eval
import JSCore.Trace
import JSCore.Properties
import JSCore.Taint
import JSCore.Tactics
import JSCore.Metatheory.EvalEq
import JSCore.Metatheory.TraceComposition

open JSCore

def lookupProject_body : Expr :=
  (.call "db.project.findUnique"
    [("where", (.obj [
  ("id", (.var "projectId")),
  ("workspaceId", (.field
  (.var "auth")
  "workspaceId"))
]))]
    "project"
    (.ret
      (.var "project")))

-- argAtPath helper for "where.workspaceId" with two-field obj
private theorem argAtPath_where_wsId_2 (target resultId : String) (idVal wsVal : Val) :
    argAtPath { target := target,
                args := [("where", Val.obj [("id", idVal), ("workspaceId", wsVal)])],
                resultId := resultId } "where.workspaceId" = some wsVal := by
  have h1 : ("where.workspaceId" : String).splitOn "." = ["where", "workspaceId"] := by native_decide
  have h2 : (BEq.beq "where" "where" : Bool) = true := by native_decide
  have h3 : (BEq.beq "id" "workspaceId" : Bool) = false := by native_decide
  have h4 : (BEq.beq "workspaceId" "workspaceId" : Bool) = true := by native_decide
  simp only [argAtPath, h1, argLookup, fieldLookup, List.find?, List.foldl,
             h2, h3, h4, ite_true, ite_false]

-- Helper: evaluate the arg obj for the findUnique call
private theorem eval_findUnique_arg (n : Nat) (env : Env) (store : Store)
    (fields : List (String × Val)) (idVal wsVal : Val)
    (h_env_auth : env "auth" = some (Val.obj fields))
    (h_store_auth : store "auth" = none)
    (h_fl : fieldLookup fields "workspaceId" = some wsVal)
    (h_env_id : lookup env store "projectId" = some idVal)
    (hn : n ≥ 4) :
    eval n env store (.obj [("id", .var "projectId"), ("workspaceId", .field (.var "auth") "workspaceId")]) =
    mkResult (.ok (Val.obj [("id", idVal), ("workspaceId", wsVal)])) store [] := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 4 := ⟨n - 4, by omega⟩
  rw [show n' + 4 = (n' + 3) + 1 from by omega, eval_obj_eq]
  simp only [List.foldl]
  rw [show n' + 3 = (n' + 2) + 1 from by omega, eval_var_eq]
  rw [h_env_id]
  simp only [mkResult_outcome, mkResult_store, mkResult_trace, List.nil_append, List.append_nil]
  rw [eval_field_var h_env_auth h_store_auth h_fl (by omega)]
  simp only [mkResult_outcome, mkResult_store, mkResult_trace, List.nil_append, List.append_nil]
  rfl

theorem lookupProject_ws_isolation
    (fuel : Nat)
    (auth : Val)
    (projectId : Val)
    (env : Env)
    (store : Store)
    (h_env_auth : env "auth" = some auth)
    (h_env_projectId : env "projectId" = some projectId)
    (h_store_auth : store "auth" = none)
    (h_store_projectId : store "projectId" = none)
    (h_req_0 : ∃ __n_lhs_0 __n_rhs_0, Option.bind (some auth) (fun __v => Val.field' __v "workspaceId") = some (Val.num __n_lhs_0) ∧ some (Val.num 0) = some (Val.num __n_rhs_0) ∧ __n_lhs_0 > __n_rhs_0)
    (h_fuel : fuel = 5)
    : ∀ c ∈ callsTo (eval fuel env store lookupProject_body).trace "db.*",
      argAtPath c "where.workspaceId" = Option.bind (some auth) (fun __v => Val.field' __v "workspaceId") := by
  subst h_fuel
  -- Extract auth structure from @requires
  obtain ⟨n, _, h_ws, _, _⟩ := h_req_0
  simp only [Option.bind] at h_ws
  have ⟨fields, h_auth_eq, h_fl⟩ : ∃ fields, auth = Val.obj fields ∧
      fieldLookup fields "workspaceId" = some (Val.num n) := by
    cases auth with
    | obj fields => exact ⟨fields, rfl, by simpa [Val.field'] using h_ws⟩
    | str _ => simp [Val.field'] at h_ws
    | num _ => simp [Val.field'] at h_ws
    | bool _ => simp [Val.field'] at h_ws
    | none => simp [Val.field'] at h_ws
    | arr _ => simp [Val.field'] at h_ws
  subst h_auth_eq
  simp only [Option.bind, Val.field', h_fl]
  intro c hc
  -- Step through outer call
  simp only [lookupProject_body] at hc
  rw [show (5:Nat) = 4+1 from rfl, eval_call_eq] at hc
  simp only [List.foldl] at hc
  have h_l_pid : lookup env store "projectId" = some projectId := by
    rw [lookup_none h_store_projectId, h_env_projectId]
  rw [eval_findUnique_arg 4 env store fields projectId (Val.num n)
      h_env_auth h_store_auth h_fl h_l_pid (by omega)] at hc
  simp only [mkResult_outcome, mkResult_store, mkResult_trace,
             List.nil_append, List.append_nil] at hc
  -- hc: c ∈ callsTo ([.call cr] ++ ret_trace) "db.*"
  rw [callsTo_append] at hc
  rw [List.mem_append] at hc
  cases hc with
  | inl h1 =>
    have hp : matchesPattern "db.project.findUnique" "db.*" = true := by native_decide
    have := mem_callsTo_singleton hp h1; subst this
    exact argAtPath_where_wsId_2 "db.project.findUnique" "project" projectId (Val.num n)
  | inr h2 =>
    -- ret (var "project") produces no calls
    exfalso
    have h_ret_trace : (eval 4 (env.set "project" Val.none) store (.ret (.var "project"))).trace = [] := by
      rw [show (4:Nat) = 3+1 from rfl, eval_ret_trace, show (3:Nat) = 2+1 from rfl, eval_var_trace_nil]
    rw [h_ret_trace, callsTo_nil] at h2
    exact List.not_mem_nil c h2

theorem lookupProject_ws_isolation_canonical
    (fuel : Nat)
    (auth : Val)
    (projectId : Val)
    (h_req_0 : ∃ __n_lhs_0 __n_rhs_0, Option.bind (some auth) (fun __v => Val.field' __v "workspaceId") = some (Val.num __n_lhs_0) ∧ some (Val.num 0) = some (Val.num __n_rhs_0) ∧ __n_lhs_0 > __n_rhs_0)
    (h_fuel : fuel = 5)
    : ∀ c ∈ callsTo (eval fuel ((emptyEnv.set "auth" auth).set "projectId" projectId) emptyStore lookupProject_body).trace "db.*",
      argAtPath c "where.workspaceId" = Option.bind (some auth) (fun __v => Val.field' __v "workspaceId") := by
  intro c hc
  exact lookupProject_ws_isolation
    fuel auth projectId
    ((emptyEnv.set "auth" auth).set "projectId" projectId) emptyStore
    (by simp [Env.set, emptyEnv])
    (by simp [Env.set, emptyEnv])
    (by simp [emptyStore])
    (by simp [emptyStore])
    h_req_0 h_fuel c hc
