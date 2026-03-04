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

-- Var eval always produces empty trace and preserves store
private theorem eval_var_trace_nil {n : Nat} {env : Env} {store : Store} {x : String} :
    (eval (n + 1) env store (Expr.var x)).trace = [] := by
  rw [eval_var_eq]; cases lookup env store x <;> rfl

private theorem eval_var_store_eq {n : Nat} {env : Env} {store : Store} {x : String} :
    (eval (n + 1) env store (Expr.var x)).store = store := by
  rw [eval_var_eq]; cases lookup env store x <;> rfl

-- argAtPath helper for "where.workspaceId" path
private theorem argAtPath_where_wsId (target : String) (resultId : String) (wsId : Val) :
    argAtPath { target := target,
                args := [("where", Val.obj [("workspaceId", wsId)])],
                resultId := resultId } "where.workspaceId" = some wsId := by
  have h1 : ("where.workspaceId" : String).splitOn "." = ["where", "workspaceId"] := by native_decide
  have h2 : (BEq.beq "where" "where" : Bool) = true := by native_decide
  have h3 : (BEq.beq "workspaceId" "workspaceId" : Bool) = true := by native_decide
  simp only [argAtPath, h1, argLookup, fieldLookup, List.find?, List.foldl,
             h2, h3, ite_true, ite_false]

-- Helper: evaluate .field (.var "auth") "workspaceId" when auth = Val.obj fields
private theorem eval_auth_wsId (n : Nat) (env : Env) (store : Store)
    (fields : List (String × Val)) (wsVal : Val)
    (h_env : env "auth" = some (Val.obj fields))
    (h_store : store "auth" = none)
    (h_fl : fieldLookup fields "workspaceId" = some wsVal)
    (hn : n ≥ 3) :
    eval n env store (.field (.var "auth") "workspaceId") =
    mkResult (.ok wsVal) store [] := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 3 := ⟨n - 3, by omega⟩
  rw [show n' + 3 = (n' + 2) + 1 from by omega, eval_field_eq]
  rw [show n' + 2 = (n' + 1) + 1 from by omega, eval_var_eq]
  rw [lookup_none h_store, h_env]
  simp only [mkResult_outcome, mkResult_store, mkResult_trace, h_fl]

-- Helper: evaluate arg obj [("workspaceId", .field (.var "auth") "workspaceId")]
private theorem eval_arg_obj (n : Nat) (env : Env) (store : Store)
    (fields : List (String × Val)) (wsVal : Val)
    (h_env : env "auth" = some (Val.obj fields))
    (h_store : store "auth" = none)
    (h_fl : fieldLookup fields "workspaceId" = some wsVal)
    (hn : n ≥ 4) :
    eval n env store (.obj [("workspaceId", .field (.var "auth") "workspaceId")]) =
    mkResult (.ok (Val.obj [("workspaceId", wsVal)])) store [] := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 4 := ⟨n - 4, by omega⟩
  rw [show n' + 4 = (n' + 3) + 1 from by omega, eval_obj_eq]
  simp only [List.foldl]
  rw [eval_auth_wsId (n' + 3) env store fields wsVal h_env h_store h_fl (by omega)]
  simp only [mkResult_outcome, mkResult_store, mkResult_trace,
             List.nil_append, List.append_nil]

-- Ret always preserves inner trace
private theorem eval_ret_preserves_trace {n : Nat} {env : Env} {store : Store} {e : Expr} :
    (eval (n + 1) env store (.ret e)).trace = (eval n env store e).trace := by
  rw [eval_ret_eq]
  cases eval n env store e with
  | mk outcome s t =>
    cases outcome with
    | ok v => simp [mkResult]
    | error _ => rfl
    | brk => rfl
    | returned _ => rfl

-- Helper: ret of obj of vars has no db.* calls in trace
private theorem ret_obj_vars_no_calls (env : Env) (store : Store) :
    callsTo (eval 4 env store
      (.ret (.obj [("projects", .var "projects"), ("tasks", .var "tasks")]))).trace "db.*" = [] := by
  have h_t : (eval 4 env store
      (.ret (.obj [("projects", .var "projects"), ("tasks", .var "tasks")]))).trace = [] := by
    rw [show (4:Nat) = 3+1 from rfl, eval_ret_preserves_trace]
    rw [show (3:Nat) = 2+1 from rfl, eval_obj_eq]
    simp only [List.foldl, eval_var_trace_nil (n := 1), eval_var_store_eq (n := 1),
               List.nil_append, List.append_nil]
    generalize (eval 2 env store (Expr.var "projects")).outcome = o1
    cases o1 <;> (
      simp only [mkResult_outcome, mkResult_store, mkResult_trace, List.nil_append, List.append_nil,
                 eval_var_trace_nil (n := 1), eval_var_store_eq (n := 1)]
      generalize (eval 2 env store (Expr.var "tasks")).outcome = o2
      cases o2 <;> simp [mkResult_trace])
  rw [h_t]; rfl

-- Main theorem
theorem exportWorkspaceData_ws_isolation
    (fuel : Nat)
    (auth : Val)
    (format : Val)
    (env : Env)
    (store : Store)
    (h_env_auth : env "auth" = some auth)
    (h_env_format : env "format" = some format)
    (h_store_auth : store "auth" = none)
    (h_store_format : store "format" = none)
    (h_req_0 : ∃ __n_lhs_0 __n_rhs_0, Option.bind (some auth) (fun __v => Val.field' __v "workspaceId") = some (Val.num __n_lhs_0) ∧ some (Val.num 0) = some (Val.num __n_rhs_0) ∧ __n_lhs_0 > __n_rhs_0)
    (h_fuel : fuel = 6)
    : ∀ c ∈ callsTo (eval fuel env store exportWorkspaceData_body).trace "db.*",
      argAtPath c "where.workspaceId" = Option.bind (some auth) (fun __v => Val.field' __v "workspaceId") := by
  subst h_fuel
  obtain ⟨n, _, h_ws, _, _⟩ := h_req_0
  simp only [Option.bind] at h_ws
  -- Deduce auth = Val.obj fields
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
  simp only [exportWorkspaceData_body] at hc
  rw [show (6:Nat) = 5+1 from rfl, eval_call_eq] at hc
  simp only [List.foldl] at hc
  rw [eval_arg_obj 5 env store fields (Val.num n) h_env_auth h_store_auth h_fl (by omega)] at hc
  simp only [mkResult_outcome, mkResult_store, mkResult_trace,
             List.nil_append, List.append_nil] at hc
  -- Split: [.call cr1] ++ inner_trace
  rw [callsTo_append] at hc
  rw [List.mem_append] at hc
  cases hc with
  | inl h1 =>
    have hp : matchesPattern "db.projects.findMany" "db.*" = true := by native_decide
    simp only [callsTo, extractCalls, List.filterMap, List.filter, hp, ite_true,
               decide_true, List.mem_cons, List.mem_nil_iff, or_false] at h1
    subst h1
    exact argAtPath_where_wsId "db.projects.findMany" "projects" (Val.num n)
  | inr h2 =>
    have h_env_auth2 : (env.set "projects" Val.none) "auth" = some (Val.obj fields) := by
      simp [Env.set, show ("auth" : String) ≠ "projects" from by decide, h_env_auth]
    rw [show (5:Nat) = 4+1 from rfl, eval_call_eq] at h2
    simp only [List.foldl] at h2
    rw [eval_arg_obj 4 (env.set "projects" Val.none) store fields (Val.num n)
        h_env_auth2 h_store_auth h_fl (by omega)] at h2
    simp only [mkResult_outcome, mkResult_store, mkResult_trace,
               List.nil_append, List.append_nil] at h2
    -- Split: [.call cr2] ++ ret_trace
    rw [callsTo_append] at h2
    rw [List.mem_append] at h2
    cases h2 with
    | inl h2a =>
      have hp : matchesPattern "db.tasks.findMany" "db.*" = true := by native_decide
      simp only [callsTo, extractCalls, List.filterMap, List.filter, hp, ite_true,
                 decide_true, List.mem_cons, List.mem_nil_iff, or_false] at h2a
      subst h2a
      exact argAtPath_where_wsId "db.tasks.findMany" "tasks" (Val.num n)
    | inr h2b =>
      exfalso
      have h_no_calls := ret_obj_vars_no_calls
        ((env.set "projects" Val.none).set "tasks" Val.none) store
      rw [h_no_calls] at h2b
      exact List.not_mem_nil c h2b

theorem exportWorkspaceData_ws_isolation_canonical
    (fuel : Nat)
    (auth : Val)
    (format : Val)
    (h_req_0 : ∃ __n_lhs_0 __n_rhs_0, Option.bind (some auth) (fun __v => Val.field' __v "workspaceId") = some (Val.num __n_lhs_0) ∧ some (Val.num 0) = some (Val.num __n_rhs_0) ∧ __n_lhs_0 > __n_rhs_0)
    (h_fuel : fuel = 6)
    : ∀ c ∈ callsTo (eval fuel ((emptyEnv.set "auth" auth).set "format" format) emptyStore exportWorkspaceData_body).trace "db.*",
      argAtPath c "where.workspaceId" = Option.bind (some auth) (fun __v => Val.field' __v "workspaceId") := by
  intro c hc
  exact exportWorkspaceData_ws_isolation
    fuel auth format
    ((emptyEnv.set "auth" auth).set "format" format) emptyStore
    (by simp [Env.set, emptyEnv])
    (by simp [Env.set, emptyEnv])
    (by simp [emptyStore])
    (by simp [emptyStore])
    h_req_0 h_fuel c hc

theorem exportWorkspaceData_read_only
    : (callExprsIn exportWorkspaceData_body "db.*.update").length = 0 := by
  native_decide

theorem exportWorkspaceData_read_only_1
    : (callExprsIn exportWorkspaceData_body "db.*.create").length = 0 := by
  native_decide

theorem exportWorkspaceData_read_only_2
    : (callExprsIn exportWorkspaceData_body "db.*.delete").length = 0 := by
  native_decide
