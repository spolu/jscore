import JSCore.Syntax
import JSCore.Values
import JSCore.Eval
import JSCore.Trace
import JSCore.Properties
import JSCore.Taint
import JSCore.Tactics
import JSCore.Metatheory.EvalEq
import JSCore.Metatheory.FuelMono
import JSCore.Metatheory.ArgAt

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

private theorem auth_ws_string (auth : Val)
    (h : match Option.bind (some auth) (fun __v => Val.field' __v "workspaceId"),
               some (Val.str "ws_") with
         | some __lhs, some __rhs => Val.startsWith' __lhs __rhs = true
         | _, _ => False) :
    ∃ fields s, auth = Val.obj fields ∧
      fieldLookup fields "workspaceId" = some (Val.str s) := by
  simp only [Option.bind] at h
  cases h_f : Val.field' auth "workspaceId" with
  | none => rw [h_f] at h; simp at h
  | some l =>
    rw [h_f] at h
    cases l with
    | str s =>
      cases auth with
      | obj fields => exact ⟨fields, s, rfl, by simpa [Val.field'] using h_f⟩
      | str _ => simp [Val.field'] at h_f
      | num _ => simp [Val.field'] at h_f
      | bool _ => simp [Val.field'] at h_f
      | none => simp [Val.field'] at h_f
      | arr _ => simp [Val.field'] at h_f
    | num n => simp [Val.startsWith'] at h
    | bool b => simp [Val.startsWith'] at h
    | none => simp [Val.startsWith'] at h
    | obj fs => simp [Val.startsWith'] at h
    | arr es => simp [Val.startsWith'] at h

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
  rw [evalPairsAux_pure_cons (eval_field_var h_env h_store h_fl (by omega))]
  rw [evalPairsAux_nil]
  rfl

-- Helper: ret of obj of vars has no db.* calls in trace

private theorem ret_obj_vars_no_calls (env : Env) (store : Store) :
    callsTo (eval 4 env store
      (.ret (.obj [("projects", .var "projects"), ("tasks", .var "tasks")]))).trace "db.*" = [] := by
  have h_t : (eval 4 env store
      (.ret (.obj [("projects", .var "projects"), ("tasks", .var "tasks")]))).trace = [] := by
    rw [show (4:Nat) = 3+1 from rfl, eval_ret_trace]
    rw [show (3:Nat) = 2+1 from rfl, eval_obj_eq]
    cases h1 : lookup env store "projects" with
    | none =>
      rw [evalPairsAux_cons, show (2:Nat) = 1+1 from rfl, eval_var_eq, h1]
      rfl
    | some v1 =>
      rw [evalPairsAux_pure_cons (v := v1)
          (by rw [show (2:Nat) = 1+1 from rfl, eval_var_eq, h1])]
      cases h2 : lookup env store "tasks" with
      | none =>
        rw [evalPairsAux_cons, show (2:Nat) = 1+1 from rfl, eval_var_eq, h2]
        rfl
      | some v2 =>
        rw [evalPairsAux_pure_cons (v := v2)
            (by rw [show (2:Nat) = 1+1 from rfl, eval_var_eq, h2])]
        rw [evalPairsAux_nil]
        rfl
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
    (h_req_0 : match Option.bind (some auth) (fun __v => Val.field' __v "workspaceId"), some (Val.str "ws_") with | some __lhs, some __rhs => Val.startsWith' __lhs __rhs = true | _, _ => False)
    (h_fuel : fuel ≥ 6)
    : ∀ c ∈ callsTo (eval fuel env store exportWorkspaceData_body).trace "db.*",
      argAt c ["where", "workspaceId"] = Option.bind (some auth) (fun __v => Val.field' __v "workspaceId") := by
  rw [eval_fuel_mono 6 exportWorkspaceData_body (by decide) fuel h_fuel]
  obtain ⟨fields, s, h_auth_eq, h_fl⟩ := auth_ws_string auth h_req_0
  subst h_auth_eq
  simp only [Option.bind, Val.field', h_fl]
  intro c hc
  -- Step through outer call
  simp only [exportWorkspaceData_body] at hc
  rw [show (6:Nat) = 5+1 from rfl, eval_call_eq] at hc
  rw [evalPairsAux_pure_cons
      (eval_arg_obj 5 env store fields (Val.str s) h_env_auth h_store_auth h_fl (by omega)),
      evalPairsAux_nil] at hc
  simp only [mkResult_outcome, mkResult_store, mkResult_trace,
             List.nil_append, List.append_nil] at hc
  -- Split: [.call cr1] ++ inner_trace
  rw [callsTo_append] at hc
  rw [List.mem_append] at hc
  cases hc with
  | inl h1 =>
    have hp : matchesPattern "db.projects.findMany" "db.*" = true := by native_decide
    have := mem_callsTo_singleton hp h1; subst this
    simp
  | inr h2 =>
    have h_env_auth2 : (env.set "projects" Val.none) "auth" = some (Val.obj fields) := by
      simp [Env.set, show ("auth" : String) ≠ "projects" from by decide, h_env_auth]
    rw [show (5:Nat) = 4+1 from rfl, eval_call_eq] at h2
    rw [evalPairsAux_pure_cons
        (eval_arg_obj 4 (env.set "projects" Val.none) store fields (Val.str s)
          h_env_auth2 h_store_auth h_fl (by omega)),
        evalPairsAux_nil] at h2
    simp only [mkResult_outcome, mkResult_store, mkResult_trace,
               List.nil_append, List.append_nil] at h2
    -- Split: [.call cr2] ++ ret_trace
    rw [callsTo_append] at h2
    rw [List.mem_append] at h2
    cases h2 with
    | inl h2a =>
      have hp : matchesPattern "db.tasks.findMany" "db.*" = true := by native_decide
      have := mem_callsTo_singleton hp h2a; subst this
      simp
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
    (h_req_0 : match Option.bind (some auth) (fun __v => Val.field' __v "workspaceId"), some (Val.str "ws_") with | some __lhs, some __rhs => Val.startsWith' __lhs __rhs = true | _, _ => False)
    (h_fuel : fuel ≥ 6)
    : ∀ c ∈ callsTo (eval fuel ((emptyEnv.set "auth" auth).set "format" format) emptyStore exportWorkspaceData_body).trace "db.*",
      argAt c ["where", "workspaceId"] = Option.bind (some auth) (fun __v => Val.field' __v "workspaceId") := by
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
