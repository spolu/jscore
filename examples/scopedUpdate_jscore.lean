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


private theorem argAtPath_update_wsId (target resultId : String) (idVal wsVal : Val) :
    argAtPath { target := target,
                args := [("where", Val.obj [("id", idVal), ("workspaceId", wsVal)]),
                         ("data", Val.obj [("updatedAt", Val.str "now")])],
                resultId := resultId } "where.workspaceId" = some wsVal := by
  have h1 : ("where.workspaceId" : String).splitOn "." = ["where", "workspaceId"] := by native_decide
  have h2 : (BEq.beq "where" "where" : Bool) = true := by native_decide
  have h3 : (BEq.beq "id" "workspaceId" : Bool) = false := by native_decide
  have h4 : (BEq.beq "workspaceId" "workspaceId" : Bool) = true := by native_decide
  simp only [argAtPath, h1, argLookup, fieldLookup, List.find?, List.foldl,
             h2, h3, h4, ite_true, ite_false]

-- Helper: evaluate obj [("id", var "itemId")]

private theorem eval_id_arg (n : Nat) (env : Env) (store : Store) (idVal : Val)
    (h_id : lookup env store "itemId" = some idVal) (hn : n ≥ 3) :
    eval n env store (.obj [("id", .var "itemId")]) =
    mkResult (.ok (Val.obj [("id", idVal)])) store [] := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 3 := ⟨n - 3, by omega⟩
  rw [show n' + 3 = (n' + 2) + 1 from by omega, eval_obj_eq]
  simp only [List.foldl]
  rw [show n' + 2 = (n' + 1) + 1 from by omega, eval_var_eq, h_id]
  simp only [mkResult_outcome, mkResult_store, mkResult_trace, List.nil_append, List.append_nil]

-- Helper: field access on item (field may or may not exist)

private theorem eval_field_item (n : Nat) (env : Env) (store : Store)
    (item_fields : List (String × Val)) (fname : String)
    (h_env_item : env "item" = some (Val.obj item_fields))
    (h_store_item : store "item" = none)
    (hn : n ≥ 2) :
    eval n env store (.field (.var "item") fname) =
    mkResult (.ok (match fieldLookup item_fields fname with
                   | some v => v | none => Val.none)) store [] := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
  rw [show n' + 2 = (n' + 1) + 1 from by omega, eval_field_eq]
  rw [show n' + 1 = n' + 1 from rfl, eval_var_eq]
  rw [lookup_none h_store_item, h_env_item]
  simp only [mkResult_outcome, mkResult_store, mkResult_trace]
  cases fieldLookup item_fields fname with
  | some v => rfl
  | none => rfl

-- Helper: evaluate the update's "where" obj with id and workspaceId fields

private theorem eval_update_where_2 (n : Nat) (env : Env) (store : Store)
    (item_fields : List (String × Val)) (wsVal : Val)
    (h_env_item : env "item" = some (Val.obj item_fields))
    (h_store_item : store "item" = none)
    (h_fl_ws : fieldLookup item_fields "workspaceId" = some wsVal)
    (hn : n ≥ 4) :
    eval n env store (.obj [("id", .field (.var "item") "id"),
                            ("workspaceId", .field (.var "item") "workspaceId")]) =
    mkResult (.ok (Val.obj [("id", match fieldLookup item_fields "id" with
                                   | some v => v | none => Val.none),
                            ("workspaceId", wsVal)])) store [] := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 4 := ⟨n - 4, by omega⟩
  rw [show n' + 4 = (n' + 3) + 1 from by omega, eval_obj_eq]
  simp only [List.foldl]
  have h1 := eval_field_item (n' + 3) env store item_fields "id" h_env_item h_store_item (by omega)
  rw [h1]
  simp only [mkResult_outcome, mkResult_store, mkResult_trace, List.nil_append, List.append_nil]
  rw [eval_field_var h_env_item h_store_item h_fl_ws (by omega)]
  simp only [mkResult_outcome, mkResult_store, mkResult_trace, List.nil_append, List.append_nil]
  rfl

-- Helper: evaluate "data" obj [("updatedAt", strLit "now")]

private theorem eval_data_arg (n : Nat) (env : Env) (store : Store) (hn : n ≥ 3) :
    eval n env store (.obj [("updatedAt", .strLit "now")]) =
    mkResult (.ok (Val.obj [("updatedAt", Val.str "now")])) store [] := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 3 := ⟨n - 3, by omega⟩
  rw [show n' + 3 = (n' + 2) + 1 from by omega, eval_obj_eq]
  simp only [List.foldl]
  rw [show n' + 2 = (n' + 1) + 1 from by omega, eval_strLit_eq]
  simp only [mkResult_outcome, mkResult_store, mkResult_trace, List.nil_append, List.append_nil]


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



def scopedUpdate_body : Expr :=
  (.call "db.item.findUnique"
    [("where", (.obj [
  ("id", (.var "itemId"))
]))]
    "__call_2"
    (.letConst "item"
      (.var "__ensures_item")
      (.seq
        (.ite
          (.binOp .eq
            (.var "kind")
            (.strLit "workspace"))
          (.call "db.item.update"
            [("where", (.obj [
  ("id", (.field
  (.var "item")
  "id")),
  ("workspaceId", (.field
  (.var "item")
  "workspaceId"))
])), ("data", (.obj [
  ("updatedAt", (.strLit "now"))
]))]
            "__void_0"
            Expr.none)
          (.call "db.item.update"
            [("where", (.obj [
  ("id", (.field
  (.var "item")
  "id"))
])), ("data", (.obj [
  ("updatedAt", (.strLit "now"))
]))]
            "__void_1"
            Expr.none))
        Expr.none)))


theorem scopedUpdate_scoped_update
    (fuel : Nat)
    (auth : Val)
    (kind : Val)
    (itemId : Val)
    (env : Env)
    (store : Store)
    (h_env_auth : env "auth" = some auth)
    (h_env_kind : env "kind" = some kind)
    (h_env_itemId : env "itemId" = some itemId)
    (h_store_auth : store "auth" = none)
    (h_store_kind : store "kind" = none)
    (h_store_itemId : store "itemId" = none)
    (h_req_0 : ∃ __n_lhs_0 __n_rhs_0,
      Option.bind (some auth) (fun __v => Val.field' __v "workspaceId") =
        some (Val.num __n_lhs_0) ∧
      some (Val.num 0) = some (Val.num __n_rhs_0) ∧ __n_lhs_0 > __n_rhs_0)
    (h_req_1 : some kind = some (Val.str "workspace"))
    (__ensures_item : Val)
    (h_env___ensures_item : env "__ensures_item" = some __ensures_item)
    (h_store___ensures_item : store "__ensures_item" = none)
    (h_ensures_0 : Option.bind (some __ensures_item) (fun __v => Val.field' __v "workspaceId") =
      Option.bind (some auth) (fun __v => Val.field' __v "workspaceId"))
    (h_store_item : store "item" = none)
    (h_fuel : fuel = 9)
    : ∀ c ∈ callsTo (eval fuel env store scopedUpdate_body).trace "db.item.update",
      argAtPath c "where.workspaceId" =
        Option.bind (some auth) (fun __v => Val.field' __v "workspaceId") := by
  subst h_fuel
  -- Phase 1: Extract structure from hypotheses
  obtain ⟨n, _, h_ws, _, _⟩ := h_req_0
  simp only [Option.bind] at h_ws
  have ⟨auth_fields, h_auth_eq, h_fl_auth⟩ : ∃ fs, auth = Val.obj fs ∧
      fieldLookup fs "workspaceId" = some (Val.num n) := by
    cases auth with
    | obj fs => exact ⟨fs, rfl, by simpa [Val.field'] using h_ws⟩
    | str _ => simp [Val.field'] at h_ws
    | num _ => simp [Val.field'] at h_ws
    | bool _ => simp [Val.field'] at h_ws
    | none => simp [Val.field'] at h_ws
    | arr _ => simp [Val.field'] at h_ws
  subst h_auth_eq
  have h_kind : kind = Val.str "workspace" := by cases h_req_1; rfl
  subst h_kind
  simp only [Option.bind, Val.field', h_fl_auth] at h_ensures_0
  have ⟨item_fields, h_item_eq, h_fl_item⟩ : ∃ fs, __ensures_item = Val.obj fs ∧
      fieldLookup fs "workspaceId" = some (Val.num n) := by
    cases __ensures_item with
    | obj fs => exact ⟨fs, rfl, by simpa [Val.field'] using h_ensures_0⟩
    | str _ => simp [Val.field'] at h_ensures_0
    | num _ => simp [Val.field'] at h_ensures_0
    | bool _ => simp [Val.field'] at h_ensures_0
    | none => simp [Val.field'] at h_ensures_0
    | arr _ => simp [Val.field'] at h_ensures_0
  subst h_item_eq
  simp only [Option.bind, Val.field', h_fl_auth]
  intro c hc
  -- Phase 2: Outer call "db.item.findUnique"
  simp only [scopedUpdate_body] at hc
  rw [show (9:Nat) = 8+1 from rfl, eval_call_eq] at hc
  simp only [List.foldl] at hc
  rw [eval_id_arg 8 env store itemId (by rw [lookup_none h_store_itemId, h_env_itemId])
      (by omega)] at hc
  simp only [mkResult_outcome, mkResult_store, mkResult_trace,
             List.nil_append, List.append_nil] at hc
  rw [callsTo_append] at hc; rw [List.mem_append] at hc
  cases hc with
  | inl h_outer =>
    exfalso
    have : matchesPattern "db.item.findUnique" "db.item.update" = false := by native_decide
    simp [callsTo, extractCalls, List.filterMap, List.filter, this] at h_outer
  | inr h_body =>
  -- Phase 3: letConst "item" (var "__ensures_item")
  rw [show (8:Nat) = 7+1 from rfl, eval_letConst_eq] at h_body
  have h_var_ens : eval 7 (env.set "__call_2" Val.none) store (Expr.var "__ensures_item") =
      mkResult (.ok (Val.obj item_fields)) store [] := by
    rw [show (7:Nat) = 6+1 from rfl, eval_var_eq]
    rw [show lookup (env.set "__call_2" Val.none) store "__ensures_item" =
        some (Val.obj item_fields) from by
      rw [lookup_none h_store___ensures_item]
      simp [Env.set, show ("__ensures_item" : String) ≠ "__call_2" from by decide,
            h_env___ensures_item]]
  rw [h_var_ens] at h_body
  simp only [mkResult_outcome, mkResult_store, mkResult_trace,
             List.nil_append, List.append_nil] at h_body
  -- Phase 4: seq (ite ...) Expr.none
  rw [show (7:Nat) = 6+1 from rfl, eval_seq_none_trace] at h_body
  -- Phase 5: ite condition = true
  rw [show (6:Nat) = 5+1 from rfl, eval_ite_eq] at h_body
  -- env₂ = (env.set "__call_2" Val.none).set "item" (Val.obj item_fields)
  have h_l_kind : lookup ((env.set "__call_2" Val.none).set "item" (Val.obj item_fields))
      store "kind" = some (Val.str "workspace") := by
    rw [lookup_none h_store_kind]
    simp [Env.set, show ("kind" : String) ≠ "item" from by decide,
          show ("kind" : String) ≠ "__call_2" from by decide, h_env_kind]
  have h_cond : eval 5 ((env.set "__call_2" Val.none).set "item" (Val.obj item_fields)) store
      (.binOp .eq (.var "kind") (.strLit "workspace")) =
      mkResult (.ok (.bool true)) store [] := by
    rw [show (5:Nat) = 4+1 from rfl, eval_binOp_eq]
    rw [show (4:Nat) = 3+1 from rfl, eval_var_eq, h_l_kind]
    simp only [mkResult_outcome, mkResult_store, mkResult_trace, List.nil_append]
    rw [eval_strLit_eq]
    simp only [mkResult_outcome, mkResult_store, mkResult_trace, List.append_nil, evalBinOp]
    have : (Val.str "workspace" == Val.str "workspace") = true := by native_decide
    rw [this]
  rw [h_cond] at h_body
  simp only [mkResult_outcome, mkResult_store, mkResult_trace,
             List.nil_append, List.append_nil] at h_body
  -- Phase 6: True branch — call "db.item.update"
  rw [show (5:Nat) = 4+1 from rfl, eval_call_eq] at h_body
  simp only [List.foldl] at h_body
  -- env₂ item lookup
  have h_env₂_item : ((env.set "__call_2" Val.none).set "item" (Val.obj item_fields)) "item" =
      some (Val.obj item_fields) := by simp [Env.set]
  rw [eval_update_where_2 4 ((env.set "__call_2" Val.none).set "item" (Val.obj item_fields))
      store item_fields (Val.num n) h_env₂_item h_store_item h_fl_item (by omega)] at h_body
  simp only [mkResult_outcome, mkResult_store, mkResult_trace,
             List.nil_append, List.append_nil] at h_body
  rw [eval_data_arg 4 ((env.set "__call_2" Val.none).set "item" (Val.obj item_fields))
      store (by omega)] at h_body
  simp only [mkResult_outcome, mkResult_store, mkResult_trace,
             List.nil_append, List.append_nil] at h_body
  -- Split: [.call update_cr] ++ Expr.none trace
  rw [callsTo_append] at h_body; rw [List.mem_append] at h_body
  cases h_body with
  | inl h_call =>
    have hp : matchesPattern "db.item.update" "db.item.update" = true := by native_decide
    have := mem_callsTo_singleton hp h_call; subst this
    exact argAtPath_update_wsId "db.item.update" "__void_0"
      (match fieldLookup item_fields "id" with | some v => v | none => Val.none)
      (Val.num n)
  | inr h_rest =>
    exfalso
    rw [eval_none_trace, callsTo_nil] at h_rest
    exact List.not_mem_nil c h_rest

