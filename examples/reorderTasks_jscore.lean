import JSCore.Syntax

import JSCore.Values

import JSCore.Eval

import JSCore.Trace

import JSCore.Properties

import JSCore.Taint

import JSCore.Tactics


import JSCore.Metatheory.EvalEq

import JSCore.Metatheory.TraceComposition

import JSCore.Metatheory.ForOfCallsTo


open JSCore


def reorderTasks_body : Expr :=
  (.seq
    (.forOf "taskId"
      (.var "tasks")
      (.call "db.task.update"
        [("where", (.obj [
  ("id", (.var "taskId")),
  ("projectId", (.var "projectId"))
])), ("data", (.obj [
  ("position", (.numLit 0))
]))]
        "__void_0"
        Expr.none))
    Expr.none)


abbrev loop_body : Expr :=
  .call "db.task.update"
    [("where", (.obj [("id", (.var "taskId")), ("projectId", (.var "projectId"))])),
     ("data", (.obj [("position", (.numLit 0))]))]
    "__void_0"
    Expr.none

-- argAtPath computation helper: string ops via native_decide, structure via simp

private theorem argAtPath_where_pid (id_val pid_val : Val) :
    argAtPath { target := "db.task.update",
                args := [("where", Val.obj [("id", id_val), ("projectId", pid_val)]),
                         ("data", Val.obj [("position", Val.num 0)])],
                resultId := "__void_0" } "where.projectId" = some pid_val := by
  have h1 : ("where.projectId" : String).splitOn "." = ["where", "projectId"] := by native_decide
  have h2 : (BEq.beq "where" "where" : Bool) = true := by native_decide
  have h3 : (BEq.beq "id" "projectId" : Bool) = false := by native_decide
  have h4 : (BEq.beq "projectId" "projectId" : Bool) = true := by native_decide
  simp only [argAtPath, h1, argLookup, fieldLookup, List.find?, List.foldl,
             h2, h3, h4, ite_true, ite_false]

-- Helper: single iteration properties (store invariant + callsTo property)

private theorem loop_body_props (env : Env) (store : Store) (elem projectId : Val)
    (h_env : env "projectId" = some projectId)
    (h_store : store "projectId" = none) :
    let r := eval 4 (Env.set env "taskId" elem) store loop_body
    r.store = store ∧
    (∀ c ∈ callsTo r.trace "db.*", argAtPath c "where.projectId" = some projectId) := by
  cases h_tid : store "taskId" with
  | none =>
    have h_l_tid : lookup (Env.set env "taskId" elem) store "taskId" = some elem := by
      rw [lookup_none h_tid]; simp [Env.set]
    have h_l_pid : lookup (Env.set env "taskId" elem) store "projectId" = some projectId := by
      rw [lookup_none h_store]
      simp [Env.set, show ("projectId" : String) ≠ "taskId" from by decide, h_env]
    simp only [loop_body, eval, mkResult, Env.set, List.foldl,
      List.append, List.nil_append, List.append_nil, h_l_tid, h_l_pid]
    refine ⟨trivial, ?_⟩
    intro c hc
    have h_pat : matchesPattern "db.task.update" "db.*" = true := by native_decide
    have := mem_callsTo_singleton h_pat hc; subst this
    exact argAtPath_where_pid elem projectId
  | some tid =>
    have h_l_tid : lookup (Env.set env "taskId" elem) store "taskId" = some tid := by
      rw [lookup_some h_tid]
    have h_l_pid : lookup (Env.set env "taskId" elem) store "projectId" = some projectId := by
      rw [lookup_none h_store]
      simp [Env.set, show ("projectId" : String) ≠ "taskId" from by decide, h_env]
    simp only [loop_body, eval, mkResult, Env.set, List.foldl,
      List.append, List.nil_append, List.append_nil, h_l_tid, h_l_pid]
    refine ⟨trivial, ?_⟩
    intro c hc
    have h_pat : matchesPattern "db.task.update" "db.*" = true := by native_decide
    have := mem_callsTo_singleton h_pat hc; subst this
    exact argAtPath_where_pid tid projectId

-- Step through outer eval to expose the foldl

private theorem eval_outer_trace (env : Env) (store : Store) (elems : List Val)
    (h_store_tasks : store "tasks" = none)
    (h_env_tasks : env "tasks" = some (Val.arr elems)) :
    callsTo (eval 6 env store reorderTasks_body).trace "db.*" =
    callsTo (elems.foldl (forOfFoldStep 4 env "taskId" loop_body)
        (mkResult (.ok Val.none) store [])).trace "db.*" := by
  have h_lookup : lookup env store "tasks" = some (Val.arr elems) := by
    rw [lookup_none h_store_tasks, h_env_tasks]
  simp only [reorderTasks_body]
  rw [show (6 : Nat) = 5 + 1 from rfl, eval_seq_none_trace]
  rw [show (5 : Nat) = 4 + 1 from rfl, eval_forOf_eq]
  rw [show (4 : Nat) = 3 + 1 from rfl, eval_var_eq]
  rw [h_lookup]
  simp only [mkResult_outcome, mkResult_store, mkResult_trace, List.nil_append, List.append_nil]
  rfl

-- Non-array tasks produces no db.* calls

private theorem non_arr_no_calls (env : Env) (store : Store) (tasks : Val)
    (h_store_tasks : store "tasks" = none)
    (h_env_tasks : env "tasks" = some tasks)
    (h_not_arr : ∀ (elems : List Val), tasks ≠ Val.arr elems) :
    callsTo (eval 6 env store reorderTasks_body).trace "db.*" = [] := by
  have h_lookup : lookup env store "tasks" = some tasks := by
    rw [lookup_none h_store_tasks, h_env_tasks]
  simp only [reorderTasks_body]
  rw [show (6 : Nat) = 5 + 1 from rfl, eval_seq_none_trace]
  rw [show (5 : Nat) = 4 + 1 from rfl, eval_forOf_eq]
  rw [show (4 : Nat) = 3 + 1 from rfl, eval_var_eq]
  rw [h_lookup]
  simp only [mkResult_outcome, mkResult_store, mkResult_trace, List.nil_append, List.append_nil]
  cases tasks with
  | arr elems => exact absurd rfl (h_not_arr elems)
  | str _ | num _ | bool _ | none | obj _ =>
    simp only [callsTo, extractCalls, List.filterMap, List.filter]


theorem reorderTasks_ws_isolation
    (fuel : Nat)
    (auth : Val)
    (projectId : Val)
    (tasks : Val)
    (env : Env)
    (store : Store)
    (h_env_auth : env "auth" = some auth)
    (h_env_projectId : env "projectId" = some projectId)
    (h_env_tasks : env "tasks" = some tasks)
    (h_store_auth : store "auth" = none)
    (h_store_projectId : store "projectId" = none)
    (h_store_tasks : store "tasks" = none)
    (h_req_0 : ∃ __n_lhs_0 __n_rhs_0, Option.bind (some auth) (fun __v => Val.field' __v "workspaceId") = some (Val.num __n_lhs_0) ∧ some (Val.num 0) = some (Val.num __n_rhs_0) ∧ __n_lhs_0 > __n_rhs_0)
    (h_fuel : fuel = 6)
    : ∀ c ∈ callsTo (eval fuel env store reorderTasks_body).trace "db.*",
      argAtPath c "where.projectId" = some projectId := by
  subst h_fuel
  intro c hc
  cases h_tasks : tasks with
  | arr elems =>
    rw [h_tasks] at h_env_tasks
    rw [eval_outer_trace env store elems h_store_tasks h_env_tasks] at hc
    -- Prove step invariant
    have h_step : ∀ elem store_i, store_i = store →
        let r := eval 4 (env.set "taskId" elem) store_i loop_body
        r.store = store ∧ (∀ c ∈ callsTo r.trace "db.*",
          argAtPath c "where.projectId" = some projectId) :=
      fun elem _ h_si => h_si ▸ loop_body_props env store elem projectId h_env_projectId h_store_projectId
    -- Use forOfFold_callsTo from metatheory
    have h_inv := forOfFold_callsTo 4 env "taskId" elems loop_body "db.*"
      (fun c => argAtPath c "where.projectId" = some projectId)
      (fun s => s = store)
      (mkResult (.ok Val.none) store [])
      rfl
      (fun c hc => by simp [callsTo, extractCalls, mkResult, List.filterMap, List.filter] at hc)
      h_step
    exact h_inv.1 c hc
  | _ =>
    have h_not_arr : ∀ (elems : List Val), tasks ≠ Val.arr elems := by
      rw [h_tasks]; intro elems; exact Val.noConfusion
    rw [non_arr_no_calls env store tasks h_store_tasks h_env_tasks h_not_arr] at hc
    exact absurd hc (List.not_mem_nil c)

