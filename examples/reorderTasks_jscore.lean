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
import JSCore.Metatheory.LoopInvariant
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

-- Helpers: evaluate the two argument objects of the update call

private theorem eval_where_arg (n : Nat) (env : Env) (store : Store) (tidVal pidVal : Val)
    (h_tid : lookup env store "taskId" = some tidVal)
    (h_pid : lookup env store "projectId" = some pidVal)
    (hn : n ≥ 3) :
    eval n env store (.obj [("id", .var "taskId"), ("projectId", .var "projectId")]) =
    mkResult (.ok (Val.obj [("id", tidVal), ("projectId", pidVal)])) store [] := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 3 := ⟨n - 3, by omega⟩
  rw [show n' + 3 = (n' + 2) + 1 from by omega, eval_obj_eq]
  rw [evalPairsAux_pure_cons (v := tidVal)
      (by rw [show n' + 2 = (n' + 1) + 1 from by omega, eval_var_eq, h_tid])]
  rw [evalPairsAux_pure_cons (v := pidVal)
      (by rw [show n' + 2 = (n' + 1) + 1 from by omega, eval_var_eq, h_pid])]
  rw [evalPairsAux_nil]
  rfl

private theorem eval_data_arg (n : Nat) (env : Env) (store : Store) (hn : n ≥ 2) :
    eval n env store (.obj [("position", .numLit 0)]) =
    mkResult (.ok (Val.obj [("position", Val.num 0)])) store [] := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
  rw [show n' + 2 = (n' + 1) + 1 from by omega, eval_obj_eq]
  rw [evalPairsAux_pure_cons (v := Val.num 0) (by rw [eval_numLit_eq])]
  rw [evalPairsAux_nil]
  rfl

-- Helper: single iteration properties (store invariant + callsTo property)

private theorem loop_body_props (env : Env) (store : Store) (elem projectId : Val)
    (h_env : env "projectId" = some projectId)
    (h_store : store "projectId" = none) :
    (eval 4 (Env.set env "taskId" elem) store loop_body).store = store ∧
    (∀ c ∈ callsTo (eval 4 (Env.set env "taskId" elem) store loop_body).trace "db.*",
      argAt c ["where", "projectId"] = some projectId) := by
  have h_l_pid : lookup (Env.set env "taskId" elem) store "projectId" = some projectId := by
    rw [lookup_none h_store]
    simp [Env.set, show ("projectId" : String) ≠ "taskId" from by decide, h_env]
  have main : ∀ tidVal, lookup (Env.set env "taskId" elem) store "taskId" = some tidVal →
      (eval 4 (Env.set env "taskId" elem) store loop_body).store = store ∧
      (∀ c ∈ callsTo (eval 4 (Env.set env "taskId" elem) store loop_body).trace "db.*",
        argAt c ["where", "projectId"] = some projectId) := by
    intro tidVal h_l_tid
    have h_eval : eval 4 (Env.set env "taskId" elem) store loop_body =
        mkResult (.ok Val.none) store
          [.call { target := "db.task.update",
                   args := [("where", Val.obj [("id", tidVal), ("projectId", projectId)]),
                            ("data", Val.obj [("position", Val.num 0)])],
                   resultId := "__void_0" }] := by
      rw [show (4:Nat) = 3+1 from rfl]
      simp only [loop_body]
      rw [eval_call_eq]
      rw [evalPairsAux_pure_cons
          (eval_where_arg 3 _ store tidVal projectId h_l_tid h_l_pid (by omega))]
      rw [evalPairsAux_pure_cons (eval_data_arg 3 _ store (by omega))]
      rw [evalPairsAux_nil]
      rw [show (3:Nat) = 2+1 from rfl]
      simp only [mkResult_outcome, mkResult_store, mkResult_trace, eval_none_eq,
                 List.nil_append, List.append_nil]
      rfl
    rw [h_eval]
    refine ⟨rfl, ?_⟩
    intro c hc
    have h_pat : matchesPattern "db.task.update" "db.*" = true := by native_decide
    have := mem_callsTo_singleton h_pat hc; subst this
    simp
  cases h_tid : store "taskId" with
  | none =>
    exact main elem (by rw [lookup_none h_tid]; simp [Env.set])
  | some tid =>
    exact main tid (lookup_some h_tid)

-- Step through outer eval to expose the forOf loop

private theorem eval_outer_trace (env : Env) (store : Store) (elems : List Val)
    (h_store_tasks : store "tasks" = none)
    (h_env_tasks : env "tasks" = some (Val.arr elems)) :
    (eval 6 env store reorderTasks_body).trace =
    (evalForOf 4 env store "taskId" elems loop_body []).trace := by
  have h_lookup : lookup env store "tasks" = some (Val.arr elems) := by
    rw [lookup_none h_store_tasks, h_env_tasks]
  simp only [reorderTasks_body]
  rw [show (6:Nat) = 5+1 from rfl, eval_seq_none_trace]
  rw [show (5:Nat) = 4+1 from rfl, eval_forOf_eq]
  rw [show (4:Nat) = 3+1 from rfl, eval_var_eq]
  rw [h_lookup]
  simp only [mkResult_outcome, mkResult_store, mkResult_trace]

-- Non-array tasks produces no db.* calls

private theorem non_arr_no_calls (env : Env) (store : Store) (tasks : Val)
    (h_store_tasks : store "tasks" = none)
    (h_env_tasks : env "tasks" = some tasks)
    (h_not_arr : ∀ (elems : List Val), tasks ≠ Val.arr elems) :
    callsTo (eval 6 env store reorderTasks_body).trace "db.*" = [] := by
  have h_lookup : lookup env store "tasks" = some tasks := by
    rw [lookup_none h_store_tasks, h_env_tasks]
  have h_no : ∀ elems, (eval 4 env store (.var "tasks")).outcome ≠ .ok (.arr elems) := by
    intro elems
    rw [show (4:Nat) = 3+1 from rfl, eval_var_eq, h_lookup]
    simp only [mkResult_outcome, ne_eq, Outcome.ok.injEq]
    exact h_not_arr elems
  simp only [reorderTasks_body]
  rw [show (6:Nat) = 5+1 from rfl, eval_seq_none_trace]
  rw [show (5:Nat) = 4+1 from rfl, eval_forOf_non_arr_trace h_no]
  rw [show (4:Nat) = 3+1 from rfl, eval_var_trace_nil, callsTo_nil]

theorem reorderTasks_scope_limited
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
    (h_fuel : fuel ≥ 6)
    : ∀ c ∈ callsTo (eval fuel env store reorderTasks_body).trace "db.*",
      argAt c ["where", "projectId"] = some projectId := by
  rw [eval_fuel_mono 6 reorderTasks_body (by decide) fuel h_fuel]
  intro c hc
  cases h_tasks : tasks with
  | arr elems =>
    rw [h_tasks] at h_env_tasks
    rw [eval_outer_trace env store elems h_store_tasks h_env_tasks] at hc
    have h_inv := forOf_callsTo 4 env "taskId" elems loop_body "db.*"
      (fun c => argAt c ["where", "projectId"] = some projectId)
      (fun s => s = store)
      store []
      rfl
      (fun c hc => absurd hc (List.not_mem_nil c))
      (fun elem store_i h_si =>
        h_si ▸ loop_body_props env store elem projectId h_env_projectId h_store_projectId)
    exact h_inv.1 c hc
  | _ =>
    have h_not_arr : ∀ (elems : List Val), tasks ≠ Val.arr elems := by
      rw [h_tasks]; intro elems; exact Val.noConfusion
    rw [non_arr_no_calls env store tasks h_store_tasks h_env_tasks h_not_arr] at hc
    exact absurd hc (List.not_mem_nil c)
