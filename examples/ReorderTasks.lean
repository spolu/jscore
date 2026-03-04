import JSCore.Syntax
import JSCore.Values
import JSCore.Eval
import JSCore.Trace
import JSCore.Properties
import JSCore.Taint
import JSCore.Tactics
import JSCore.Metatheory.TraceComposition
import JSCore.Metatheory.LoopInvariant

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

-- Lookup reduction lemmas
theorem lookup_none {env : Env} {store : Store} {x : String} (h : store x = none) :
    lookup env store x = env x := by unfold lookup; rw [h]; rfl

theorem lookup_some {env : Env} {store : Store} {x : String} {v : Val}
    (h : store x = some v) : lookup env store x = some v := by
  unfold lookup; rw [h]; rfl

-- mkResult field access lemmas (targeted, avoids expanding mkResult everywhere)
private theorem mkResult_outcome {o : Outcome} {s : Store} {t : List TraceEntry} :
    (mkResult o s t).outcome = o := rfl
private theorem mkResult_store {o : Outcome} {s : Store} {t : List TraceEntry} :
    (mkResult o s t).store = s := rfl
private theorem mkResult_trace {o : Outcome} {s : Store} {t : List TraceEntry} :
    (mkResult o s t).trace = t := rfl

-- Equation lemmas for eval (single-step, no recursive unfolding)
private theorem eval_seq_eq {n : Nat} {env : Env} {store : Store} {e1 e2 : Expr} :
    eval (n + 1) env store (Expr.seq e1 e2) =
    (let r1 := eval n env store e1
     match r1.outcome with
     | .ok _ => let r2 := eval n env r1.store e2
                mkResult r2.outcome r2.store (r1.trace ++ r2.trace)
     | _ => r1) := rfl

private theorem eval_forOf_eq {n : Nat} {env : Env} {store : Store}
    {x : String} {arrExpr body : Expr} :
    eval (n + 1) env store (Expr.forOf x arrExpr body) =
    (let ra := eval n env store arrExpr
     match ra.outcome with
     | .ok (.arr elems) =>
       elems.foldl (fun (acc : Result) elem =>
         match acc.outcome with
         | .ok _ =>
           let r := eval n (env.set x elem) acc.store body
           match r.outcome with
           | .brk => mkResult (.ok .none) r.store (acc.trace ++ r.trace)
           | .returned v => mkResult (.returned v) r.store (acc.trace ++ r.trace)
           | _ => mkResult r.outcome r.store (acc.trace ++ r.trace)
         | _ => acc
       ) (mkResult (.ok .none) ra.store ra.trace)
     | .ok _ => mkResult (.error (.str "forOf on non-array")) ra.store ra.trace
     | _ => ra) := rfl

private theorem eval_var_eq {n : Nat} {env : Env} {store : Store} {x : String} :
    eval (n + 1) env store (Expr.var x) =
    (match lookup env store x with
     | some v => mkResult (.ok v) store []
     | Option.none => mkResult (.error (.str s!"undefined variable: {x}")) store []) := rfl

private theorem eval_none_eq {n : Nat} {env : Env} {store : Store} :
    eval (n + 1) env store Expr.none = mkResult (.ok .none) store [] := rfl

-- The foldl step function
def forOfStep (env : Env) (body : Expr) (acc : Result) (elem : Val) : Result :=
  match acc.outcome with
  | .ok _ =>
    let r := eval 4 (Env.set env "taskId" elem) acc.store body
    match r.outcome with
    | .brk => mkResult (.ok .none) r.store (acc.trace ++ r.trace)
    | .returned v => mkResult (.returned v) r.store (acc.trace ++ r.trace)
    | _ => mkResult r.outcome r.store (acc.trace ++ r.trace)
  | _ => acc

theorem foldl_eq (env : Env) (elems : List Val) (acc : Result) :
    elems.foldl (fun (acc : Result) (elem : Val) =>
      match acc.outcome with
      | .ok _ =>
        let r := eval 4 (Env.set env "taskId" elem) acc.store loop_body
        match r.outcome with
        | .brk => mkResult (.ok .none) r.store (acc.trace ++ r.trace)
        | .returned v => mkResult (.returned v) r.store (acc.trace ++ r.trace)
        | _ => mkResult r.outcome r.store (acc.trace ++ r.trace)
      | _ => acc
    ) acc = elems.foldl (forOfStep env loop_body) acc := rfl

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

-- Helper: single iteration properties
theorem loop_body_props (env : Env) (store : Store) (elem projectId : Val)
    (h_env : env "projectId" = some projectId)
    (h_store : store "projectId" = none) :
    let r := eval 4 (Env.set env "taskId" elem) store loop_body
    r.store = store ∧
    (∃ v, r.outcome = .ok v) ∧
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
    refine ⟨trivial, ⟨.none, rfl⟩, ?_⟩
    intro c hc
    have h_pat : matchesPattern "db.task.update" "db.*" = true := by native_decide
    simp only [callsTo, extractCalls, List.filterMap, List.filter, h_pat,
      List.mem_cons, List.mem_nil_iff, or_false, ite_true, ite_false,
      decide_true, decide_false, Bool.true_and, Bool.and_true] at hc
    subst hc
    simp only [List.cons_append, List.nil_append, List.append_nil]
    exact argAtPath_where_pid elem projectId
  | some tid =>
    have h_l_tid : lookup (Env.set env "taskId" elem) store "taskId" = some tid := by
      rw [lookup_some h_tid]
    have h_l_pid : lookup (Env.set env "taskId" elem) store "projectId" = some projectId := by
      rw [lookup_none h_store]
      simp [Env.set, show ("projectId" : String) ≠ "taskId" from by decide, h_env]
    simp only [loop_body, eval, mkResult, Env.set, List.foldl,
      List.append, List.nil_append, List.append_nil, h_l_tid, h_l_pid]
    refine ⟨trivial, ⟨.none, rfl⟩, ?_⟩
    intro c hc
    have h_pat : matchesPattern "db.task.update" "db.*" = true := by native_decide
    simp only [callsTo, extractCalls, List.filterMap, List.filter, h_pat,
      List.mem_cons, List.mem_nil_iff, or_false, ite_true, ite_false,
      decide_true, decide_false, Bool.true_and, Bool.and_true] at hc
    subst hc
    simp only [List.cons_append, List.nil_append, List.append_nil]
    exact argAtPath_where_pid tid projectId

-- Foldl invariant
theorem foldl_invariant (env : Env) (store : Store) (projectId : Val)
    (elems : List Val) (acc : Result)
    (h_env : env "projectId" = some projectId)
    (h_store : store "projectId" = none)
    (h_acc_ok : ∃ v, acc.outcome = .ok v)
    (h_acc_store : acc.store = store)
    (h_acc_calls : ∀ c ∈ callsTo acc.trace "db.*",
      argAtPath c "where.projectId" = some projectId) :
    ∀ c ∈ callsTo (elems.foldl (forOfStep env loop_body) acc).trace "db.*",
      argAtPath c "where.projectId" = some projectId := by
  induction elems generalizing acc with
  | nil => simpa [List.foldl] using h_acc_calls
  | cons hd tl ih =>
    simp only [List.foldl, forOfStep]
    obtain ⟨v, hv⟩ := h_acc_ok
    simp only [hv]
    -- Rewrite acc.store → store in the eval call
    rw [h_acc_store]
    have h_props := loop_body_props env store hd projectId h_env h_store
    obtain ⟨h_store_eq, ⟨v', hv'⟩, h_calls⟩ := h_props
    simp only [hv']
    apply ih
    · exact ⟨v', by simp [mkResult]⟩
    · simp only [mkResult]; exact h_store_eq
    · intro c hc
      simp only [mkResult] at hc
      rw [callsTo_append] at hc
      rw [List.mem_append] at hc
      cases hc with
      | inl h => exact h_acc_calls c h
      | inr h => exact h_calls c h

-- Helper: the outer eval trace for the arr case
-- Uses equation lemmas instead of `simp only [eval]` to avoid timeout
theorem eval_outer_trace (env : Env) (store : Store) (elems : List Val)
    (h_store_tasks : store "tasks" = none)
    (h_env_tasks : env "tasks" = some (Val.arr elems)) :
    callsTo (eval 6 env store reorderTasks_body).trace "db.*" =
    callsTo (elems.foldl (fun (acc : Result) (elem : Val) =>
      match acc.outcome with
      | .ok _ =>
        let r := eval 4 (Env.set env "taskId" elem) acc.store loop_body
        match r.outcome with
        | .brk => mkResult (.ok .none) r.store (acc.trace ++ r.trace)
        | .returned v => mkResult (.returned v) r.store (acc.trace ++ r.trace)
        | _ => mkResult r.outcome r.store (acc.trace ++ r.trace)
      | _ => acc
    ) (mkResult (.ok Val.none) store [])).trace "db.*" := by
  have h_lookup : lookup env store "tasks" = some (Val.arr elems) := by
    rw [lookup_none h_store_tasks, h_env_tasks]
  -- Step through eval using equation lemmas (targeted, no recursive unfolding)
  simp only [reorderTasks_body]
  rw [show (6 : Nat) = 5 + 1 from rfl, eval_seq_eq]
  rw [show (5 : Nat) = 4 + 1 from rfl, eval_forOf_eq]
  rw [show (4 : Nat) = 3 + 1 from rfl, eval_var_eq]
  rw [h_lookup]
  -- Reduce mkResult field accesses and iota-reduce matches on concrete constructors
  simp only [mkResult_outcome, mkResult_store, mkResult_trace, List.nil_append, List.append_nil]
  -- Now the seq outer match has eval_none in the .ok branch
  -- Reduce eval on .none
  rw [eval_none_eq]
  -- Simplify mkResult fields and List.append_nil
  simp only [mkResult_outcome, mkResult_store, mkResult_trace, List.append_nil]
  -- Now both branches of the seq match give the same callsTo
  -- The .ok branch: callsTo r1.trace "db.*"
  -- The _ branch: callsTo r1.trace "db.*"
  -- Split on the outcome to close
  generalize elems.foldl _ _ = r
  cases r with
  | mk outcome store' trace' =>
    cases outcome with
    | ok v => simp [mkResult_trace]
    | error v => rfl
    | brk => rfl
    | returned v => rfl

-- Helper: non-array tasks produces no db.* calls
theorem eval_non_arr_no_calls (env : Env) (store : Store) (tasks : Val)
    (h_store_tasks : store "tasks" = none)
    (h_env_tasks : env "tasks" = some tasks)
    (h_not_arr : ∀ (elems : List Val), tasks ≠ Val.arr elems) :
    callsTo (eval 6 env store reorderTasks_body).trace "db.*" = [] := by
  have h_lookup : lookup env store "tasks" = some tasks := by
    rw [lookup_none h_store_tasks, h_env_tasks]
  simp only [reorderTasks_body]
  rw [show (6 : Nat) = 5 + 1 from rfl, eval_seq_eq]
  rw [show (5 : Nat) = 4 + 1 from rfl, eval_forOf_eq]
  rw [show (4 : Nat) = 3 + 1 from rfl, eval_var_eq]
  rw [h_lookup]
  simp only [mkResult_outcome, mkResult_store, mkResult_trace, List.nil_append, List.append_nil]
  -- Case split on tasks to resolve the forOf match
  cases tasks with
  | arr elems => exact absurd rfl (h_not_arr elems)
  | str s =>
    -- forOf on non-array: .ok (.str s) matches .ok _ (second forOf branch)
    -- Result has error outcome, seq catch-all returns it directly
    simp only [eval_none_eq, mkResult_outcome, mkResult_store, mkResult_trace,
      List.append_nil, callsTo_append,
      callsTo, extractCalls, List.filterMap, List.filter, List.nil_append]
  | num n =>
    simp only [eval_none_eq, mkResult_outcome, mkResult_store, mkResult_trace,
      List.append_nil, callsTo_append,
      callsTo, extractCalls, List.filterMap, List.filter, List.nil_append]
  | bool b =>
    simp only [eval_none_eq, mkResult_outcome, mkResult_store, mkResult_trace,
      List.append_nil, callsTo_append,
      callsTo, extractCalls, List.filterMap, List.filter, List.nil_append]
  | none =>
    simp only [eval_none_eq, mkResult_outcome, mkResult_store, mkResult_trace,
      List.append_nil, callsTo_append,
      callsTo, extractCalls, List.filterMap, List.filter, List.nil_append]
  | obj fs =>
    simp only [eval_none_eq, mkResult_outcome, mkResult_store, mkResult_trace,
      List.append_nil, callsTo_append,
      callsTo, extractCalls, List.filterMap, List.filter, List.nil_append]

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
    rw [foldl_eq] at hc
    exact foldl_invariant env store projectId elems
      (mkResult (.ok Val.none) store [])
      h_env_projectId h_store_projectId
      ⟨.none, rfl⟩ rfl
      (fun c hc => by simp [callsTo, extractCalls, mkResult, List.filterMap, List.filter] at hc)
      c hc
  | _ =>
    have h_not_arr : ∀ (elems : List Val), tasks ≠ Val.arr elems := by
      rw [h_tasks]; intro elems; exact Val.noConfusion
    rw [eval_non_arr_no_calls env store tasks h_store_tasks h_env_tasks h_not_arr] at hc
    exact absurd hc (List.not_mem_nil c)
