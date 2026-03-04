/-
  JSCore₀ Metatheory — Eval Equation Lemmas.
  Single-step unfolding of eval for each Expr constructor.
  These avoid recursive unfolding (which causes timeouts) by using rfl proofs.
-/
import JSCore.Eval

namespace JSCore

-- mkResult field access
theorem mkResult_outcome {o : Outcome} {s : Store} {t : List TraceEntry} :
    (mkResult o s t).outcome = o := rfl
theorem mkResult_store {o : Outcome} {s : Store} {t : List TraceEntry} :
    (mkResult o s t).store = s := rfl
theorem mkResult_trace {o : Outcome} {s : Store} {t : List TraceEntry} :
    (mkResult o s t).trace = t := rfl

-- lookup reduction
theorem lookup_none {env : Env} {store : Store} {x : String}
    (h : store x = none) : lookup env store x = env x := by
  unfold lookup; rw [h]; rfl

theorem lookup_some {env : Env} {store : Store} {x : String} {v : Val}
    (h : store x = some v) : lookup env store x = some v := by
  unfold lookup; rw [h]; rfl

-- eval equation lemmas (single-step, no recursive unfolding)

theorem eval_var_eq {n : Nat} {env : Env} {store : Store} {x : String} :
    eval (n + 1) env store (Expr.var x) =
    (match lookup env store x with
     | some v => mkResult (.ok v) store []
     | Option.none => mkResult (.error (.str s!"undefined variable: {x}")) store []) := rfl

theorem eval_strLit_eq {n : Nat} {env : Env} {store : Store} {s : String} :
    eval (n + 1) env store (Expr.strLit s) = mkResult (.ok (.str s)) store [] := rfl

theorem eval_numLit_eq {n : Nat} {env : Env} {store : Store} {i : Int} :
    eval (n + 1) env store (Expr.numLit i) = mkResult (.ok (.num i)) store [] := rfl

theorem eval_boolLit_eq {n : Nat} {env : Env} {store : Store} {b : Bool} :
    eval (n + 1) env store (Expr.boolLit b) = mkResult (.ok (.bool b)) store [] := rfl

theorem eval_none_eq {n : Nat} {env : Env} {store : Store} :
    eval (n + 1) env store Expr.none = mkResult (.ok .none) store [] := rfl

theorem eval_seq_eq {n : Nat} {env : Env} {store : Store} {e1 e2 : Expr} :
    eval (n + 1) env store (Expr.seq e1 e2) =
    (let r1 := eval n env store e1
     match r1.outcome with
     | .ok _ => let r2 := eval n env r1.store e2
                mkResult r2.outcome r2.store (r1.trace ++ r2.trace)
     | _ => r1) := rfl

theorem eval_letConst_eq {n : Nat} {env : Env} {store : Store}
    {x : String} {e body : Expr} :
    eval (n + 1) env store (Expr.letConst x e body) =
    (let r1 := eval n env store e
     match r1.outcome with
     | .ok v => let r2 := eval n (env.set x v) r1.store body
                mkResult r2.outcome r2.store (r1.trace ++ r2.trace)
     | _ => r1) := rfl

theorem eval_letMut_eq {n : Nat} {env : Env} {store : Store}
    {x : String} {e body : Expr} :
    eval (n + 1) env store (Expr.letMut x e body) =
    (let r1 := eval n env store e
     match r1.outcome with
     | .ok v => let r2 := eval n env (r1.store.set x v) body
                mkResult r2.outcome r2.store (r1.trace ++ r2.trace)
     | _ => r1) := rfl

theorem eval_assign_eq {n : Nat} {env : Env} {store : Store}
    {x : String} {e body : Expr} :
    eval (n + 1) env store (Expr.assign x e body) =
    (let r1 := eval n env store e
     match r1.outcome with
     | .ok v => let r2 := eval n env (r1.store.set x v) body
                mkResult r2.outcome r2.store (r1.trace ++ r2.trace)
     | _ => r1) := rfl

theorem eval_ite_eq {n : Nat} {env : Env} {store : Store}
    {cond thn els : Expr} :
    eval (n + 1) env store (Expr.ite cond thn els) =
    (let rc := eval n env store cond
     match rc.outcome with
     | .ok (.bool true) =>
       let r := eval n env rc.store thn
       mkResult r.outcome r.store (rc.trace ++ r.trace)
     | .ok (.bool false) =>
       let r := eval n env rc.store els
       mkResult r.outcome r.store (rc.trace ++ r.trace)
     | .ok _ => mkResult (.error (.str "if condition not boolean")) rc.store rc.trace
     | _ => rc) := rfl

theorem eval_forOf_eq {n : Nat} {env : Env} {store : Store}
    {x : String} {arrExpr body : Expr} :
    eval (n + 1) env store (Expr.forOf x arrExpr body) =
    (let ra := eval n env store arrExpr
     match ra.outcome with
     | .ok (.arr elems) =>
       elems.foldl (fun (acc : Result) (elem : Val) =>
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

theorem eval_call_eq {n : Nat} {env : Env} {store : Store}
    {target : String} {argExprs : List (String × Expr)}
    {resultBinder : String} {body : Expr} :
    eval (n + 1) env store (Expr.call target argExprs resultBinder body) =
    (let argResult := argExprs.foldl (fun (acc : List (String × Val) × Store × List TraceEntry)
        (pair : String × Expr) =>
      let (vals, curStore, curTrace) := acc
      let r := eval n env curStore pair.2
      match r.outcome with
      | .ok v => (vals ++ [(pair.1, v)], r.store, curTrace ++ r.trace)
      | _ => (vals, r.store, curTrace ++ r.trace)
    ) ([], store, [])
    let (argVals, argStore, argTrace) := argResult
    let cr : CallRecord := { target := target, args := argVals, resultId := resultBinder }
    let callTrace := argTrace ++ [.call cr]
    let resultVal := Val.none
    let r := eval n (env.set resultBinder resultVal) argStore body
    mkResult r.outcome r.store (callTrace ++ r.trace)) := rfl

theorem eval_ret_eq {n : Nat} {env : Env} {store : Store} {e : Expr} :
    eval (n + 1) env store (Expr.ret e) =
    (let r := eval n env store e
     match r.outcome with
     | .ok v => mkResult (.returned v) r.store r.trace
     | _ => r) := rfl

theorem eval_field_eq {n : Nat} {env : Env} {store : Store}
    {e : Expr} {fname : String} :
    eval (n + 1) env store (Expr.field e fname) =
    (let r := eval n env store e
     match r.outcome with
     | .ok (.obj fields) =>
       match fieldLookup fields fname with
       | some v => mkResult (.ok v) r.store r.trace
       | Option.none => mkResult (.ok .none) r.store r.trace
     | .ok _ => mkResult (.ok .none) r.store r.trace
     | _ => r) := rfl

theorem eval_obj_eq {n : Nat} {env : Env} {store : Store} {pairs : List (String × Expr)} :
    eval (n + 1) env store (.obj pairs) =
    (let result := pairs.foldl (fun (acc : List (String × Val) × Store × List TraceEntry)
        (pair : String × Expr) =>
      let (vals, curStore, curTrace) := acc
      let r := eval n env curStore pair.2
      match r.outcome with
      | .ok v => (vals ++ [(pair.1, v)], r.store, curTrace ++ r.trace)
      | _ => (vals, r.store, curTrace ++ r.trace)
    ) ([], store, [])
    mkResult (.ok (.obj result.1)) result.2.1 result.2.2) := rfl

theorem eval_binOp_eq {n : Nat} {env : Env} {store : Store}
    {op : BinOp} {e1 e2 : Expr} :
    eval (n + 1) env store (Expr.binOp op e1 e2) =
    (let r1 := eval n env store e1
     match r1.outcome with
     | .ok v1 =>
       let r2 := eval n env r1.store e2
       match r2.outcome with
       | .ok v2 => mkResult (evalBinOp op v1 v2) r2.store (r1.trace ++ r2.trace)
       | _ => r2
     | _ => r1) := rfl

theorem eval_break_eq {n : Nat} {env : Env} {store : Store} :
    eval (n + 1) env store Expr.«break» = mkResult .brk store [] := rfl

theorem eval_throw_eq {n : Nat} {env : Env} {store : Store} {e : Expr} :
    eval (n + 1) env store (Expr.throw e) =
    (let r := eval n env store e
     match r.outcome with
     | .ok v => mkResult (.error v) r.store r.trace
     | _ => r) := rfl

theorem eval_tryCatch_eq {n : Nat} {env : Env} {store : Store}
    {body : Expr} {errName : String} {handler : Expr} :
    eval (n + 1) env store (Expr.tryCatch body errName handler) =
    (let rb := eval n env store body
     match rb.outcome with
     | .error v =>
       let rh := eval n (env.set errName v) rb.store handler
       mkResult rh.outcome rh.store (rb.trace ++ rh.trace)
     | _ => rb) := rfl

-- Derived property: Expr.none always produces empty trace regardless of fuel

theorem eval_none_trace {n : Nat} {env : Env} {store : Store} :
    (eval n env store Expr.none).trace = [] := by
  cases n with
  | zero => rfl
  | succ n => rw [eval_none_eq]; rfl

-- Derived property: seq with Expr.none tail has same trace as first expr

theorem eval_seq_none_trace {n : Nat} {env : Env} {store : Store} {e : Expr} :
    (eval (n + 1) env store (Expr.seq e Expr.none)).trace =
    (eval n env store e).trace := by
  rw [eval_seq_eq]
  generalize eval n env store e = r1
  cases r1 with
  | mk outcome s t =>
    cases outcome with
    | ok v =>
      simp only [mkResult_outcome, mkResult_store, mkResult_trace]
      rw [eval_none_trace]; simp
    | error _ => rfl
    | brk => rfl
    | returned _ => rfl

-- Derived properties: var eval produces empty trace and preserves store

theorem eval_var_trace_nil {n : Nat} {env : Env} {store : Store} {x : String} :
    (eval (n + 1) env store (Expr.var x)).trace = [] := by
  rw [eval_var_eq]; cases lookup env store x <;> rfl

theorem eval_var_store_eq {n : Nat} {env : Env} {store : Store} {x : String} :
    (eval (n + 1) env store (Expr.var x)).store = store := by
  rw [eval_var_eq]; cases lookup env store x <;> rfl

-- Derived property: ret preserves inner trace

theorem eval_ret_trace {n : Nat} {env : Env} {store : Store} {e : Expr} :
    (eval (n + 1) env store (.ret e)).trace = (eval n env store e).trace := by
  rw [eval_ret_eq]
  cases eval n env store e with
  | mk outcome s t =>
    cases outcome with
    | ok v => simp [mkResult]
    | error _ => rfl
    | brk => rfl
    | returned _ => rfl

-- Derived property: field access on an env-bound object variable

theorem eval_field_var {n : Nat} {env : Env} {store : Store}
    {x : String} {fields : List (String × Val)} {fname : String} {v : Val}
    (h_env : env x = some (Val.obj fields))
    (h_store : store x = none)
    (h_fl : fieldLookup fields fname = some v)
    (hn : n ≥ 2) :
    eval n env store (.field (.var x) fname) = mkResult (.ok v) store [] := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
  rw [show n' + 2 = (n' + 1) + 1 from by omega, eval_field_eq]
  rw [show n' + 1 = n' + 1 from rfl, eval_var_eq]
  rw [lookup_none h_store, h_env]
  simp only [mkResult_outcome, mkResult_store, mkResult_trace, h_fl]

end JSCore
