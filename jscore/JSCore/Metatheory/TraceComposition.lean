/-
  JSCore₀ Metatheory — Trace Composition.
  Trace of seq/letConst/letMut = trace of subexpressions concatenated.
-/
import JSCore.Eval

namespace JSCore

theorem seq_trace (fuel : Nat) (env : Env) (store : Store) (e1 e2 : Expr) :
    (eval (fuel + 1) env store (.seq e1 e2)).trace =
      match (eval fuel env store e1).outcome with
      | .ok _ => (eval fuel env store e1).trace ++ (eval fuel env (eval fuel env store e1).store e2).trace
      | _ => (eval fuel env store e1).trace := by
  simp only [eval]
  generalize (eval fuel env store e1) = r1
  match r1.outcome with
  | .ok v => simp [mkResult]
  | .error _ => simp [mkResult, Result.trace]
  | .brk => simp [mkResult, Result.trace]
  | .returned _ => simp [mkResult, Result.trace]

theorem letConst_trace (fuel : Nat) (env : Env) (store : Store) (x : String) (e body : Expr) :
    (eval (fuel + 1) env store (.letConst x e body)).trace =
      match (eval fuel env store e).outcome with
      | .ok v => (eval fuel env store e).trace ++
          (eval fuel (env.set x v) (eval fuel env store e).store body).trace
      | _ => (eval fuel env store e).trace := by
  simp only [eval]
  generalize (eval fuel env store e) = r1
  match r1.outcome with
  | .ok v => simp [mkResult]
  | .error _ => simp [mkResult, Result.trace]
  | .brk => simp [mkResult, Result.trace]
  | .returned _ => simp [mkResult, Result.trace]

-- Calls-to preserves over trace concatenation
theorem callsTo_append (t1 t2 : List TraceEntry) (pattern : String) :
    callsTo (t1 ++ t2) pattern = callsTo t1 pattern ++ callsTo t2 pattern := by
  simp [callsTo, extractCalls, List.filterMap_append, List.filter_append]

-- If P holds for all calls in t1 and t2, it holds for all calls in t1 ++ t2
theorem forall_calls_append (t1 t2 : List TraceEntry) (pattern : String)
    (P : CallRecord → Prop)
    (h1 : ∀ c ∈ callsTo t1 pattern, P c)
    (h2 : ∀ c ∈ callsTo t2 pattern, P c) :
    ∀ c ∈ callsTo (t1 ++ t2) pattern, P c := by
  rw [callsTo_append]
  intro c hc
  rw [List.mem_append] at hc
  cases hc with
  | inl h => exact h1 c h
  | inr h => exact h2 c h

-- extractCalls preserves over trace concatenation
theorem extractCalls_append (t1 t2 : List TraceEntry) :
    extractCalls (t1 ++ t2) = extractCalls t1 ++ extractCalls t2 := by
  simp [extractCalls, List.filterMap_append]

-- If P holds for all extracted calls in t1 and t2, it holds in t1 ++ t2
theorem forall_extractCalls_append (t1 t2 : List TraceEntry)
    (P : CallRecord → Prop)
    (h1 : ∀ c ∈ extractCalls t1, P c)
    (h2 : ∀ c ∈ extractCalls t2, P c) :
    ∀ c ∈ extractCalls (t1 ++ t2), P c := by
  rw [extractCalls_append]
  intro c hc
  rw [List.mem_append] at hc
  cases hc with
  | inl h => exact h1 c h
  | inr h => exact h2 c h

-- callsTo on empty trace is empty
theorem callsTo_nil (pattern : String) :
    callsTo [] pattern = [] := rfl

-- callsTo on a single matching .call entry is a singleton
theorem callsTo_singleton_call {cr : CallRecord} {pattern : String}
    (h : matchesPattern cr.target pattern = true) :
    callsTo [TraceEntry.call cr] pattern = [cr] := by
  simp [callsTo, extractCalls, List.filterMap, List.filter, h]

-- c ∈ callsTo [.call cr] pattern implies c = cr (when pattern matches)
theorem mem_callsTo_singleton {cr : CallRecord} {pattern : String} {c : CallRecord}
    (h_pat : matchesPattern cr.target pattern = true)
    (h_mem : c ∈ callsTo [TraceEntry.call cr] pattern) :
    c = cr := by
  rw [callsTo_singleton_call h_pat] at h_mem
  simp [List.mem_cons, List.mem_nil_iff] at h_mem
  exact h_mem

end JSCore
