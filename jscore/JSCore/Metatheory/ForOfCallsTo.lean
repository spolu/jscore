/-
  JSCore₀ Metatheory — ForOf CallsTo Infrastructure.

  callsTo-flavored corollaries of the generic loop invariant. Since eval's
  forOf case computes `evalForOf` definitionally (both delegate to
  `evalForOfAux`), these lemmas apply directly to eval output — the historical
  foldl-vs-explicit-recursion break mismatch is gone.
-/
import JSCore.Eval
import JSCore.Metatheory.EvalEq
import JSCore.Metatheory.TraceComposition
import JSCore.Metatheory.LoopInvariant

namespace JSCore

/-- Main invariant: a per-call property P (guarded by store invariant I) is
    preserved across forOf iterations. Use after `rw [eval_forOf_eq]` exposes
    `evalForOf` in the goal. -/
theorem forOf_callsTo (fuel : Nat) (env : Env)
    (x : String) (elems : List Val) (body : Expr) (pattern : List String)
    (P : CallRecord → Prop) (I : Store → Prop)
    (store : Store) (pfx : List TraceEntry)
    (h_I : I store)
    (h_pfx : ∀ c ∈ callsTo pfx pattern, P c)
    (h_step : ∀ elem store_i, I store_i →
      let r := eval fuel (env.set x elem) store_i body
      I r.store ∧ ∀ c ∈ callsTo r.trace pattern, P c) :
    (∀ c ∈ callsTo (evalForOf fuel env store x elems body pfx).trace pattern, P c) ∧
    I (evalForOf fuel env store x elems body pfx).store := by
  simp only [evalForOf]
  have h := evalForOfAux_invariant
    (fun elem st => eval fuel (env.set x elem) st body)
    (fun e => ∀ cr, e = TraceEntry.call cr →
      matchesPattern cr.target pattern = true → P cr)
    I
    (fun elem store_i hI => by
      obtain ⟨hI', hP⟩ := h_step elem store_i hI
      refine ⟨hI', ?_⟩
      intro e he cr hcr hm
      subst hcr
      exact hP cr (mem_callsTo.mpr ⟨he, hm⟩))
    elems store pfx h_I
    (fun e he cr hcr hm => by
      subst hcr
      exact h_pfx cr (mem_callsTo.mpr ⟨he, hm⟩))
  obtain ⟨hP, hI'⟩ := h
  refine ⟨?_, hI'⟩
  intro c hc
  obtain ⟨hmem, hpat⟩ := mem_callsTo.mp hc
  exact hP _ hmem c rfl hpat

/-- Non-array case: forOf trace equals array expr trace (no loop iterations run). -/
theorem eval_forOf_non_arr_trace {n : Nat} {env : Env} {store : Store}
    {x : String} {arrExpr body : Expr}
    (h : ∀ elems, (eval n env store arrExpr).outcome ≠ .ok (.arr elems)) :
    (eval (n + 1) env store (.forOf x arrExpr body)).trace =
    (eval n env store arrExpr).trace := by
  rw [eval_forOf_eq]
  generalize eval n env store arrExpr = ra at h ⊢
  cases h_out : ra.outcome with
  | ok v =>
    cases v with
    | arr elems => exact absurd h_out (h elems)
    | str _ => simp [h_out, mkResult]
    | num _ => simp [h_out, mkResult]
    | bool _ => simp [h_out, mkResult]
    | none => simp [h_out, mkResult]
    | obj _ => simp [h_out, mkResult]
  | error _ => simp [h_out]
  | brk => simp [h_out]
  | returned _ => simp [h_out]

end JSCore
