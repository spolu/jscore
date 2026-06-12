/-
  JSCore₀ Metatheory — Loop Invariant.
  Generic invariant principle for evalForOfAux, plus the eval-specific
  forOf_invariant corollaries. Since eval's forOf case computes evalForOf
  definitionally, these apply directly to eval output.
-/
import JSCore.Eval
import JSCore.Metatheory.EvalEq

namespace JSCore

/-- Generic loop invariant: a store invariant `I` plus a per-iteration
    trace-entry property `P` propagate through `evalForOfAux`, regardless of
    whether the loop runs to completion, breaks, returns, or errors. -/
theorem evalForOfAux_invariant (evalBody : Val → Store → Result)
    (P : TraceEntry → Prop) (I : Store → Prop)
    (h_step : ∀ elem store_i, I store_i →
      I (evalBody elem store_i).store ∧ ∀ e ∈ (evalBody elem store_i).trace, P e)
    (elems : List Val) (store : Store) (pfx : List TraceEntry)
    (h_I : I store) (h_pfx : ∀ e ∈ pfx, P e) :
    (∀ e ∈ (evalForOfAux evalBody elems store pfx).trace, P e) ∧
    I (evalForOfAux evalBody elems store pfx).store := by
  induction elems generalizing store pfx with
  | nil => exact ⟨h_pfx, h_I⟩
  | cons hd tl ih =>
    obtain ⟨h_I', h_P'⟩ := h_step hd store h_I
    have h_pfx' : ∀ e ∈ pfx ++ (evalBody hd store).trace, P e := by
      intro e he
      rw [List.mem_append] at he
      cases he with
      | inl h => exact h_pfx e h
      | inr h => exact h_P' e h
    cases h_out : (evalBody hd store).outcome with
    | ok v =>
      simp only [evalForOfAux_cons, h_out]
      exact ih _ _ h_I' h_pfx'
    | brk =>
      simp only [evalForOfAux_cons, h_out, mkResult]
      exact ⟨h_pfx', h_I'⟩
    | returned v =>
      simp only [evalForOfAux_cons, h_out, mkResult]
      exact ⟨h_pfx', h_I'⟩
    | error e =>
      simp only [evalForOfAux_cons, h_out, mkResult]
      exact ⟨h_pfx', h_I'⟩

-- The main loop invariant theorem (eval-specific corollary).
theorem forOf_invariant (fuel : Nat) (env : Env) (store : Store)
    (x : String) (elems : List Val) (body : Expr)
    (P : TraceEntry → Prop) (I : Store → Prop)
    (pfx : List TraceEntry)
    (h_pfx : ∀ e ∈ pfx, P e)
    (h_init : I store)
    (h_step : ∀ elem store_i, I store_i →
      let r := eval fuel (env.set x elem) store_i body
      I r.store ∧ ∀ e ∈ r.trace, P e) :
    let result := evalForOf fuel env store x elems body pfx
    (∀ e ∈ result.trace, P e) ∧ I result.store := by
  simp only [evalForOf]
  exact evalForOfAux_invariant _ P I (fun elem st hI => h_step elem st hI)
    elems store pfx h_init h_pfx

-- Convenience version with empty prefix
theorem forOf_invariant' (fuel : Nat) (env : Env) (store : Store)
    (x : String) (elems : List Val) (body : Expr)
    (P : TraceEntry → Prop) (I : Store → Prop)
    (h_init : I store)
    (h_step : ∀ elem store_i, I store_i →
      let r := eval fuel (env.set x elem) store_i body
      I r.store ∧ ∀ e ∈ r.trace, P e) :
    let result := evalForOf fuel env store x elems body []
    (∀ e ∈ result.trace, P e) ∧ I result.store :=
  forOf_invariant fuel env store x elems body P I [] (fun _ h => absurd h (List.not_mem_nil _))
    h_init h_step

end JSCore
