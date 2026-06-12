/-
  JSCore₀ Tactics — custom tactics for closing proof goals mechanically.
-/
import JSCore.Eval
import JSCore.Taint
import JSCore.Properties
import JSCore.StringPredicates
import JSCore.Metatheory.TraceComposition
import JSCore.Metatheory.EnvStability
import JSCore.Metatheory.LoopInvariant
import JSCore.Metatheory.ConditionalCoverage
import JSCore.Metatheory.Composition
import JSCore.Metatheory.TaintSoundness
import JSCore.Metatheory.EvalEq
import JSCore.Metatheory.ArgAt

namespace JSCore

/--
`eval_step [h₁, h₂, …]` symbolically executes concrete-fuel `eval` terms in
the goal (or `at h` with a location) by repeatedly applying the single-step
equation lemmas, reducing the argument-list helpers, and rewriting with the
supplied lookup/field facts (e.g. `lookup env store "x" = some v`,
`fieldLookup fields "f" = some w`). Fuel must be a literal (use
`eval_fuel_mono` first) — numeral fuels unify with the `(n + 1)` patterns
directly. Replaces the hand-written per-example argument-evaluation lemmas.
-/
syntax "eval_step" ("[" Lean.Parser.Tactic.simpLemma,* "]")? (Lean.Parser.Tactic.location)? : tactic

macro_rules
  | `(tactic| eval_step $[$loc:location]?) =>
    `(tactic| eval_step [] $[$loc:location]?)
  | `(tactic| eval_step [$ts:simpLemma,*] $[$loc:location]?) =>
    `(tactic| simp only [
        eval_var_eq, eval_strLit_eq, eval_numLit_eq, eval_boolLit_eq,
        eval_none_eq, eval_seq_eq, eval_letConst_eq, eval_letMut_eq,
        eval_assign_eq, eval_ite_eq, eval_call_eq, eval_ret_eq,
        eval_field_eq, eval_obj_eq, eval_arr_eq, eval_spread_eq,
        eval_binOp_eq, eval_break_eq, eval_throw_eq, eval_tryCatch_eq,
        eval_index_eq, eval_push_eq, eval_unOp_eq,
        evalPairsAux_cons, evalPairsAux_nil,
        evalElemsAux_cons, evalElemsAux_nil,
        evalBinOp, evalUnOp,
        mkResult_outcome, mkResult_store, mkResult_trace,
        fieldLookup_nil, fieldLookup_cons_self, fieldLookup_cons_ne,
        argLookup_eq_fieldLookup,
        List.nil_append, List.append_nil, List.cons_append, List.singleton_append,
        $ts:simpLemma,*] $[$loc:location]?)

-- trace_simp: unfold eval definitions and simplify
macro "trace_simp" : tactic =>
  `(tactic| (
    simp only [eval, evalBinOp, evalUnOp, evalForOf, evalForOfAux, evalWhileAux,
               evalPairsAux, evalElemsAux,
               mkResult, lookup, Env.set, Store.set, fieldLookup, fieldSet,
               emptyEnv, emptyStore, matchesPattern,
               callsTo, extractCalls,
               argLookup, argAtPath, argAt, valAt,
               Val.startsWith', Val.mem', Val.contains',
               List.foldl, List.filter, List.filterMap, List.map, List.append,
               List.find?, List.any, List.all,
               Option.bind, Option.map, Option.getD,
               BEq.beq, Val.beq,
               String.startsWith, String.isPrefixOf,
               ite_true, ite_false,
               decide_true, decide_false,
               Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false,
               Bool.true_or, Bool.false_or, Bool.or_true, Bool.or_false,
               Bool.not_true, Bool.not_false]
    <;> (try rfl)
    <;> (try omega)
    <;> (try decide)))

-- by_taint: decide taint-freedom (purely syntactic)
macro "by_taint" : tactic =>
  `(tactic| (
    simp only [notTaintedIn, callExprsIn, callExprsInPairs, taintedBy, freeVars,
               freeVarsPairs, freeVarsList,
               collectTaintedBindings, collectTaintedBindingsPairs,
               controlFlowSafe, controlFlowSafePairs,
               matchesPat,
               List.all, List.any, List.flatMap, List.filter, List.map,
               List.elem, List.append, List.isEmpty,
               String.startsWith, String.isPrefixOf,
               BEq.beq, String.decEq,
               Bool.not_true, Bool.not_false,
               Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false,
               Bool.true_or, Bool.false_or, Bool.or_true, Bool.or_false,
               decide_true, decide_false]
    <;> (try rfl)
    <;> (try decide)))

-- by_ordering: for before/after properties, witness indices and close with omega
macro "by_ordering" : tactic =>
  `(tactic| (
    simp only [before, inside, List.get?]
    <;> (try omega)
    <;> (try exact ⟨_, _, rfl, rfl, by omega⟩)))

end JSCore
