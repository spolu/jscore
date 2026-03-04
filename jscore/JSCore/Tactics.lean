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

namespace JSCore

-- trace_simp: unfold eval definitions and simplify
macro "trace_simp" : tactic =>
  `(tactic| (
    simp only [eval, evalBinOp, evalUnOp, evalForOf, evalWhileAux,
               mkResult, lookup, Env.set, Store.set, fieldLookup, fieldSet,
               emptyEnv, emptyStore, matchesPattern, matchesPattern.go,
               callsTo, extractCalls,
               argLookup, argAtPath,
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
               matchesPat, matchesPat.go,
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
