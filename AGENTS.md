# AGENTS.md

This file provides guidance to AI agents (Claude Code, Codex, etc.) when working with code in this repository.

## Project Overview

JSCore₀ is a verification system: annotated TypeScript → Lean 4 proofs. Agents write code and proofs, humans review annotations (`@requires`, `@invariant`, `@ensures`), Lean kernel checks everything. See [PROPOSAL.md](PROPOSAL.md) for the full system design, motivation, and annotation semantics.

**Pipeline:** Annotated TS → extractor (ts-morph) → Lean AST + theorem statements → `lake build`

## Build Commands

### Lean library (`jscore/`)
```bash
export PATH="$HOME/.elan/bin:$PATH"
cd jscore && lake build JSCore
```
Toolchain: `leanprover/lean4:v4.16.0`. No external Lake dependencies. `autoImplicit` is disabled globally.

### Extractor (`extractor/`)
```bash
cd extractor && npx tsc                          # compile TS → dist/
node dist/index.js extract --out-dir ../examples <files...>
node dist/index.js verify  --out-dir ../examples --lean-dir ../jscore <files...>
node dist/index.js coverage --out-dir ../examples <files...>
```

### Examples (`examples/`)
A separate Lean project that depends on `jscore/`:
```bash
cd examples && lake build
```

## Architecture

### Lean Formalism (`jscore/JSCore/`)

Modules imported in dependency order by `jscore/JSCore.lean`:

- **Syntax** — `Expr` inductive (26 constructors). `call` is CPS-style: `call target args resultBinder body`. `whileLoop` carries its own fuel.
- **Values** — `Val` (str/num/bool/none/obj/arr). `Env` and `Store` are both `String → Option Val` (function types, not maps). `Env` = immutable (letConst), `Store` = mutable (letMut/assign). `lookup` checks Store then Env.
- **Trace** — `CallRecord`, `TraceEntry`, `Outcome`, `Result`. Pattern matching with `*` wildcards. `callsTo`, `before`/`inside` ordering predicates, `argAtPath` for dotted-path lookup into call args.
- **Eval** — `eval` uses global `fuel : Nat` with structural recursion. `List.foldl` used inline for obj/arr/call args/forOf to avoid mutual recursion. `evalWhileAux` is top-level (not local def) taking closures. `evalForOf` is separate top-level with explicit recursion on element list.
- **StringPredicates** — `Val.startsWith'`, `Val.mem'`, `Val.contains'` as Bool functions.
- **Properties** — `sumOver`, `indexOf`, `allCallsSatisfy`, `noCallsExist`.
- **Taint** — Purely syntactic analysis: `freeVars`, `collectTaintedBindings`, `taintedBy`, `notTaintedIn`, `callExprsIn`. `notTaintedIn` currently includes a conservative control-flow independence check (`source ∉ freeVars prog`), so it may produce false positives (reject path-safe programs) but should not miss real leaks. Three sets of mutual-recursive helpers for nested inductive traversal.
- **Metatheory/** — EvalEq, ForOfCallsTo, TraceComposition, EnvStability, LoopInvariant, ConditionalCoverage, Composition, TaintSoundness.
- **Tactics** — `trace_simp` (unfolds eval/binop/trace/string defs), `by_taint` (unfolds taint analysis), `by_ordering` (before/inside with omega).

### Extractor (`extractor/src/`)

- **ast-to-jscore.ts** — ts-morph AST → `JsCoreExpr`. Processes statements in CPS style (each statement's body is `rest()`).
- **lean-emitter.ts** — `JsCoreExpr` → Lean 4 source text. `emitLeanFileMulti` emits one file with multiple function defs + theorems.
- **lean-theorem.ts** — Annotations → Lean theorem statements. Three shapes: taint (native_decide), nonexistence (native_decide), runtime ∀ (sorry for agents).
- **annotation-parser.ts** — Parses `@requires`/`@invariant`/`@ensures` from TS comments. Multi-line via continuation lines.
- **reassignment.ts** — Determines letConst vs letMut based on reassignment analysis.
- **type-translator.ts** — TS types → Lean Val predicates.
- **proof-merge.ts** — Proof-preserving merge: when regenerating a `.lean` file, splices existing non-sorry proof bodies back into the fresh skeleton. Also preserves private helpers, abbrevs, and unions imports from both files.

### Extracted Lean file structure

One `_jscore.lean` file per `.ts` source file, named `<camelCaseBaseName>_jscore.lean` (e.g. `scopedUpdate.ts` → `scopedUpdate_jscore.lean`). Multiple annotated functions in one `.ts` file are consolidated into a single `.lean` file.

Each function produces: a `def <name>_body : Expr` with the expression tree, then theorems. Syntactic theorems (taint, nonexistence) close with `native_decide`. Runtime theorems have `sorry` for agents to fill using metatheory lemmas.

Lean outputs are generated under `examples/`, collocated with their `.ts` source files. Re-running the extractor on an existing file preserves proofs via the merge logic in `proof-merge.ts`.

## Lean 4 v4.16.0 Gotchas

- `break` is a keyword → use `Expr.«break»`, `.«break»`
- `prefix` is a keyword → don't use as variable name
- `List.bind` doesn't exist → use `List.flatMap`
- `Repr` can't derive for function types (affects `Env`/`Store`)
- `.var "name"` needs parens `(.var "name")` as sub-expression
- `Expr.none` and `Expr.«break»` for leaf forms to avoid ambiguity

## ts-morph AST Gotcha

`node.getChildren()` wraps collections in `SyntaxList` nodes. Direct children of `Block`, `VariableDeclarationList`, `ObjectLiteralExpression`, `ArrayLiteralExpression` etc. include `SyntaxList` which must be unwrapped. Use the `flatChildren()` helper in `ast-to-jscore.ts`.

## Known Sorrys

- `JSCore/Metatheory/TaintSoundness.lean` sorrys are resolved (`eval_independent_of_source` and `taint_soundness` are proved).
- All extracted runtime theorem proofs in `examples/` (intentional — agents fill these in)

## Proof Strategy for Runtime Theorems

Key tactics and lemmas for closing `sorry` in extracted files:
- `trace_simp` — fully concrete cases
- `forOf_invariant` / `forOf_invariant'` — loop invariants (work on `evalForOf`, NOT on eval's inline foldl)
- `forOfFold_callsTo` — callsTo invariant for forOf via eval's inline foldl (see below)
- `ite_covers` — if/then/else coverage
- `forall_calls_append` / `callsTo_append` / `callsTo_nil` — trace composition
- `callsTo_singleton_call` / `mem_callsTo_singleton` — singleton call trace reasoning
- `env_stable` / `notMutatedIn` — environment stability across eval
- `by_taint` — taint analysis goals
- `by_ordering` — before/inside ordering goals

### Eval Equation Lemmas (`Metatheory/EvalEq.lean`)

Single-step unfolding lemmas for each `Expr` constructor, all proved by `rfl`. These avoid recursive unfolding (which causes timeouts). Use with `rw` to step through eval one constructor at a time.

Available: `eval_var_eq`, `eval_strLit_eq`, `eval_numLit_eq`, `eval_boolLit_eq`, `eval_none_eq`, `eval_seq_eq`, `eval_letConst_eq`, `eval_letMut_eq`, `eval_assign_eq`, `eval_ite_eq`, `eval_forOf_eq`, `eval_call_eq`, `eval_ret_eq`, `eval_field_eq`, `eval_obj_eq`, `eval_break_eq`, `eval_throw_eq`, `eval_tryCatch_eq`.

Field access: `mkResult_outcome`/`mkResult_store`/`mkResult_trace`. Lookup: `lookup_none`/`lookup_some`.

Derived properties:
- `eval_var_trace_nil` / `eval_var_store_eq` — var eval produces `[]` trace and preserves store
- `eval_none_trace` — `Expr.none` produces `[]` trace for any fuel (including 0)
- `eval_seq_none_trace` — `seq e Expr.none` has same trace as `e` (strips trailing `Expr.none` in seq)
- `eval_ret_trace` — `ret e` preserves inner trace
- `eval_field_var` — `.field (.var x) fname` evaluates to `mkResult (.ok v) store []` when `x` is bound to `Val.obj fields` in env (not store) and `fieldLookup fields fname = some v`; requires fuel ≥ 2

### ForOf CallsTo Infrastructure (`Metatheory/ForOfCallsTo.lean`)

**Critical insight:** eval's forOf uses inline `List.foldl` (to avoid mutual recursion), while `evalForOf` uses explicit recursion. They differ on **break semantics**: foldl continues after break (converting to `.ok .none`), evalForOf stops. This means `forOf_invariant` (from LoopInvariant.lean) cannot be applied directly to eval output.

This module bridges the gap:
- `forOfFoldStep` — named version of eval's inline forOf lambda
- `eval_forOf_foldl_step` — proves the inline lambda equals `forOfFoldStep` (by `rfl`)
- `forOfFoldStep_ok` / `forOfFoldStep_not_ok` — case-split helpers
- `foldl_forOfFoldStep_not_ok` — foldl is identity when acc outcome is not ok
- **`forOfFold_callsTo`** — main invariant: given a store invariant `I` and a per-step property `P` on call records, proves all callsTo in the foldl result satisfy `P` and `I` is preserved
- `eval_forOf_non_arr_trace` — non-array case: forOf trace equals array expr trace

### Trace Composition (`Metatheory/TraceComposition.lean`)

- `callsTo_append` — `callsTo (t1 ++ t2) p = callsTo t1 p ++ callsTo t2 p`
- `forall_calls_append` — lifts per-trace call properties through concatenation
- `callsTo_nil` — `callsTo [] p = []`
- `callsTo_singleton_call` — `callsTo [.call cr] p = [cr]` when `matchesPattern cr.target p = true`
- `mem_callsTo_singleton` — `c ∈ callsTo [.call cr] p → c = cr` (combines singleton + membership). Use as: `have := mem_callsTo_singleton (by native_decide) hc; subst this`

**Note:** When using `native_decide` for `matchesPattern`, the goal must not contain free variables. Bind the `matchesPattern` proof in a separate `have` first.

### Proof Pattern: Stepping Through forOf with `seq _ Expr.none`

Many extracted bodies have the form `seq (forOf x arr body) Expr.none`. The recommended proof pattern:

1. **Strip the seq wrapper:** `rw [show (n:Nat) = m+1 from rfl, eval_seq_none_trace]` — reduces to just the forOf eval's trace
2. **Unfold forOf:** `rw [eval_forOf_eq]` then `rw [eval_var_eq]` + `rw [h_lookup]` to resolve the array
3. **Simplify:** `simp only [mkResult_outcome, mkResult_store, mkResult_trace, List.nil_append, List.append_nil]`
4. **Close with `rfl`:** The inline foldl lambda from `eval_forOf_eq` is definitionally equal to `forOfFoldStep`, so if the conclusion uses `forOfFoldStep`, `rfl` closes the goal

This avoids the `generalize` pitfall (see below) and lets you use imported equation lemmas from EvalEq.lean.

### Proof Pitfall: `generalize` with imported vs local equation lemmas

`generalize expr = x` requires **syntactic** match — it only replaces occurrences that are syntactically identical, not merely definitionally equal. When using imported equation lemmas (e.g., `eval_forOf_eq` from EvalEq.lean), the elaborated lambda terms may differ subtly from those in your theorem statement. `simp` can further change the form via zeta reduction (let-inlining).

**Avoid `generalize` on foldl expressions.** Instead:
- Use `eval_seq_none_trace` to strip `seq _ Expr.none` wrappers
- State conclusions using `forOfFoldStep` and close with `rfl` (definitional equality)
- Use `have : T := expr` to bridge between definitionally-equal forms when needed
