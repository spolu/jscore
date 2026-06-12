# AGENTS.md

This file provides guidance to AI agents (Claude Code, Codex, etc.) when working with code in this repository.

## Project Overview

JSCore₀ is a verification system: annotated TypeScript → Lean 4 proofs. Agents write code and proofs, humans review annotations (`@requires`, `@invariant`, `@ensures`), Lean kernel checks everything. See [PROPOSAL.md](PROPOSAL.md) for the full system design, motivation, and annotation semantics. See [RESEARCH.md](RESEARCH.md) for the current research plan, known soundness gaps, and the design review against Verus/Aeneas.

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
cd extractor
npx tsx src/index.ts extract  --out-dir ../examples <files...>
npx tsx src/index.ts verify   --out-dir ../examples --lean-dir ../jscore <files...>
npx tsx src/index.ts coverage --out-dir ../examples <files...>
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
- **Eval** — `eval` uses global `fuel : Nat` with structural recursion. List-shaped sub-evaluations go through top-level closure-taking helpers (`evalPairsAux` for obj/spread/call args, `evalElemsAux` for arr, `evalForOfAux` for forOf, `evalWhileAux` for while) — all SHORT-CIRCUIT on the first non-ok outcome, and a call whose argument fails is NOT recorded in the trace. `evalForOf` is a thin wrapper over `evalForOfAux`; eval's forOf case computes it definitionally (no foldl/recursion mismatch). `break` stops forOf. Semantics regression tests: `JSCore/Tests.lean` (`#guard`).
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

- `JSCore/Metatheory/TaintSoundness.lean` — `taint_soundness` is **UNPROVED** (`sorry`). This is the noninterference theorem justifying the syntactic taint analysis; proving it is Phase 2 of RESEARCH.md. (There is no `eval_independent_of_source` lemma — earlier docs claiming both were proved were wrong.)
- Freshly extracted runtime theorems in `examples/` start as `sorry` (intentional — agents fill these in). All current example proofs are complete and `lake build` is green in both `jscore/` and `examples/`.

## Known Soundness Gaps (see RESEARCH.md §2 for details)

- ~~`eval` foldls swallow errors~~ — **FIXED 2026-06**: obj/arr/spread/call-args short-circuit on errors, calls with failing args are not recorded, `break` stops forOf. Pinned by `JSCore/Tests.lean`.
- ~~Unparseable annotations silently translate to `True`~~ — **FIXED 2026-06**: translation is fail-closed (`AnnotationTranslationError`); extraction fails with a non-zero exit and no `.lean` output.
- ~~`push` breaks Env/Store disjointness~~ — **FIXED 2026-06**: pushed arrays extract as `letMut` even when `const`; eval's `push` is Store-only and errors on Env-bound names.
- ~~Fuel-pinned theorems~~ — **FIXED 2026-06**: `Metatheory/FuelMono.lean` proves `eval_fuel_mono` (`Expr.depth e ≤ n ≤ m → eval m = eval n`); generated theorems take `h_fuel : fuel ≥ N`, and proofs open with `rw [eval_fuel_mono N <fn>_body (by decide) fuel h_fuel]`.
- Annotations are not type-checked against TS types; ill-typed `@requires` yields unsatisfiable hypotheses making all runtime theorems vacuous (the known instance in `reorderTasks.ts` is fixed; the systematic check is open).
- `TraceEntry.scopeEnd` is never emitted by `eval` or the extractor, so `inside`/transaction invariants are unprovable.

CI gate: `scripts/ci.sh` — builds both projects, audits sorry/native_decide, checks extractor round-trip idempotence. Run it before considering any change done.

## Proof Strategy for Runtime Theorems

Key tactics and lemmas for closing `sorry` in extracted files:
- **First step of every runtime proof**: `rw [eval_fuel_mono N <fn>_body (by decide) fuel h_fuel]` — converts `eval fuel` to `eval N` using `h_fuel : fuel ≥ N` (FuelMono.lean; `Expr.depth` mirrors the extractor's `depthFuel`)
- `trace_simp` — fully concrete cases
- `forOf_invariant` / `forOf_invariant'` — loop invariants on `evalForOf` (which eval's forOf case computes definitionally)
- `forOf_callsTo` — callsTo invariant for forOf loops (see below)
- `ite_covers` — if/then/else coverage
- `forall_calls_append` / `callsTo_append` / `callsTo_nil` — trace composition
- `callsTo_singleton_call` / `mem_callsTo_singleton` — singleton call trace reasoning
- `env_stable` / `notMutatedIn` — environment stability across eval
- `by_taint` — taint analysis goals
- `by_ordering` — before/inside ordering goals

### Eval Equation Lemmas (`Metatheory/EvalEq.lean`)

Single-step unfolding lemmas for each `Expr` constructor, all proved by `rfl`. These avoid recursive unfolding (which causes timeouts). Use with `rw` to step through eval one constructor at a time.

Available: `eval_var_eq`, `eval_strLit_eq`, `eval_numLit_eq`, `eval_boolLit_eq`, `eval_none_eq`, `eval_seq_eq`, `eval_letConst_eq`, `eval_letMut_eq`, `eval_assign_eq`, `eval_ite_eq`, `eval_forOf_eq` (RHS uses `evalForOf`), `eval_call_eq`, `eval_ret_eq`, `eval_field_eq`, `eval_obj_eq`, `eval_arr_eq`, `eval_spread_eq`, `eval_binOp_eq`, `eval_break_eq`, `eval_throw_eq`, `eval_tryCatch_eq`.

Helper equation lemmas: `evalPairsAux_nil`/`evalPairsAux_cons`, `evalElemsAux_nil`/`evalElemsAux_cons`, `evalForOfAux_nil`/`evalForOfAux_cons`. **`evalPairsAux_pure_cons` / `evalElemsAux_pure_cons`** step over a sub-expression that evaluates to `mkResult (.ok v) store []` — the workhorse for argument/field evaluation: `rw [evalPairsAux_pure_cons (h_sub_eval), evalPairsAux_nil]` then `rfl` or projection simp. Provide `(v := ...)` explicitly when the proof is a `by`-block (delayed unification).

Field access: `mkResult_outcome`/`mkResult_store`/`mkResult_trace`. Lookup: `lookup_none`/`lookup_some`.

Derived properties:
- `eval_var_trace_nil` / `eval_var_store_eq` — var eval produces `[]` trace and preserves store
- `eval_none_trace` — `Expr.none` produces `[]` trace for any fuel (including 0)
- `eval_seq_none_trace` — `seq e Expr.none` has same trace as `e` (strips trailing `Expr.none` in seq)
- `eval_ret_trace` — `ret e` preserves inner trace
- `eval_field_var` — `.field (.var x) fname` evaluates to `mkResult (.ok v) store []` when `x` is bound to `Val.obj fields` in env (not store) and `fieldLookup fields fname = some v`; requires fuel ≥ 2

### ForOf Loop Lemmas (`Metatheory/LoopInvariant.lean`, `Metatheory/ForOfCallsTo.lean`)

Since the 2026-06 eval fix, eval's forOf case computes `evalForOf` **definitionally** (both delegate to `evalForOfAux`), so loop lemmas apply directly to eval output — no foldl bridge needed.

- `evalForOfAux_invariant` (LoopInvariant) — generic: store invariant `I` + per-iteration trace-entry property `P` propagate through the loop for any body closure
- `forOf_invariant` / `forOf_invariant'` (LoopInvariant) — eval-specific corollaries over `evalForOf`
- **`forOf_callsTo`** (ForOfCallsTo) — main workhorse: store invariant `I` + per-call property `P` over `callsTo … pattern`; apply after `rw [eval_forOf_eq]` exposes `evalForOf` in the goal
- `eval_forOf_non_arr_trace` (ForOfCallsTo) — non-array case: forOf trace equals array expr trace
- `mem_callsTo` (TraceComposition) — `c ∈ callsTo t p ↔ .call c ∈ t ∧ matchesPattern c.target p`

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
2. **Unfold forOf:** `rw [eval_forOf_eq]` then `rw [eval_var_eq]` + `rw [h_lookup]` to resolve the array; projection simp reduces the goal to a statement about `evalForOf`
3. **Apply `forOf_callsTo`** with the store invariant (typically `fun s => s = store`) and the per-iteration lemma
4. Per-iteration lemmas evaluate the loop body via `eval_call_eq` + `evalPairsAux_pure_cons` chains ending in `rfl`

See `examples/reorderTasks_jscore.lean` for the full pattern.

### Proof Pitfall: `generalize` with imported vs local equation lemmas

`generalize expr = x` requires **syntactic** match — it only replaces occurrences that are syntactically identical, not merely definitionally equal. When using imported equation lemmas (e.g., `eval_forOf_eq` from EvalEq.lean), the elaborated lambda terms may differ subtly from those in your theorem statement. `simp` can further change the form via zeta reduction (let-inlining).

**Avoid `generalize` on large eval expressions.** Instead:
- Use `eval_seq_none_trace` to strip `seq _ Expr.none` wrappers
- State conclusions using the named helpers (`evalForOf`, `evalPairsAux`) and close with `rfl` (definitional equality)
- Use `have : T := expr` to bridge between definitionally-equal forms when needed
