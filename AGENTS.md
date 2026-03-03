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
node dist/index.js extract --out-dir ../generated <files...>
node dist/index.js verify  --out-dir ../generated --lean-dir ../jscore <files...>
node dist/index.js coverage --out-dir ../generated <files...>
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
- **Metatheory/** — TraceComposition, EnvStability, LoopInvariant, ConditionalCoverage, Composition, TaintSoundness.
- **Tactics** — `trace_simp` (unfolds eval/binop/trace/string defs), `by_taint` (unfolds taint analysis), `by_ordering` (before/inside with omega).

### Extractor (`extractor/src/`)

- **ast-to-jscore.ts** — ts-morph AST → `JsCoreExpr`. Processes statements in CPS style (each statement's body is `rest()`).
- **lean-emitter.ts** — `JsCoreExpr` → Lean 4 source text.
- **lean-theorem.ts** — Annotations → Lean theorem statements. Three shapes: taint (native_decide), nonexistence (native_decide), runtime ∀ (sorry for agents).
- **annotation-parser.ts** — Parses `@requires`/`@invariant`/`@ensures` from TS comments. Multi-line via continuation lines.
- **reassignment.ts** — Determines letConst vs letMut based on reassignment analysis.
- **type-translator.ts** — TS types → Lean Val predicates.

### Generated Lean file structure

Each extracted function produces: a `def <name>_body : Expr` with the expression tree, then theorems. Syntactic theorems (taint, nonexistence) close with `native_decide`. Runtime theorems have `sorry` for agents to fill using metatheory lemmas.

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
- All generated runtime theorem proofs (intentional — agents fill these in)

## Proof Strategy for Runtime Theorems

Key tactics and lemmas for closing `sorry` in generated files:
- `trace_simp` — fully concrete cases
- `forOf_invariant` / `forOf_invariant'` — loop invariants
- `ite_covers` — if/then/else coverage
- `forall_calls_append` / `callsTo_append` — trace composition
- `env_stable` / `notMutatedIn` — environment stability across eval
- `by_taint` — taint analysis goals
- `by_ordering` — before/inside ordering goals
