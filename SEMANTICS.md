# JSCore₀ — Model Soundness Contract

What a Lean proof about a `_jscore.lean` term does and does not guarantee
about the TypeScript program it was extracted from. This is the document a
reviewer should read before trusting "proved" in CI output.

**The headline guarantee.** For a fully extracted function (no `sorry`), under
the assumptions listed in §3, the model's trace of external calls — targets
and fully-evaluated argument values, in order — matches the runtime's, up to
the documented divergences in §2. An invariant proved over the model trace
therefore holds for the runtime trace.

---

## 1. What is modeled faithfully

- **Data flow**: parameters → const/let bindings → field access → object/array
  construction → call arguments. Bindings are exact; `const`-bound names live
  in an immutable `Env`, mutated names (including arrays mutated via `.push`)
  in a mutable `Store`. The extractor guarantees Env/Store name-disjointness.
- **Control flow**: `if`/ternary, `for...of` (incl. `break`, early `return`),
  bounded `while` (see §2.6), `try/catch` over thrown values, `&&`/`||`
  desugarings, early returns.
- **Error propagation**: a throw aborts evaluation of the enclosing
  expression — object/array literals and argument lists short-circuit, a call
  whose argument evaluation fails is **not** recorded in the trace, and a loop
  stops at the first failing iteration. (Pinned by `jscore/JSCore/Tests.lean`.)
- **Integer arithmetic**: `+`, `-`, `*`, comparisons over JS numbers that are
  used as integers, modeled as unbounded `Int` (see §2.1).
- **String operations**: concatenation, template literals, `startsWith`,
  equality.

## 2. Documented divergences (model vs JS)

Each entry states the divergence and its consequence for proofs.

### 2.1 Numbers are `Int`, not IEEE-754 doubles
`Val.num : Int`. There is no float, `NaN`, `Infinity`, `-0`, or precision
loss. `+`, `-`, `*` agree with JS only while values stay within the safe
integer range and are integers. **Mitigation**: the extractor *rejects* `/`
and `%` (extracted as `sorry` — unverifiable) since truncating `Int` division
is visibly different from JS. Code relying on float behavior or overflow is
outside the model; proofs about it say nothing.

### 2.2 Equality is structural; object identity does not exist
`===` is modeled as structural `BEq` on `Val`, and object field order is
significant (`{a, b} ≠ {b, a}` in the model; both differ from JS reference
equality). **Mitigation**: the extractor rejects `===`/`!==` between
non-primitive operands. Primitive comparisons (string/number/boolean and
literal unions) agree with JS.

### 2.3 Property access on absent fields and non-objects yields `none`
`obj.missing` → `Val.none`, matching JS `undefined`. But `e.f` where `e`
evaluates to a non-object also yields `ok none`, whereas JS **throws
TypeError** on `null`/`undefined` receivers. Consequence: the model may
continue executing (and recording calls) past a point where the runtime would
have crashed — the model trace can be a *superset* of the runtime trace on
such paths. Safe for `∀ call` invariants; for `∃ call` invariants the witness
call could sit after a would-be TypeError. TypeScript's type checker makes
non-null access on typed code rare, but `T | null` flows are the user's
responsibility (use explicit guards, which the model does follow).

### 2.4 `undefined` and `null` are one value
Both map to `Val.none`. Code that distinguishes them (`x === undefined` vs
`x === null`) is not faithfully modeled.

### 2.5 Call results are opaque
An external call's result is bound as `Val.none` in evaluation. Code whose
*control flow* depends on a call result (e.g. `if (row.deleted) ...`) is
modeled as if the result were `none`, **unless** the binding carries
`@ensures` annotations — then the body reads a universally-quantified
parameter constrained by exactly the `@ensures` hypotheses and the TS type
predicates. Consequence: properties that depend on un-annotated result values
are proved for the `none`-result execution only. Annotate result-dependent
branches with `@ensures`, or treat the proof as covering the data-flow
skeleton.

### 2.6 `while` loops carry explicit fuel
`whileLoop N cond body` runs at most `N` iterations (`@fuel` annotation,
default project-wide limit). Exhaustion yields an `error` outcome with the
trace up to that point. Per-iteration invariants are unaffected; post-loop
claims must account for the error path.

### 2.7 `Promise.all` is sequentialized
Calls inside `Promise.all` are modeled in argument order. Per-call properties
(isolation, taint, membership) are unaffected; `before`/`after` ordering
invariants *between calls inside the same `Promise.all`* are proved under the
sequential order only and are not guaranteed at runtime.

### 2.8 Thrown values are simplified
`throw new Error(msg)` is modeled as throwing the string `msg`; Error
objects, subclasses, stacks, and `instanceof` checks in catch blocks are not
modeled.

### 2.9 Array index semantics
`arr[i]` with negative or out-of-bounds `i` yields `none` (JS `undefined`) —
matching JS. Non-integer indices don't arise (numbers are `Int`).

## 3. Trust assumptions (the fine print)

A "proved" verdict relies on:

1. **The Lean kernel** (and, for theorems closed by `native_decide` —
   currently only in `examples/` — the Lean compiler toolchain; tracked P1
   work removes this).
2. **The extractor** (~1.5k LOC TypeScript): the JSCore₀ term faithfully
   represents the source. Unmodeled constructs and divergent operators are
   rejected (extracted as `sorry`, reported by `coverage`/`verify`), and
   untranslatable annotations fail extraction — both fail closed.
3. **The annotation translator**: the Lean proposition means what the
   annotation says. Translation is fail-closed; annotations are the artifact
   humans review.
4. **`@ensures` annotations are assumed, not proved**: if an external call
   violates its `@ensures` at runtime, proofs are sound over wrong
   assumptions. Keep these to schema/API-contract facts.
5. **TS type predicates** come from the TypeScript checker, which the codebase
   already trusts.

## 4. Regression protection

The error/short-circuit semantics, push/Env-Store disjointness, and index
behavior above are pinned by executable `#guard` tests in
`jscore/JSCore/Tests.lean`, built by `scripts/ci.sh`. When changing `eval`,
extend those tests; when a divergence is discovered, either fix `eval` to
match JS, make the extractor reject the construct, or document it here —
never leave it silent.
