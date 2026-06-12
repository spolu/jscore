# JSCore₀ — Research Plan

Status: 2026-06-12. This document records the findings of a design review (including a
comparison against Verus and Aeneas) and lays out the research plan. It is the working
roadmap; PROPOSAL.md remains the system-design document.

---

## 1. Where we stand

What works today:

- A deep-embedded calculus (`Expr`, 26 constructors) with a fuel-indexed functional
  evaluator producing a first-class **trace** of external calls.
- A syntactic taint analysis (`notTaintedIn`) discharged by `native_decide`.
- An extractor (ts-morph) producing one consolidated `.lean` file per `.ts` file, with
  proof-preserving regeneration.
- A metatheory layer (EvalEq equation lemmas, trace composition, `forOfFold_callsTo`,
  env stability) that made the example proofs *possible* — all example proofs check.

What doesn't:

- Proof-to-code ratio is ~5–10:1 **per invariant** for trivial properties
  (`reorderTasks`: 28 lines of TS, one invariant, ~150 lines of Lean).
- The central taint soundness theorem is `sorry` (see §2.1).
- Several soundness gaps in the model and the annotation pipeline (§2).

---

## 2. Issues found (review, 2026-06)

Ordered by severity. P0 items undermine the trust story the system is built on.

### 2.1 `taint_soundness` is unproved (P0)

`JSCore/Metatheory/TaintSoundness.lean` is a single `sorry`. This is the theorem that
justifies interpreting the syntactic check `notTaintedIn = true` as the semantic claim
"the secret cannot reach the call's arguments". Until it is proved, every
`no-secret-leak` invariant in the system is a claim about an unverified static analysis
— exactly the situation (trusted analyzer, no kernel-checked connection to semantics)
the project exists to avoid. Note the statement is a **noninterference property**
(2-safety/hyperproperty): two runs differing only in the source value produce identical
matching call records. This is also the strongest argument for using Lean over SMT —
Verus cannot even state it (see §3) — so proving it is both a debt and a headline.

### 2.2 `eval` swallows errors inside `obj` / `arr` / call-argument folds (P0, semantic bug) — **FIXED 2026-06**

> Fixed: `evalPairsAux`/`evalElemsAux`/`evalForOfAux` (top-level, closure-taking)
> short-circuit on the first non-ok outcome; calls with failing args are not
> recorded; `break` now stops forOf; eval's forOf agrees with `evalForOf`
> definitionally (ForOfCallsTo's foldl bridge deleted, `forOf_callsTo` replaces
> `forOfFold_callsTo`). Semantics pinned by `jscore/JSCore/Tests.lean` (#guard).
> All example proofs re-proved (slightly shorter than before).

Original finding (kept for the record):

The inline `foldl`s for `.obj`, `.arr`, `.spread` overrides, and `.call` arguments do
not stop when a sub-expression evaluates to a non-`ok` outcome: they drop the field and
keep folding, and the final result is unconditionally `.ok`:

```lean
| .obj pairs =>
    ... match r.outcome with
        | .ok v => (vals ++ [(pair.1, v)], r.store, curTrace ++ r.trace)
        | _ => (vals, r.store, curTrace ++ r.trace)   -- error dropped, fold continues
    ...
    mkResult (.ok (.obj result.1)) ...                 -- outcome ignored
```

Consequences: a throw inside `{a: f(), b: g()}` is silently converted into "field
missing", `g()` still executes in the model (in JS it does not), and — worst — `.call`
records the call **even when an argument threw**, so the model trace contains calls the
runtime never makes. For `∀ call` invariants this is over-approximating (acceptable);
for `∃ call` invariants (`audit-complete`, `auth-gate`) it is **unsound**: the model can
exhibit a witness call that real execution never performs. Fix: make the folds
short-circuit on the first non-`ok` outcome (mirror `evalForOf`'s structure), and
propagate the error outcome. This changes `eval`'s equations, so EvalEq/ForOfCallsTo
need mechanical updates; do it before more proofs accumulate on the wrong semantics.

### 2.3 Unparseable annotations silently become `True` (P0) — **FIXED 2026-06**

> Fixed: translation is fail-closed. `lean-theorem.ts` throws
> `AnnotationTranslationError` on any annotation it can't translate to a
> non-trivial proposition; no `.lean` output is written for the file and the
> CLI exits non-zero with the offending annotation and reason.

Original finding (kept for the record):

`lean-theorem.ts` falls back to `True /- TODO: ... -/` when an invariant, requires, or
ensures fails to parse (`translateCallPred`, `translateRequireToLean`,
`translateEnsuresPred`, and the catch-all runtime translation). A human approves
`@invariant audit-complete: ∀ call ... ∃ call ...` — the `∃` shape isn't implemented —
and CI happily reports "proved" on a vacuous `True`. This inverts the trust story: the
one artifact the human reviews is the one whose formal meaning can silently evaporate.
Fix: translation must **fail closed** — any annotation that does not translate to a
non-trivial proposition is an extraction error, surfaced in `coverage`/`verify`.

### 2.4 No vacuity / well-typedness checking of annotations (P0) — **FIXED 2026-06**

> Fixed: `extractor/src/annotation-typecheck.ts` type-checks `@requires` and
> `@ensures` (the *hypotheses* — a mistyped conclusion is fail-safe, merely
> unprovable) against TS types: numeric ops on non-numbers, kind-mismatched
> equalities, `starts_with`/`∈` kind errors, missing fields, and contradictory
> numeric bounds (interval check) all fail extraction. This caught **three
> more vacuous theorems** in the shipped examples (`exportWorkspaceData`,
> `lookupProject`, `scopedUpdate` all carried `@requires auth.workspaceId > 0`
> on a string field); their annotations are now
> `auth.workspaceId starts_with "ws_"` — well-typed and still load-bearing —
> and the proofs were redone against the honest hypothesis. A kernel-checked
> witness term per theorem (vs this extractor-side check) is deferred —
> revisit with the Phase 3 reflection engine.

`examples/reorderTasks.ts` carries `@requires auth.workspaceId > 0` — a *string* field
compared numerically. The generated hypothesis demands `auth.workspaceId` be a
`Val.num`, which is unsatisfiable for every real input, making **all** runtime theorems
for that function vacuously true. Nothing catches this; the same file's `ws-isolation`
tag actually constrains `projectId`, not `workspaceId` — annotation drift that a
reviewer reading only annotations would mis-approve. Fixes:
- Type-check annotation expressions against the TS types (the extractor already has the
  type checker; `type-translator.ts` knows `workspaceId : string`).
- Emit a **satisfiability witness** per theorem: a concrete input (from the TS types)
  for which all hypotheses hold, checked by `decide`/evaluation. A theorem whose
  hypotheses admit no witness should fail CI.

### 2.5 Fuel-pinned theorems, no fuel monotonicity (P1) — **FIXED 2026-06**

> Fixed: `Metatheory/FuelMono.lean` defines `Expr.depth` (mirroring the
> extractor's `depthFuel`) and proves `eval_fuel_mono` — any fuel ≥ the term's
> structural depth yields the same result (induction on fuel; congruence
> lemmas for the closure-taking helpers). The extractor now emits
> `h_fuel : fuel ≥ N`, and proofs open with
> `rw [eval_fuel_mono N body (by decide) fuel h_fuel]`. Generated theorems now
> quantify over all sufficient fuels.

Original finding (kept for the record):

Generated theorems take `(h_fuel : fuel = 8)`. The proved statement is about `eval 8`,
not about "the execution"; nothing connects fuel 8 to fuel 9. Because `eval`'s fuel
decreases per *AST depth* (not per loop iteration — `forOf`'s foldl reuses `fuel'`),
a fixed fuel ≈ term depth is in fact sufficient for arbitrary input sizes, but that
argument lives in nobody's head and no lemma. Fix:
- Prove `eval_fuel_mono : sufficientFuel e ≤ n → eval n env store e = eval (n+1) env store e`
  with a computable `sufficientFuel : Expr → Nat` (structural depth; `whileLoop` carries
  its own fuel so it doesn't escalate).
- Restate generated theorems as `∀ fuel ≥ sufficientFuel body` (or define
  `run e env store := eval (sufficientFuel e) env store e` and state theorems about
  `run`). This also kills the `rw [show (6:Nat) = 5+1 from rfl]` stepping noise in every
  proof.
- Longer term: an inductive big-step relation with `eval` as its decision procedure
  (soundness + completeness), so theorems quantify over derivations, not fuel.

### 2.6 `native_decide` is in the trust chain (P1)

Taint and nonexistence theorems close by `native_decide`, which trusts the Lean
compiler, `implemented_by` attributes, and the C toolchain — a far larger TCB than the
kernel, and the known soundness-loophole vector in Lean. This contradicts the "Lean
kernel verdict, decades of trust" pitch in PROPOSAL.md. The checks are small finite AST
traversals; `decide` should be feasible if the Bool functions are written for kernel
reduction (avoid `String.splitOn` in hot paths — see §5.2). Policy: `decide` by
default; `native_decide` only behind an explicit, documented opt-in.

### 2.7 `scopeEnd` is never emitted (P1)

`TraceEntry.scopeEnd` exists and `inside` (transaction scoping) is defined over it, but
neither `eval` nor the extractor ever produces a `scopeEnd` entry. Every
`transactional:`-style invariant is unprovable (or vacuous, depending on shape). Either
implement scoped calls (a `callScoped target args binder callbackBody rest` constructor
whose eval brackets the callback trace with `call`/`scopeEnd`) or delete `inside` until
it's real.

### 2.8 `push` breaks Env/Store disjointness (P2) — **FIXED 2026-06**

> Fixed on both sides: the extractor classifies pushed arrays as `letMut` even
> when declared `const` (`findPushedVars` in reassignment.ts), and eval's
> `push` does a Store-only lookup — pushing an Env-bound name errors instead
> of silently shadowing. Pinned by two #guard tests in `JSCore/Tests.lean`.

Original finding (kept for the record):

`push` writes the updated array into `Store` even when the array was `letConst`-bound
(JS `const arr = []; arr.push(x)` is legal and common — it's the `map`/`filter`
desugaring target). After the first push, `lookup` sees the Store copy and the
"`letConst` names never appear in Store" invariant — which `env_stable` and every
generated `h_store_x : store "x" = none` hypothesis lean on — is violated for that name.
Fix: extractor must classify pushed arrays as `letMut` (reassignment.ts should treat
`.push` as a write), and `push` in eval should error if the name is not already in
Store. Add a regression test.

### 2.9 Semantic divergences from JavaScript are undocumented (P2)

Deliberate modeling choices, fine individually, but they need a written soundness
contract (what does a proof about the model guarantee about the TS program?):
- `Int` vs IEEE-754 doubles; `/` and `%` are truncating integer ops. An invariant
  proved about `a / b` can be false at runtime. The extractor should *reject* `/`, `%`
  on numbers (or model them as opaque) until a story exists.
- `binOp .eq` is structural `BEq` on `Val`; object equality is field-order-sensitive,
  and JS `===` on objects is reference equality. Extractor should reject `===` between
  non-primitive types.
- `field` on non-objects yields `ok none` (JS throws on `null`/`undefined` access);
  missing fields yield `none` (matches `undefined`). No `undefined` vs `null`
  distinction. Document.
- `Promise.all` sequentialization: already documented in PROPOSAL.md; keep.

### 2.10 Documentation drift (fixed)

CLAUDE.md and the project memory claimed `taint_soundness` was proved; the file is
`sorry` and the named lemma `eval_independent_of_source` does not exist. Corrected as
part of this review. CI should grep for `sorry` outside `examples/` and fail (the
`sorry`s in freshly-extracted examples are intentional; library `sorry`s are not).

---

## 3. What Verus teaches us

Verus (Rust → VIR → AIR → Z3) shows **why SMT is enough for its property class — and
that its property class excludes ours**:

- **Why SMT suffices there.** Verus restricts itself to first-order safety/functional
  correctness over machine ints, bitvectors, `Seq`/`Map`, ADTs — fragments where SMT is
  decidable or near-complete — and uses Rust's ownership discipline to *eliminate the
  heap from the encoding* (`&mut T` becomes a value pair; no frame axioms). Result:
  proof-to-code ratios of ~0.3–2 and second-scale verification, vs seL4-class 20:1.
  The escape hatches (manual triggers, `assert..by`, proof functions for induction,
  disabled nonlinear arith) mark exactly where SMT automation frays.
- **What it cannot do.** No execution traces as semantic objects (history must be
  reified as ghost state by hand), no hyperproperties — our `taint_soundness`
  (noninterference, 2-safety) is *not statable* as a Verus contract. And the TCB is the
  encoder + Z3 (~500kLOC, no proof objects), vs our kernel-checked story.
- **The transplantable lesson.** JSCore₀'s property grammar is *also* a deliberately
  restricted first-order fragment (arg-at-path equalities, membership, prefixes, sums,
  ordering). Verus's leverage comes from discharging that fragment with a *decision
  procedure* instead of interactive proof. We can have the same leverage **without
  giving up the kernel**: proof by reflection (§6) — a verified checker run by `decide`.
  Where Verus trusts Z3, we prove the checker sound once, in Lean.

So: SMT is enough for Verus because of property-class restriction plus ownership; it
would not be enough for JSCore₀'s taint/noninterference claims, and adopting an SMT
backend would trade away the small TCB that is this project's entire differentiation.
The right move is to steal the *automation philosophy*, not the solver.

## 4. What Aeneas teaches us

Aeneas (Rust → Charon/LLBC → pure functional Lean) is the strongest existing argument
for **shallow embeddings**: borrows become forward/backward functions, loops become
recursive functions, programs become ordinary Lean definitions, and proofs become
`progress`-driven symbolic execution over a `Result` monad — a few lines per function,
with fuel hidden behind unfolding equations.

JSCore₀ chose a deep embedding, and pays for it in every proof: each theorem manually
symbolically executes `eval` over the term via equation lemmas. But the deep embedding
is what lets us state properties *about programs as data* — `notTaintedIn` is an AST
predicate, `taint_soundness` quantifies over environments, and trace properties
quantify over a semantic object the shallow translation wouldn't surface unless built
in. The synthesis:

- **Keep the deep embedding as the semantic anchor** (taint, noninterference, the
  trust argument).
- **Steal Aeneas's ergonomics for the per-program proofs**, in either of two forms:
  1. *Shallow companion translation*: the extractor (or a Lean metaprogram) also emits
     each function as an ordinary Lean definition in a trace-writer monad
     (`StateT Store (ExceptT Val (Writer (List TraceEntry)))`-shaped), plus a theorem
     `⟦f⟧_shallow = eval n env store f_body` proved by `rfl`/`simp`. Runtime invariants
     are then proved against the shallow form with `simp`/`omega` and a small
     `progress`-style tactic, Aeneas-fashion.
  2. *Verified checker / reflection* (§6) — subsumes (1) for the supported fragment and
     is the better long-term bet; (1) remains the fallback for properties outside the
     checker's fragment.
- Aeneas's loop story (loops → recursive functions over the loop frame) also motivates
  §5.4: eliminating `Store` via SSA-style renaming would remove the Env/Store dichotomy
  that bloats every theorem statement with `h_store_* = none` hypotheses.

## 5. AST → Lean model: concrete improvements

1. **Fix the error-swallowing folds** (§2.2) — correctness, do first.
2. **Path/pattern pre-splitting.** `argAtPath` and `matchesPattern` take dotted
   `String`s and call `String.splitOn` at proof time; every example re-proves
   `("where.projectId").splitOn "." = [...]` by `native_decide`. Change the Lean API to
   take `List String` segments and have the *extractor* emit
   `argAtPath c ["where", "projectId"]`. All string-splitting reasoning disappears from
   proofs, and `decide` becomes viable where `native_decide` was needed.
3. **Fuel discipline** (§2.5): `sufficientFuel` + `eval_fuel_mono`, theorems stated at
   `∀ fuel ≥ sufficientFuel body`.
4. **Eliminate `Store` for most programs (SSA).** `reassignment.ts` already computes
   reassignment; instead of routing reassigned variables through a second namespace,
   rename (`x` → `x₁, x₂, …`) and translate loops Aeneas-style as recursion over the
   loop-carried frame. `letMut`/`assign`/`Store` then only remain for genuinely
   loop-carried mutation (`reduce`, accumulator `push`), and ideally a
   `forOf-with-accumulator` constructor models that directly. Every generated theorem
   loses its `h_store_* = none` hypothesis block, `lookup` collapses to `env x`, and
   `env_stable` becomes trivial. This is the single biggest statement-size reduction
   available.
5. **Unique-binder certificate.** Have the extractor alpha-rename to globally unique
   names and emit `BindersUnique body = true` (a decidable AST predicate) once per
   function. Metatheory lemmas can then assume non-shadowing instead of case-splitting
   on string equality at every `Env.set`/lookup step.
6. **Transactions**: implement scoped calls + `scopeEnd` emission, or drop `inside`
   (§2.7).
7. **Reject divergent operators** at extraction (`/`, `%`, `===` on objects) until
   modeled honestly (§2.9). Rejection is already the documented philosophy for
   unmodeled constructs — apply it to unmodeled *semantics* too.
8. **Env as data for canonical theorems.** The `_canonical` theorems instantiate
   `emptyEnv.set "a" a …` (function values), which blocks `Decidable` instances. An
   assoc-list env with a `⟦·⟧ : EnvL → Env` coercion lets fully-concrete properties be
   closed by `decide` end-to-end.

## 6. Lean library: making proofs small

Near-term (weeks, mechanical):

- **Generic argAtPath lemmas** — one lemma family
  (`argAtPath_cons_hit`, `argAtPath_cons_miss`, `argAtPath_obj_field`) replacing the
  per-example private lemmas (`argAtPath_where_pid`, `argAtPath_where_wsId_2`, …).
  With §5.2 these become `simp` lemmas requiring no string reasoning.
- **Simp sets over macro tactics.** Register `@[eval_simp]`, `@[taint_simp]`,
  `@[trace_simp]` attributes (via `register_simp_attr`) and tag the EvalEq/trace
  lemmas, so `trace_simp` is `simp only [eval_simp, …]` that users can extend, instead
  of a frozen macro list in Tactics.lean.
- **An `eval_step` tactic** (the Aeneas `progress` analogue): one tactic invocation
  steps the goal through one `Expr` constructor — applies the right `eval_*_eq` lemma,
  normalizes `mkResult` projections and `++ []`/`[] ++`, and discharges
  lookup side-conditions from `h_env_*`/`h_store_*` hypotheses by `assumption`/`simp`.
  `eval_step*` then replaces the `rw [show 6 = 5+1…, eval_seq_none_trace]; rw […]`
  liturgy. Target: `eval_outer_trace`-style helper lemmas become 2–3 lines.
- **lookup automation**: `lookup_set_same`, `lookup_set_ne` (with `String` `decide`
  discharge), `Env.set` commutation under distinct names, packaged into the simp sets.

Medium-term (the real bet) — **proof by reflection**:

Build a *verified symbolic evaluator* over a symbolic value domain

```
SymVal := param <name> <path>        -- projection of a function parameter
        | lit <Val>
        | obj (List (String × SymVal)) | arr (List SymVal) | …
        | unknown <callResultId>      -- opaque call result / widened loop value
```

and a checker `checkForallCalls (body : Expr) (pattern : List String)
(path : List String) (rhs : SymExpr) : Bool` that symbolically executes the program
(joining branches, widening loop-carried state) and verifies every reachable matching
call's argument-at-path equals the symbolic RHS. Prove **once**:

```
theorem checkForallCalls_sound :
    checkForallCalls body pat path rhs = true →
    ∀ env store fuel …(well-formedness)…,
      ∀ c ∈ callsTo (eval fuel env store body).trace pat,
        argAtPath c path = ⟦rhs⟧ env
```

Then `reorderTasks_ws_isolation` is `by apply checkForallCalls_sound; decide` — one
line, kernel-checked, no agent proof-search at all for the supported fragment. This is
the Verus lesson (decision procedure for a restricted fragment) realized with a Lean
kernel TCB, and the taint pipeline (`notTaintedIn` + `taint_soundness`) is already this
exact architecture — the research step is extending it from taint to the data-flow
invariant grammar, and actually proving the soundness theorems. Agents then only write
proofs for properties *outside* the checker fragment (∃-ordering, sums, cross-function
composition), which is also the natural fragment-growth feedback loop: every property
the checker can't do is a candidate next feature.

## 7. Plan

### Phase 0 — Foundations & honesty (do immediately)
1. ✅ **DONE 2026-06** — Fix error-swallowing folds in `eval` (§2.2); EvalEq/
   ForOfCallsTo/LoopInvariant reworked; examples re-proved; #guard tests added.
2. ✅ **DONE 2026-06** — Fail-closed annotation translation (§2.3).
3. ✅ **DONE 2026-06** — annotation type-checking + contradiction detection
   (`annotation-typecheck.ts`); all four example vacuity instances fixed
   (§2.4). Kernel-checked witnesses deferred to Phase 3.
4. ✅ **DONE 2026-06** — `Expr.depth` + `eval_fuel_mono` (FuelMono.lean);
   generated theorems take `fuel ≥ N` (§2.5).
5. ✅ **DONE 2026-06** — `scripts/ci.sh`: builds both projects, sorry audit
   (TaintSoundness allowlisted), native_decide forbidden in the library,
   extractor round-trip idempotence over examples.
6. ✅ **DONE 2026-06** — `push`/`letMut` fixed (§2.8); extractor rejects `/`,
   `%`, object `===`/`!==`, unknown operators; **SEMANTICS.md** is the
   divergence contract (§2.9). Writing it surfaced one more divergence —
   `arr[-1]` clamped to index 0 instead of yielding `none` — fixed in eval and
   pinned by #guard tests.

**Phase 0 is complete.**

Exit criterion: every theorem that CI reports "proved" means what the annotation says,
for all sufficient fuels, with no vacuous hypotheses.

### Phase 1 — Proof-size reduction (library work)
1. Paths/patterns as `List String` through extractor + Trace API (§5.2).
2. Generic argAtPath/matchesPattern simp lemmas; simp sets; `eval_step` tactic (§6).
3. SSA experiment: extractor pass eliminating `letMut` for non-loop-carried
   reassignment; measure hypothesis/statement shrinkage (§5.4).
4. Re-prove all examples; **metric: proof LOC per invariant**, target ≥3× reduction
   (reorderTasks: 150 → ≤50 lines).

### Phase 2 — Taint soundness (the debt, and a paper-grade result)
1. Prove `taint_soundness` (noninterference). Suggested route: define a binding-set
   indexed simulation (`envs agree off taintedSet` ∧ `stores agree off taintedSet`),
   prove a fundamental lemma by induction on fuel/Expr mutual structure, derive the
   trace-equality corollary. The §2.2 fix simplifies this (no error-swallowing cases).
2. If the full statement resists, *weaken honestly*: restrict to programs passing a
   stricter decidable precondition (e.g. no `Store` after SSA), and make the extractor
   emit that precondition. A proved theorem about a smaller fragment beats a `sorry`
   about a bigger one.

### Phase 3 — Reflection engine (the headline)
1. Symbolic evaluator + `checkForallCalls` + soundness theorem (§6).
2. Extend the checker fragment: membership (`∈ [..]`), `starts_with`, implication
   guards from `ite` conditions (subsumes `ite_covers` reasoning), `¬∃` (already
   syntactic via `callExprsIn` — port to the same framework).
3. Extractor emits `by exact checkX_sound … (by decide)` proofs directly; agents only
   see `sorry` for out-of-fragment properties.
4. Metric: fraction of the 20 PROPOSAL.md invariants closed fully automatically.

### Phase 4 — Expressiveness gaps
1. `∃ call … before/after` invariants (audit-complete, auth-gate): trace-ordering
   metatheory + checker support (symbolic trace is a *sequence* of symbolic calls, so
   ordering is decidable in the same pass).
2. `sumOver` / conservation invariants.
3. Transactions: scoped calls + `scopeEnd` (§2.7); `inside` checker support.
4. Cross-function composition: implement the `invariant_composition` story from
   PROPOSAL.md (currently only trace-append lemmas exist) — callee invariants as lemmas
   keyed by call target, applied at `call` sites in the caller's proof/checker.
5. `Promise.all`: a `par` construct proved sound under all interleavings, or keep the
   documented sequential conservatism.

### Phase 5 — Scale evaluation
1. Extract a realistic codebase slice (a Dust-like API surface: ~20–50 functions);
   measure extraction coverage %, checker-closure %, agent success rate on the
   remainder, wall-clock verify time.
2. The PROPOSAL.md "twenty invariants" as a benchmark suite with golden Lean output.
3. Ablations: deep+reflection (ours) vs shallow companion (§4.1) on proof effort.

### Phase 6 — Positioning / writing
Position against: Verus (automation via SMT, fat TCB, no hyperproperties/traces),
Aeneas (shallow translation, no program-as-data properties, trusted translation),
RustBelt-style foundational work (small TCB, prohibitive effort). JSCore₀'s claim:
*trace and noninterference properties of effectful glue code, stated against a deep
embedding, discharged by verified decision procedures, with a kernel-only TCB and a
human-review surface of one-line annotations*. The honest TCB statement: Lean kernel +
extractor (~1.5kLOC) + annotation translator + `@ensures` assumptions — and the
research goal is keeping the middle two small and boring.

---

## 8. Open questions

- **Loop invariant inference for the checker**: widening to `unknown` loses per-element
  facts (e.g. `position = indexOf(...)` in reorderTasks needs the loop *index*). How
  much of the invariant grammar survives a purely syntactic widening? Likely need
  symbolic loop variables (`elem i of param "tasks"`) — an indexed widening.
- **`@ensures` trust**: ensures hypotheses are assumed, not proved. Can DB-schema-level
  facts (`findUnique` returns row matching `where`) be checked once against a Prisma
  schema and reused, shrinking the per-annotation trust surface?
- **Float semantics**: is rejecting `/` viable for real code, or do we need a rational/
  float model? Survey real Dust handlers for arithmetic usage first.
- **Should `Env`/`Store` be one assoc-list state** with extraction-time SSA making
  immutability a *theorem* rather than a namespace? (§5.4 experiment decides.)
- **Trace equality vs trace refinement**: after the §2.2 fix, is the model trace always
  a *prefix-refinement* of the runtime trace under error? State and prove the intended
  relation explicitly as the model's soundness contract.
