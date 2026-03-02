# `@invariant` — A Verification System for Agent-Generated TypeScript

---

## Motivation

The bottleneck has shifted. Models are increasingly capable — the deficiency is now human:

- **Humans can't write formal specifications** from scratch, but they can approve a one-line constraint
- **Humans can't review agent-generated code** at the scale and speed agents produce it
- **Humans can't catch subtle behavioral regressions** across thousands of lines of changed implementation

This system inverts the usual flow: agents write code, proofs, _and_ most invariants, humans _only_ specify what the code should do by collaborating with agents on invariants, and a mathematical kernel checks the proofs. The human's role is authoring intent and approving behavioral changes — not reading implementation.

---

## The Human Interface: Three Annotations

Humans collaborate with agents on three types of comment annotations. `@requires` and `@invariant` go on function signatures; `@ensures` goes inline at call sites in the function body.

```typescript
// @requires amount > 0
// @requires fromId ≠ toId
// @invariant ws-isolation: ∀ call db.* (c) => c.where.workspaceId = auth.workspaceId
// @invariant conservation: ∀ call db.account.update (u) =>
//   sum(u.data.balance.increment) = 0
async function transferCredits(
  auth: Auth,
  fromId: string,
  toId: string,
  amount: number,
) {
  const from = await db.account.findUnique({ where: { id: fromId } });
  // @ensures from.balance ≥ amount

  // ... implementation
}
```

### `@requires <prop>`

A condition the _caller_ must prove before invoking this function. Becomes a hypothesis in the function's own proofs — the function gets to assume it. If the function internally validates the condition and throws (e.g. `if (amount <= 0) throw ...`), the proof for the invariant finds the guard automatically from the control flow; the caller still has no obligation because there is no `@requires` on their side.

The key insight: `@requires` is not about _where_ the check happens. It's about _who is responsible_. If it appears on a function, the caller is responsible for proving it. If it doesn't appear, no one is — and any needed fact must come from the code's own control flow.

```typescript
// @requires amount > 0
// @requires fromId ≠ toId
// @requires endpoint.url starts_with "https://"
// @requires auth.role ∈ ["admin", "editor"]
// @requires items.length ≤ 100
// @requires startDate < endDate
// @requires auth.workspaceId = workspace.id
```

### `@invariant <tag>: <prop>`

A proposition proved over every execution of the function. The tag is a human-readable name used in CI output and review diffs.

```typescript
// @invariant ws-isolation: ∀ call db.* (c) =>
//   c.where.workspaceId = auth.workspaceId

// @invariant audit-complete: ∀ call db.*.update (u) =>
//   ∃ call db.auditLog.create (a) after u where
//     a.data.actorId = auth.userId ∧ a.data.resourceId = u.where.id

// @invariant no-secret-leak: ¬ tainted apiKey in call logger.*

// @invariant auth-gate: ∀ call db.*.update (u) =>
//   ∃ call permissions.check (p) before u where p.action = "write"

// @invariant read-only: ¬ ∃ call db.*.update (u)

// @invariant page-bounded: ∀ call db.*.findMany (f) => f.take = pageSize
```

Multiple invariants may share a tag. Each is proved independently — they are separate proof obligations, not conjoined. Shared tags group related properties for CI output and review: `soft-delete` might have both "all updates set deletedAt" and "no hard deletes", displayed together under one heading but verified as two distinct proofs.

### `@ensures <binding>.<pred>` (inline, at call site)

A semantic post-condition on the result of an external call, written as an inline comment in the function body. The annotation names the result binding and asserts a property that TypeScript's type system cannot express — typically a relationship between the result and the call's arguments.

Type-level information (field names, field types, nullability) is extracted automatically from TypeScript. `@ensures` is only needed for semantic properties beyond types:

```typescript
async function transferCredits(auth: Auth, fromId: string, toId: string, amount: number) {
  const fromAccount = await db.account.findUnique({ where: { id: fromId, workspaceId: auth.workspaceId } });
  // @ensures fromAccount.id = fromId
  // @ensures fromAccount.workspaceId = auth.workspaceId

  const toAccount = await db.account.findUnique({ where: { id: toId, workspaceId: auth.workspaceId } });
  // @ensures toAccount.id = toId
  // @ensures toAccount.balance ≥ 0
  // ...
}
```

These are the kinds of properties `@ensures` captures — a `findUnique` returns the record matching its `where` clause, a balance is non-negative, a list respects its `take` limit. TypeScript knows `fromAccount` has an `id: string` field; `@ensures` adds that `id = fromId`.

#### How TypeScript types become proof hypotheses

The extractor runs as a TypeScript compiler plugin with full access to the type checker. When it encounters a call like `const x = await db.account.findUnique(...)`, it resolves the return type to a concrete structural type and translates it into a `Val` shape predicate. The translation rules:

| TypeScript type                     | Val predicate                                                      |
| ----------------------------------- | ------------------------------------------------------------------ |
| `string`                            | `∃ s, v = Val.str s`                                               |
| `number`                            | `∃ n, v = Val.num n`                                               |
| `boolean`                           | `∃ b, v = Val.bool b`                                              |
| `null` / `undefined` / `void`       | `v = Val.none`                                                     |
| `T \| null`                         | `v = Val.none ∨ ⟦T⟧(v)`                                            |
| `T \| undefined`                    | `v = Val.none ∨ ⟦T⟧(v)`                                            |
| `T[]`                               | `∃ elems, v = Val.arr elems ∧ ∀ e ∈ elems, ⟦T⟧(e)`                 |
| `{ k₁: T₁, k₂: T₂ }`              | `∃ fields, v = Val.obj fields ∧ ⟦T₁⟧(lookup fields "k₁") ∧ ...`   |
| `{ k?: T }`                         | `... ∧ (lookup fields "k" = none ∨ ⟦T⟧(lookup fields "k"))`       |
| `"a" \| "b"` (string literal union) | `v = Val.str "a" ∨ v = Val.str "b"`                                |
| `A & B`                             | `⟦A⟧(v) ∧ ⟦B⟧(v)`                                                  |
| Generic / conditional types         | Resolved by TS type checker first, then translated structurally    |

The extractor only expands fields to the depth actually accessed in the function body — unused nested structure is left as `Val` (unconstrained). This keeps predicates manageable while providing exactly the hypotheses proofs need.

For example, given:

```typescript
type Account = { id: string; balance: number; workspaceId: string };
const fromAccount = await db.account.findUnique({ where: { id: fromId } });
// @ensures fromAccount.id = fromId
```

The generated Lean proof universally quantifies over `resultVal` with the combined constraint — the TS type predicate plus the `@ensures`:

```lean
∀ resultVal,
  -- Combined constraint: TS type + @ensures, under the same binder:
  (resultVal = Val.none ∨
   ∃ fields, resultVal = Val.obj fields ∧
     -- From TypeScript type (Account):
     (∃ s, fieldLookup fields "id" = some (Val.str s)) ∧
     (∃ n, fieldLookup fields "balance" = some (Val.num n)) ∧
     (∃ s, fieldLookup fields "workspaceId" = some (Val.str s)) ∧
     -- From @ensures (nested under the same ∃ fields):
     fieldLookup fields "id" = some (Val.str fromId)) →
  -- ... proof that invariants hold for all such resultVal
```

The TS type gives structure (field existence and types), `@ensures` gives semantics (field values and relationships). Together they constrain the universally quantified result tightly enough for proofs to close, without modeling callee internals.

`@ensures` annotations are trusted assumptions, not proved. If the external call violates them at runtime, the proof is sound over wrong assumptions. This is acceptable because the TS type predicates come from the type checker (already trusted by the codebase), and the `@ensures` properties typically follow from database schemas, API contracts, or query semantics — each a single human-readable line tied to a specific binding.

### The property grammar

```
prop :=
  | ∀ call <pattern> (c) => <pred>           -- all matching calls satisfy pred
  | ∃ call <pattern> (c) <order> => <pred>   -- at least one matching call
  | ¬ ∃ call <pattern>                       -- no matching calls exist
  | ¬ tainted <binding> in call <pattern>    -- binding never flows to call args
  | return <pred>                            -- return value property
  | <expr> = <expr>
  | <expr> ≠ <expr>
  | <expr> < <expr>  |  <expr> ≤ <expr>
  | <expr> > <expr>  |  <expr> ≥ <expr>
  | <expr> ∈ [<vals>]
  | <expr> starts_with <expr>
  | <expr> contains <field>
  | sum(<expr>) = <expr>                     -- sum over matching call args (all must have field)
  | <prop> ∧ <prop>
  | <prop> → <prop>

order :=
  | before <call-binding>                    -- this call appears earlier in trace
  | after <call-binding>                     -- this call appears later in trace
  | where <call-binding> inside <call-binding>  -- call nested within transaction

pattern := "db.*" | "db.user.findMany" | "logger.*" ...  -- string prefix matching

expr :=
  | <param>                                  -- function parameter: auth
  | <param>.<path>                           -- deep access: auth.workspaceId
  | c.<path>                                 -- call argument: c.where.workspaceId
  | c.result.<path>                          -- call result field: c.result.id
  | <literal>                                -- "admin", 100, true
  | now                                      -- current timestamp
  | <expr> ++ <expr>                         -- string concatenation
  | now + <duration>                         -- timestamp arithmetic
  | indexOf(<expr>, <expr>)                  -- position in list

duration := <num>d | <num>h | <num>m         -- days, hours, minutes
```

### What `@requires` can express

`@requires` asserts things the proof system can reason about — propositions with decidable truth over `Val`:

| ✅ Valid                          | ❌ Not valid                    |
| --------------------------------- | ------------------------------- |
| `amount > 0`                      | `amount is valid credit amount` |
| `fromId ≠ toId`                   | `email is valid email address`  |
| `role ∈ ["admin", "editor"]`      | `cron is valid cron expression` |
| `url starts_with "https://"`      | `token is non-expired JWT`      |
| `auth.workspaceId = workspace.id` | `uuid is valid UUID format`     |

Domain-specific validation ("valid email", "valid cron") is not a `@requires`. The function validates it internally and throws — the proof finds the guard from the `ite`+`throw` in the extracted JSCore₀ term automatically. No annotation needed.

---

## The Architecture

```
┌──────────────────────────────────────────────────────┐
│  @requires / @invariant / @ensures comments          │  ← Agent/Human writes, Human review
│  (humans review / collaborate with this)              │
├──────────────────────────────────────────────────────┤
│  TypeScript implementation                           │  ← Agent writes
│  (humans never read this)                            │
├──────────────────────────────────────────────────────┤
│  JSCore₀ term                                        │  ← Extractor produces
│  (deterministic compiler pass, ~1000 LOC, auditable) │
├──────────────────────────────────────────────────────┤
│  Lean 4 statements                                   │  ← Toolchain compiles
│  (from annotations, deterministic translation)       │
├──────────────────────────────────────────────────────┤
│  Lean 4 proofs                                       │  ← Agent writes
│  (untrusted — wrong proofs don't check)              │
├──────────────────────────────────────────────────────┤
│  Lean kernel verdict                                 │  ← Machine checks
│  (small, mathematically sound, decades of trust)     │
└──────────────────────────────────────────────────────┘
```

**Trust chain.** The human trusts their own annotations and the Lean kernel. The extractor is small and auditable (~1000 LOC). Everything in between is untrusted and verified. Wrong code produces a wrong JSCore₀ term that fails to prove. Wrong proofs don't check. The only path through CI is code that actually satisfies the invariant against a specification the human authored.

---

## JSCore₀: The Core Calculus

A Lean 4 language modeling how values flow from TypeScript function inputs to the arguments of external calls. Not a model of JavaScript semantics — a model of data flow to effect boundaries.

### Design principles

1. **Data flow is first-class.** The calculus tracks how values move from parameters through let-chains, field access, object construction, conditionals, and loops to call arguments.
2. **Effects are opaque boundaries.** External calls (`await db.findMany(...)`) are modeled as named operations with evaluated arguments. What happens inside is irrelevant — only what's passed matters.
3. **Call results are named.** Every call binds its result, making all values in the program traceable to their origin.
4. **Two binding levels.** `letConst` (immutable, into `Env`) vs `letMut`/`assign` (mutable, into `Store`). Function parameters are always `letConst` — they can never be affected by loop mutations.
5. **Extraction-friendly.** Every construct maps directly to a TypeScript AST pattern.

### Syntax

```lean
inductive Expr where
  -- Values
  | var      : String → Expr
  | strLit   : String → Expr
  | numLit   : Int → Expr
  | boolLit  : Bool → Expr
  | none     : Expr

  -- Bindings
  | letConst : String → Expr → Expr → Expr     -- const x = e; body
  | letMut   : String → Expr → Expr → Expr     -- let x = e; body (mutable)
  | assign   : String → Expr → Expr → Expr     -- x = e; body (reassign)

  -- Data flow
  | field    : Expr → String → Expr            -- e.f
  | obj      : List (String × Expr) → Expr     -- { k: e }
  | spread   : Expr → List (String × Expr) → Expr  -- { ...e, k: e }
  | arr      : List Expr → Expr                -- [e1, e2]
  | index    : Expr → Expr → Expr              -- e[i]
  | push     : String → Expr → Expr            -- arr.push(x) — only array mutation

  -- Control
  | seq      : Expr → Expr → Expr              -- e1; e2
  | ite      : Expr → Expr → Expr → Expr       -- if c then t else f
  | forOf    : String → Expr → Expr → Expr     -- for (const x of arr) { body }
  | whileLoop : Nat → Expr → Expr → Expr       -- while (c) { body }, Nat = fuel
  | break    : Expr
  | ret      : Expr → Expr                     -- return e (early return)

  -- Effects (the boundary)
  | call     : String                          -- target: "db.document.findMany"
             → List (String × Expr)           -- named arguments
             → String                         -- result binder
             → Expr                           -- body using result
             → Expr

  -- Errors
  | throw    : Expr → Expr
  | tryCatch : Expr → String → Expr → Expr

  -- Computation
  | binOp    : BinOp → Expr → Expr → Expr
  | unOp     : UnOp → Expr → Expr
```

**The critical design:** `call target args resultBinder body` means `const resultBinder = await target(args); body`. Every value in the program is traceable: from a parameter, from a literal, from a computation, or from the named result of a specific call. Nothing is anonymous.

### Values and evaluation state

```lean
inductive Val where
  | str  : String → Val
  | num  : Int → Val
  | bool : Bool → Val
  | none : Val
  | obj  : List (String × Val) → Val
  | arr  : List Val → Val

abbrev Env   := String → Option Val   -- immutable: const bindings and parameters
abbrev Store := String → Option Val   -- mutable: let bindings that get reassigned

-- Lookup: Store takes priority over Env
def lookup (env : Env) (store : Store) (x : String) : Option Val :=
  store x <|> env x
```

### The trace

Evaluation produces a `Result` carrying an `Outcome`, the final `Store`, and a `Trace` — the ordered list of external calls made:

```lean
structure CallRecord where
  target   : String                  -- "db.document.findMany"
  args     : List (String × Val)     -- evaluated argument values
  resultId : String                  -- name of result binder in program

inductive TraceEntry where
  | call     : CallRecord → TraceEntry
  | scopeEnd : CallRecord → TraceEntry  -- marks end of a scoped call (e.g. $transaction callback)

structure Result where
  outcome : Outcome                  -- ok Val | error Val | brk | returned Val
  store   : Store
  trace   : List TraceEntry

def eval : Env → Store → Expr → Result
```

All verification is about propositions over traces. Most trace queries operate over `CallRecord`s (extracted from `TraceEntry.call` entries); `scopeEnd` entries are only used by the `inside` predicate for transaction scoping.

### Key evaluation rules

**`letConst`** — value goes into `Env` (immutable):

```lean
| .letConst x e body =>
  let r1 := eval env store e
  match r1.outcome with
  | .ok v => let r2 := eval (env.set x v) r1.store body
              { r2 with trace := r1.trace ++ r2.trace }
  | _ => r1
```

**`letMut`/`assign`** — value goes into `Store` (mutable):

```lean
| .letMut x e body =>
  let r1 := eval env store e
  match r1.outcome with
  | .ok v => let r2 := eval env (r1.store.set x v) body
              { r2 with trace := r1.trace ++ r2.trace }
  | _ => r1
```

**`call`** — records to trace, binds result. External calls can either succeed or throw:

```lean
| .call target namedArgs resultBinder body =>
  let (argVals, argTrace) := evalNamedArgs env store namedArgs
  let cr := { target, args := argVals, resultId := resultBinder }
  -- Two cases: call succeeds or call throws
  -- Case 1: success — resultVal constrained by @ensures + TS type
  let r := eval (env.set resultBinder resultVal) store body
  { r with trace := argTrace ++ [cr] ++ r.trace }
  -- Case 2: call throws — trace records up to the failed call, body never executes
  { outcome := .error callError, store, trace := argTrace ++ [cr] }
```

Proofs must hold for both cases. In the success case, `resultVal` is universally quantified over all values satisfying the `@ensures` predicates and TypeScript return type. In the failure case, the body never executes — the trace contains only the calls evaluated before and including the failed call. This means invariants are proved over the trace *as actually produced*, including partial traces from call failures. An invariant like `∀ call db.*.update (u) => ...` holds vacuously if the update call never executes due to an earlier failure — the guarantee is: every call that *does appear* in the trace satisfies the property.

**`ite`** — both branches produce separate traces; only one executes:

```lean
| .ite cond thn els =>
  let rc := eval env store cond
  match rc.outcome with
  | .ok (.bool true)  => let r := eval env rc.store thn
                          { r with trace := rc.trace ++ r.trace }
  | .ok (.bool false) => let r := eval env rc.store els
                          { r with trace := rc.trace ++ r.trace }
  | _ => ...
```

**`forOf`** — trace is concatenation of all iteration traces. The loop variable goes into `Env` (immutable per-iteration binding, matching `for (const x of ...)`):

```lean
def evalForOf (env : Env) (store : Store) (x : String)
    (elems : List Val) (body : Expr) (prefix : List CallRecord) : Result :=
  elems.foldl (fun acc elem =>
    match acc.outcome with
    | .ok _ => let r := eval (env.set x elem) acc.store body
                { r with trace := acc.trace ++ r.trace }
    | _ => acc
  ) { outcome := .ok .none, store, trace := prefix }
```

### Desugaring: TypeScript → JSCore₀

The extractor is a TypeScript compiler plugin (~1000 LOC). Straightforward syntax-directed translation:

| TypeScript                          | JSCore₀                                                      |
| ----------------------------------- | ------------------------------------------------------------ |
| `const x = e; ...`                  | `letConst "x" ⟦e⟧ ⟦rest⟧`                                    |
| `let x = e; ...` (never reassigned) | `letConst "x" ⟦e⟧ ⟦rest⟧`                                    |
| `let x = e; ...` (reassigned)       | `letMut "x" ⟦e⟧ ⟦rest⟧`                                      |
| `x = e; ...`                        | `assign "x" ⟦e⟧ ⟦rest⟧`                                      |
| `const r = await m.fn({k:v}); ...`  | `call "m.fn" [("k",⟦v⟧)] "r" ⟦rest⟧`                         |
| `a.b.c`                             | `field (field (var "a") "b") "c"`                            |
| `{k1: e1, k2: e2}`                  | `obj [("k1",⟦e1⟧), ("k2",⟦e2⟧)]`                             |
| `{...e, k: e1}`                     | `spread ⟦e⟧ [("k",⟦e1⟧)]`                                    |
| `c ? t : f` / `if (c) {t} else {f}` | `ite ⟦c⟧ ⟦t⟧ ⟦f⟧`                                            |
| `for (const x of arr) { body }`     | `forOf "x" ⟦arr⟧ ⟦body⟧`                                     |
| `while (c) { body }`                | `whileLoop N ⟦c⟧ ⟦body⟧` (N = fuel)                          |
| `break`                             | `break`                                                      |
| `return e`                          | `ret ⟦e⟧`                                                    |
| `throw new Error(m)`                | `throw (strLit m)`                                           |
| `try { b } catch(x) { h }`          | `tryCatch ⟦b⟧ "x" ⟦h⟧`                                       |
| `arr.push(v)`                       | `push "arr" ⟦v⟧`                                             |
| `a?.b`                              | `ite (binOp .neq (var "a") none) (field (var "a") "b") none` |
| `` `${a}:${b}` ``                   | `binOp .strConcat ⟦a⟧ (binOp .strConcat (strLit ":") ⟦b⟧)`   |
| `const {x, y} = e; ...`             | `letConst "x" (field ⟦e⟧ "x") (letConst "y" ...)`            |
| `a && b`                            | `ite ⟦a⟧ ⟦b⟧ (boolLit false)`                                |
| `a \|\| b`                          | `letConst fresh ⟦a⟧ (ite (var fresh) (var fresh) ⟦b⟧)` (fresh binder) |
| `e1; e2`                            | `seq ⟦e1⟧ ⟦e2⟧`                                              |
| `xs.map(x => f(x))`                 | `letMut "__acc" (arr []) (forOf "x" ⟦xs⟧ (seq (push "__acc" ⟦f(x)⟧) (var "__acc")))` |
| `xs.filter(x => p(x))`              | `letMut "__acc" (arr []) (forOf "x" ⟦xs⟧ (ite ⟦p(x)⟧ (push "__acc" (var "x")) none))` |
| `xs.flatMap(x => f(x))`             | Same as `map` with inner array concatenation                 |
| `xs.forEach(x => f(x))`             | `forOf "x" ⟦xs⟧ ⟦f(x)⟧`                                     |
| `xs.find(x => p(x))`                | `forOf` + early `ret` on match                               |
| `xs.some(x => p(x))`                | `forOf` + early `ret (boolLit true)` on match                |
| `xs.every(x => p(x))`               | `forOf` + early `ret (boolLit false)` on fail                |
| `xs.reduce((acc, x) => f, init)`    | `letMut "__acc" ⟦init⟧ (forOf "x" ⟦xs⟧ (assign "__acc" ⟦f⟧ ...))` |
| Pure helper `f(args)`               | Inlined — body substituted at call site                      |
| `Promise.all([f(), g()])`           | Sequential: `call "f" ... (call "g" ...)` (see limitations)  |
| Async call `f(args)`                | `call "f" ...` — opaque effect boundary                      |

**While-loop fuel.** `whileLoop N cond body` executes `body` at most `N` times. The extractor chooses `N` from a `@fuel` annotation on the loop (`// @fuel 100`) or defaults to a configurable project-wide limit (default: 1000). When fuel runs out, evaluation produces `Outcome.error (Val.str "fuel exhausted")` — the function's trace up to that point is preserved, but the proof must account for this error path. In practice, invariants that hold per-iteration (proved via a loop invariant) are unaffected by the fuel bound — the fuel only matters for proofs about post-loop behavior. If no `@fuel` is provided and the default is insufficient, the proof fails with an explicit "fuel exhausted" path the agent cannot close, prompting it to add an annotation.

**Early returns.** `ret e` short-circuits evaluation: it produces `Outcome.returned v` which propagates upward through `seq`, `letConst`, `letMut`, etc. without executing subsequent code — but the trace up to that point is preserved. The extractor prefers restructuring simple early returns into `ite` when possible (`if (x) return y; rest` → `ite x y rest`), falling back to `ret` for complex cases (multiple early returns, returns inside loops, returns inside try/catch).

**Extractor rejects** (emits `sorry`, proof cannot close): closures over mutable state, `this`, dynamic property access `obj[expr]`, generators, `eval`/`Proxy`, `as any`. Rejection is correct behavior — unmodeled code is flagged unprovable.

**Known limitation: concurrency.** `Promise.all` is desugared to sequential calls. This is conservative — it proves invariants under a specific ordering, while the runtime may execute calls in any order. Per-call properties (ws-isolation, taint, membership checks) are unaffected since they hold regardless of trace ordering. However, ordering invariants (`before`/`after`) between calls inside a `Promise.all` may be provable under the sequential model but not actually guaranteed at runtime. In practice this rarely matters: ordering invariants typically express "check before mutate" patterns where the calls are already sequential. A future `par` construct could model `Promise.all` precisely by requiring proofs to hold for all valid interleavings.

---

## The Property System

### Trace queries

```lean
-- All calls whose target starts with pattern
def callsTo (trace : List CallRecord) (pattern : String) : List CallRecord :=
  trace.filter (fun c => c.target.startsWith pattern)

-- Value of a named argument, including nested paths ("where.workspaceId")
def argAtPath (c : CallRecord) (path : String) : Option Val := ...

-- Ordering: c1 appears before c2 in the trace
def before (trace : List CallRecord) (c1 c2 : CallRecord) : Prop :=
  ∃ i j, trace[i]? = some c1 ∧ trace[j]? = some c2 ∧ i < j

-- String predicates
def Val.startsWith : Val → Val → Prop
  | .str a, .str b => b.isPrefixOf a
  | _, _ => False

def Val.mem : Val → List Val → Prop := ...
def Val.contains : Val → String → Prop := ...

-- Aggregation: sum over a numeric field across matching calls.
-- Returns Option Int — none if any matching call lacks the field.
-- This forces proofs to establish that all matching calls have the
-- expected numeric field; a malformed call cannot be silently skipped.
def sumOver (trace : List CallRecord) (pattern : String)
    (path : String) : Option Int :=
  (callsTo trace pattern).foldlM (fun acc c =>
    match argAtPath c path with
    | some (.num n) => some (acc + n)
    | _ => none) 0

-- Nesting: c1 occurs within the scope of a transaction call c2.
-- The trace includes scope markers for calls that take a callback (e.g.
-- db.$transaction). The extractor emits a scopeEnd record when the
-- callback returns. "inside" means c1 appears between c2 and c2's
-- corresponding scopeEnd in the trace.
def inside (trace : List CallRecord) (c1 c2 : CallRecord) : Prop :=
  c2.target.startsWith "db.$transaction" ∧
  ∃ i j k, trace[i]? = some c2 ∧ trace[j]? = some c1 ∧
    trace[k]? = some (scopeEnd c2) ∧ i < j ∧ j < k

-- List position
def indexOf (v : Val) (vs : List Val) : Option Nat :=
  vs.findIdx? (· == v)
```

### Taint tracking (static)

```lean
-- Does expression e transitively depend on binding source?
-- Computed over the program AST — no runtime component.
def taintedBy (prog : Expr) (source : String) : Expr → Prop :=
  fun e => source ∈ transitiveUsedBindings prog e

-- No call matching pattern has any argument that depends on source
def notTaintedIn (prog : Expr) (source pattern : String) : Prop :=
  ∀ callExpr ∈ callExprsIn prog pattern,
    ∀ (_, argExpr) ∈ callExpr.namedArgs,
      ¬ taintedBy prog source argExpr
```

Taint is purely static — it walks the AST and follows binding chains. Sound for `letConst` (immutable) bindings, conservative for `letMut` (may over-approximate).

**Mutable binding over-approximation.** If a `letMut` variable is assigned the tainted source on _any_ code path, the analysis marks it tainted everywhere — even on branches where the assignment doesn't execute. This means a pattern like `let x = safe; if (rare) { x = secret; } logger.log(x)` marks `x` as tainted in the `logger.log` call, even though most paths are clean. This is sound (no false negatives) but may produce false positives, causing proof failures for code that is actually safe. The fix is always local: refactor the mutable variable into separate `const` bindings per branch, which the agent can do automatically when the taint proof fails.

The key taint soundness theorem:

```lean
theorem taint_soundness (prog : Expr) (source pattern : String)
    (h : notTaintedIn prog source pattern) :
    ∀ env env' store,
      (∀ x ≠ source, env x = env' x) →   -- env and env' differ only on source
      callsTo (eval env store prog).trace pattern =
      callsTo (eval env' store prog).trace pattern
-- Changing source's value doesn't change any matching call's arguments
```

### Compositionality — automatic, no annotation needed

When function `f` calls function `g`, and `g` has proved invariants, those invariants are automatically available as lemmas in `f`'s proof. The agent discovers them by inspecting the proof database for any `call` targets in `f`'s JSCore₀ term. No `@given` — the dependency is the call graph, already in the code.

The soundness theorem:

```lean
theorem invariant_composition
    -- g's invariant is proved
    (h_g : g_invariant_holds_for_g_body)
    -- f passes arguments satisfying g's @requires
    (h_args : f_satisfies_g_preconditions) :
    -- g's invariant holds over the g-originated sub-trace within f
    g_invariant_holds_in_f_trace
```

---

## Metatheory

Five theorems, proved once in Lean 4, used by all user proofs:

**1. Determinism.** `eval` is a Lean function — determinism is automatic.

**2. Trace compositionality.**

```lean
theorem seq_trace (env : Env) (store : Store) (e1 e2 : Expr) :
    (eval env store (.seq e1 e2)).trace =
      (eval env store e1).trace ++
      (eval env (eval env store e1).store e2).trace
```

**3. Env stability.** Values in `Env` (parameters, `const` bindings) are never affected by `Store` mutations. By construction, `letConst` names only enter `Env` and `letMut`/`assign` names only enter `Store` — the namespaces are disjoint. This makes workspace isolation proofs trivially stable through loops — `auth.workspaceId` is in `Env`; loop iterations mutate `Store`.

```lean
theorem env_stable (env : Env) (store store' : Store) (x : String)
    (h_env : env x = some v)
    (h_not_in_store : store x = none)
    (h_not_in_store' : store' x = none) :
    lookup env store x = lookup env store' x  -- = some v
```

The preconditions `store x = none` hold by construction for any `letConst`-bound or parameter-bound name — the evaluator never places such names in `Store`. A companion lemma establishes this invariant over evaluation:

```lean
theorem eval_preserves_store_disjointness (env : Env) (store : Store) (e : Expr)
    (x : String) (h : env x = some v) (h_s : store x = none) :
    (eval env store e).store x = none
```

**4. Loop invariant principle.**

```lean
theorem forOf_invariant (env : Env) (store : Store)
    (x : String) (elems : List Val) (body : Expr)
    (P : CallRecord → Prop) (I : Store → Prop)
    (h_init : I store)
    (h_step : ∀ elem store_i, I store_i →
      let r := eval (env.set x elem) store_i body
      I r.store ∧ ∀ c ∈ r.trace, P c) :
    (∀ c ∈ (evalForOf env store x elems body []).trace, P c) ∧
    I (evalForOf env store x elems body []).store
```

**5. Conditional coverage.** If the condition evaluates to a boolean and a property holds on both branches, it holds on the conditional. When the condition doesn't evaluate to a boolean (error or non-boolean value), evaluation produces an empty trace — the property holds vacuously.

```lean
theorem ite_covers (env : Env) (store : Store) (cond thn els : Expr)
    (P : List CallRecord → Prop)
    (h_cond : ∃ b, (eval env store cond).outcome = .ok (.bool b))
    (h_true  : (eval env store cond).outcome = .ok (.bool true)  → P (eval env store thn).trace)
    (h_false : (eval env store cond).outcome = .ok (.bool false) → P (eval env store els).trace) :
    P (eval env store (.ite cond thn els)).trace
```

This last theorem is what makes guard reasoning work: the `if (amount <= 0) throw` pattern means the "not thrown" branch has `amount > 0` as a hypothesis, available for any invariant proof that needs it. The `h_cond` precondition is typically discharged by `trace_simp` from the comparison's type.

---

## Custom Tactics

Agents use these to close proof goals mechanically:

- **`trace_simp`** — unfolds `eval`, simplifies the trace, reduces invariant checks to concrete value equality goals. Handles most data-flow invariants automatically via `simp` + `omega`.
- **`loop_inv I`** — applies `forOf_invariant` with store invariant `I`; reduces to per-iteration obligations which `trace_simp` typically closes.
- **`by_taint`** — walks the AST statically and proves taint-freedom by `decide`.
- **`by_ordering`** — computes trace indices and proves `before`/`after` properties.

### Why agents can write these proofs

This system assumes agents can generate Lean 4 proofs — a strong assumption, but a deliberately engineered one. These are not open-ended mathematical proofs. They are proofs about concrete program terms in a 7-constructor calculus, and they follow a small number of repeating patterns: unfold the trace, check each call record, appeal to env stability through a loop, or walk the AST for taint-freedom. The custom tactics above are designed to collapse most proof goals into one or two tactic invocations. In practice, a workspace-isolation proof for a function with no loops is just `by trace_simp`; with a loop, it's `by loop_inv (fun s => True) <;> trace_simp`. The agent doesn't need to invent proof strategies — it needs to recognize which pattern applies and supply the right store invariant. When a proof fails, Lean returns a precise goal state showing exactly what remains unproved, giving the agent a concrete target to fix rather than a vague error. And critically, wrong proofs are free — they simply don't check. The agent can iterate aggressively because the kernel is the judge, not a human reviewer.

---

## File Structure

```
jscore/
├── JSCore/
│   ├── Syntax.lean            -- Expr, BinOp, UnOp           (~100 LOC)
│   ├── Values.lean            -- Val, Env, Store, lookup      (~120 LOC)
│   ├── Eval.lean              -- eval, evalForOf, evalWhile   (~600 LOC)
│   ├── Trace.lean             -- CallRecord, callsTo, before  (~150 LOC)
│   ├── Properties.lean        -- FnDecl, Invariant, requires  (~200 LOC)
│   ├── Taint.lean             -- taintedBy, notTaintedIn      (~200 LOC)
│   ├── StringPredicates.lean  -- startsWith, contains, mem   (~80 LOC)
│   ├── Metatheory/
│   │   ├── TraceComposition.lean                              (~150 LOC)
│   │   ├── EnvStability.lean                                  (~100 LOC)
│   │   ├── LoopInvariant.lean                                 (~200 LOC)
│   │   ├── ConditionalCoverage.lean                           (~120 LOC)
│   │   ├── Composition.lean                                   (~250 LOC)
│   │   └── TaintSoundness.lean                                (~200 LOC)
│   └── Tactics.lean                                           (~400 LOC)
├── JSCore.lean
└── lakefile.lean
                                              Total: ~2,870 LOC
```

---

## Twenty Real Invariant Examples

```typescript
// @requires amount > 0
// @requires fromAccountId ≠ toAccountId
// @invariant ws-isolation: ∀ call db.* (c) => c.where.workspaceId = auth.workspaceId
// @invariant conservation: ∀ call db.account.update (u) =>
//   sum(u.data.balance.increment) = 0
async function transferCredits(
  auth: Auth,
  fromAccountId: string,
  toAccountId: string,
  amount: number,
);

// @invariant ws-isolation: ∀ call db.* (c) => c.where.workspaceId = auth.workspaceId
// @invariant no-secret-leak: ¬ tainted apiKey in call logger.*
// @invariant no-secret-leak: ¬ tainted apiKey in call analytics.*
async function rotateApiKey(auth: Auth, keyId: string);

// @requires recipients.length ≤ 50
// @invariant ws-isolation: ∀ call db.* (c) => c.where.workspaceId = auth.workspaceId
// @invariant fan-out-bound: ∀ call email.send (e) => e.to ∈ recipients
// @invariant no-bcc-leak: ¬ tainted recipients in call email.send.bcc
async function sendBulkNotification(
  auth: Auth,
  recipients: string[],
  templateId: string,
);

// @invariant ws-isolation: ∀ call storage.* (c) => c.bucket = auth.workspaceId
// @invariant path-scoped: ∀ call storage.put (c) =>
//   c.key starts_with auth.workspaceId ++ "/"
async function uploadAttachment(auth: Auth, file: Upload, parentDocId: string);

// @invariant ws-isolation: ∀ call db.* (c) => c.where.workspaceId = auth.workspaceId
// @invariant soft-delete: ∀ call db.*.update (u) => u.data.deletedAt ≠ none
// @invariant soft-delete: ¬ ∃ call db.*.delete (d)
async function archiveProject(auth: Auth, projectId: string);

// @invariant ws-isolation: ∀ call db.* (c) => c.where.workspaceId = auth.workspaceId
// @invariant auth-gate: ∀ call db.*.update (u) =>
//   ∃ call permissions.check (p) before u where p.action = "write"
// @invariant auth-gate: ∀ call db.*.delete (d) =>
//   ∃ call permissions.check (p) before d where p.action = "delete"
async function updateDocument(auth: Auth, docId: string, patch: DocumentPatch);

// @requires query.length ≤ 500
// @invariant ws-isolation: ∀ call db.* (c) => c.where.workspaceId = auth.workspaceId
// @invariant ws-isolation: ∀ call searchIndex.* (c) => c.index = auth.workspaceId
// @invariant result-bounded: return.items.length ≤ limit
async function searchDocuments(
  auth: Auth,
  query: string,
  limit: number,
  cursor?: string,
);

// @invariant rate-limited: ∀ call llm.complete (l) =>
//   ∃ call rateLimiter.check (r) before l where r.key = "llm:" ++ auth.workspaceId
// @invariant approved-model: ∀ call llm.complete (l) =>
//   l.model ∈ ["gpt-4o", "claude-sonnet"]
// @invariant no-pii-leak: ¬ tainted auth.email in call llm.complete
async function generateSummary(auth: Auth, docId: string);

// @invariant ws-isolation: ∀ call db.* (c) => c.where.workspaceId = auth.workspaceId
// @invariant audit-complete: ∀ call db.member.update (u) =>
//   ∃ call db.auditLog.create (a) after u where
//     a.data.actorId = auth.userId ∧ a.data.targetId = u.where.id
// @invariant no-self-promote: ∀ call db.member.update (u) =>
//   u.where.id = auth.userId → u.data.role ≠ "admin"
async function changeMemberRole(auth: Auth, memberId: string, newRole: Role);

// @invariant ws-isolation: ∀ call db.* (c) => c.where.workspaceId = auth.workspaceId
// @invariant signed: ∀ call http.post (h) => h.headers contains "X-Signature"
// @invariant https-only: ∀ call http.post (h) => h.url starts_with "https://"
// @invariant record-first: ∀ call http.post (h) =>
//   ∃ call db.webhookEvent.create (w) before h where w.data.url = h.url
async function deliverWebhook(
  auth: Auth,
  event: DomainEvent,
  endpoint: WebhookEndpoint,
);

// @invariant ws-isolation: ∀ call db.* (c) => c.where.workspaceId = auth.workspaceId
// @invariant idempotent: ∀ call db.*.update (u) =>
//   ∃ call db.webhookEvent.findUnique (f) before u
//     where f.result.processedAt = none
async function handleStripeWebhook(payload: StripePayload, signature: string);

// @invariant ws-isolation: ∀ call db.* (c) => c.where.workspaceId = auth.workspaceId
// @invariant cache-scoped: ∀ call cache.* (c) =>
//   c.key starts_with auth.workspaceId ++ ":"
// @invariant cache-invalidated: ∀ call db.*.update (u) =>
//   ∃ call cache.invalidate (i) after u
//     where i.pattern starts_with auth.workspaceId
async function updateProjectSettings(
  auth: Auth,
  projectId: string,
  settings: Partial<Settings>,
);

// @requires targetEnv ∈ ["staging", "production"]
// @invariant approval-gate: ∀ call deploy.push (d) =>
//   d.env = "production" →
//     ∃ call approval.verify (a) before d
// @invariant tagged: ∀ call deploy.push (d) =>
//   d.metadata.commitSha = commitSha
async function deployService(
  auth: Auth,
  serviceName: string,
  commitSha: string,
  targetEnv: string,
);

// @invariant ws-isolation: ∀ call db.* (c) => c.where.workspaceId = auth.workspaceId
// @invariant consistent-ordering: ∀ call db.post.findMany (f) =>
//   f.orderBy = "createdAt_desc"
// @invariant page-bounded: ∀ call db.post.findMany (f) => f.take = pageSize
async function listPosts(auth: Auth, pageSize: number, cursor?: string);

// @invariant ws-isolation: ∀ call db.* (c) => c.where.workspaceId = auth.workspaceId
// @invariant batch-bounded: ∀ call db.*.createMany (c) => c.data.length ≤ 1000
// @invariant transactional: ∀ call db.*.createMany (c) =>
//   ∃ call db.$transaction (t) where c inside t
async function bulkImportRows(auth: Auth, rows: ImportRow[]);

// @invariant ws-isolation: ∀ call db.* (c) => c.where.workspaceId = auth.workspaceId
// @invariant expiry-set: ∀ call db.invitation.create (c) =>
//   c.data.expiresAt > now ∧ c.data.expiresAt ≤ now + 7d
// @invariant no-self-invite: ∀ call db.invitation.create (c) =>
//   c.data.email ≠ auth.email
async function inviteMember(auth: Auth, email: string, role: Role);

// @requires tasks.length ≤ 20
// @invariant ws-isolation: ∀ call db.* (c) => c.where.workspaceId = auth.workspaceId
// @invariant scope-limited: ∀ call db.task.update (u) =>
//   u.where.projectId = projectId
// @invariant ordering-preserved: ∀ call db.task.update (u) =>
//   u.data.position = indexOf(u.where.id, tasks)
async function reorderTasks(auth: Auth, projectId: string, tasks: string[]);

// @invariant ws-isolation: ∀ call db.* (c) => c.where.workspaceId = auth.workspaceId
// @invariant read-only: ¬ ∃ call db.*.update (u)
// @invariant read-only: ¬ ∃ call db.*.create (c)
// @invariant read-only: ¬ ∃ call db.*.delete (d)
async function exportWorkspaceData(auth: Auth, format: "json" | "csv");

// @invariant ws-isolation: ∀ call db.* (c) => c.where.workspaceId = token.workspaceId
// @invariant user-scoped: ∀ call db.* (c) => c.where.userId = token.userId
async function handleApiRequest(
  token: ApiToken,
  workspaceId: string,
  action: ApiAction,
);

// @requires actions.length ≤ 20
// @invariant ws-isolation: ∀ call db.* (c) => c.where.workspaceId = auth.workspaceId
// @invariant no-dangerous-actions: ∀ call scheduler.register (s) =>
//   s.action ∈ ["sync", "report", "cleanup"]
// @invariant frequency-bounded: ∀ call scheduler.register (s) =>
//   s.minIntervalSeconds ≥ 300
async function createScheduledJob(
  auth: Auth,
  schedule: CronSchedule,
  action: JobAction,
);
```

---

## The Developer Experience

### Writing a new function

Agent generates implementation. Agent proposes invariant comments. Human reads the comments — typically 15–30 seconds:

```typescript
// @requires amount > 0
// @invariant ws-isolation: ∀ call db.* (c) => c.where.workspaceId = auth.workspaceId
// @invariant no-secret-leak: ¬ tainted paymentToken in call logger.*
// @invariant audit-complete: ∀ call db.payment.create (p) =>
//   ∃ call db.auditLog.create (a) after p where a.data.userId = auth.userId
async function processPayment(auth: Auth, amount: number, paymentToken: string);
```

Human reads four lines. _"Payment processing scoped to workspace, token doesn't go to logs, every payment has an audit entry."_ Approved or amended. Implementation never read.

### CI output

```
$ npx jscore verify

  processPayment
    ws-isolation     ✓  proved [Lean, 180ms]
    no-secret-leak   ✓  proved [Lean, 95ms]
    audit-complete   ✓  proved [Lean, 340ms]
    @requires: amount > 0   → caller must satisfy

  transferCredits
    ws-isolation     ✓  proved [Lean, 160ms]
                          (uses processPayment.ws-isolation as lemma)
    conservation     ✓  proved [Lean, 220ms]
    @requires: amount > 0   ✓  satisfied — proved from caller site
    @requires: fromId ≠ toId  → caller must satisfy

  Proof graph:
    transferCredits → processPayment → [leaf]

  12 functions · 31 invariants · 0 failures
  Lean kernel: all proofs verified
```

### Extraction coverage

The extractor emits `sorry` for constructs it cannot model. A coverage report shows which functions extracted cleanly and which contain unmodeled code:

```
$ npx jscore coverage

  src/payments/
    transferCredits        ✓  fully extracted
    processPayment         ✓  fully extracted
    refundPayment          ✗  sorry at line 42: closure over mutable state
    calculateFees          ✓  fully extracted (pure, inlined at call sites)

  src/webhooks/
    deliverWebhook         ✓  fully extracted
    handleStripeWebhook    ✓  fully extracted
    retryWithBackoff       ✗  sorry at line 18: generator function

  Coverage: 14/17 functions fully extracted (82%)
  Unverified: 3 functions contain sorry — invariants cannot be proved
```

Functions with `sorry` are not silently ignored — their invariants appear as failures in `npx jscore verify`. The coverage report helps teams identify which code patterns need refactoring to become verifiable.

### Reviewing a behavioral change

Agent adds overdraft support. Review surface:

```diff
  // @requires amount > 0
- // @invariant ws-isolation: ∀ call db.* (c) => c.where.workspaceId = auth.workspaceId
+ // @requires overdraftLimit ≥ 0
+ // @invariant ws-isolation: ∀ call db.* (c) => c.where.workspaceId = auth.workspaceId
+ // @invariant overdraft-bounded: ∀ call db.account.update (u) =>
+   u.data.balance ≥ -overdraftLimit
  async function transferCredits(auth, fromId, toId, amount, overdraftLimit)
```

Two lines added. Human decides whether overdraft is an acceptable change to the behavioral contract — not whether 200 lines of implementation are correct. Everything outside the annotation diff is machine-verified as behaviorally unchanged.

---

## What This Changes

| Human does                               | Machine does                                      |
| ---------------------------------------- | ------------------------------------------------- |
| Writes `@invariant` in ~10 words         | Extracts JSCore₀ term, compiles to Lean statement |
| Approves or adjusts annotation lines     | Generates and checks Lean proof                   |
| Reviews annotation diffs on changes      | Verifies behavioral equivalence outside the diff  |
| Expresses intent in constrained notation | Proves all the tedious data-flow chains           |

**The human's irreducible contribution:** deciding whether the invariant is the right one. That judgment cannot be automated. Everything else can.
