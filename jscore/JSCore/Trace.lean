/-
  JSCore₀ Trace — CallRecord, TraceEntry, Outcome, Result, and trace queries.
-/
import JSCore.Values

namespace JSCore

structure CallRecord where
  target   : List String   -- pre-split segments: ["db", "task", "update"]
  args     : List (String × Val)
  resultId : String
  deriving Repr, BEq, DecidableEq

inductive TraceEntry where
  | call     : CallRecord → TraceEntry
  | scopeEnd : CallRecord → TraceEntry
  deriving Repr, BEq, DecidableEq

inductive Outcome where
  | ok       : Val → Outcome
  | error    : Val → Outcome
  | brk      : Outcome
  | returned : Val → Outcome
  deriving Repr, BEq

structure Result where
  outcome : Outcome
  store   : Store
  trace   : List TraceEntry

-- Extract CallRecords from trace (only .call entries)
def extractCalls (trace : List TraceEntry) : List CallRecord :=
  trace.filterMap fun e =>
    match e with
    | .call cr => some cr
    | .scopeEnd _ => Option.none

-- Does target match pattern? Both are pre-split segment lists.
-- "*" matches any single segment; a trailing "*" matches 1+ remaining segments.
-- Examples: ["db","projects","findMany"] matches ["db","*"] and
-- ["db","*","findMany"] but not ["db","*","update"].
def matchesPattern : (target pattern : List String) → Bool
  | _ :: _, ["*"] => true
  | t :: ts, p :: ps => (p == "*" || t == p) && matchesPattern ts ps
  | [], [] => true
  | _, _ => false

-- All calls whose target matches the pattern
def callsTo (trace : List TraceEntry) (pattern : List String) : List CallRecord :=
  (extractCalls trace).filter (fun c => matchesPattern c.target pattern)

-- Value of a named argument (supports simple top-level lookup)
def argLookup (args : List (String × Val)) (name : String) : Option Val :=
  fieldLookup args name

-- Value at a pre-split path inside a Val. Paths are List String so proofs
-- never reason about String.splitOn (the extractor splits at emission time).
def valAt : Val → List String → Option Val
  | v, [] => some v
  | .obj fields, seg :: rest =>
    (match fieldLookup fields seg with
     | some v => valAt v rest
     | Option.none => Option.none)
  | _, _ :: _ => Option.none

-- Value of a named argument at a pre-split path.
def argAt (c : CallRecord) : List String → Option Val
  | [] => Option.none
  | name :: rest =>
    match argLookup c.args name with
    | some v => valAt v rest
    | Option.none => Option.none

-- Dotted-path convenience wrapper (kept for backwards compatibility; prefer
-- `argAt` with explicit segments in generated statements and proofs).
def argAtPath (c : CallRecord) (path : String) : Option Val :=
  argAt c (path.splitOn ".")

-- Ordering: c1 appears before c2 in the trace
def before (trace : List TraceEntry) (c1 c2 : CallRecord) : Prop :=
  ∃ i j, trace.get? i = some (.call c1) ∧ trace.get? j = some (.call c2) ∧ i < j

-- c1 occurs inside the scope of a transaction call c2
def inside (trace : List TraceEntry) (c1 c2 : CallRecord) : Prop :=
  matchesPattern c2.target ["db", "$transaction*"] ∧
  ∃ i j k, trace.get? i = some (.call c2) ∧
    trace.get? j = some (.call c1) ∧
    trace.get? k = some (.scopeEnd c2) ∧
    i < j ∧ j < k

end JSCore
