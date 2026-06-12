/-
  JSCore₀ Properties — sumOver, indexOf, matchesPattern, and trace property helpers.
-/
import JSCore.Trace

namespace JSCore

-- Sum over a numeric field across matching calls.
-- Returns Option Int — none if any matching call lacks the field.
def sumOver (trace : List TraceEntry) (pattern : List String) (path : String) : Option Int :=
  (callsTo trace pattern).foldlM (fun acc c =>
    match argAtPath c path with
    | some (.num n) => some (acc + n)
    | _ => .none) 0

-- Position of a value in a list
def indexOf (v : Val) (vs : List Val) : Option Nat :=
  vs.findIdx? (· == v)

-- Check that all matching calls satisfy a predicate
def allCallsSatisfy (trace : List TraceEntry) (pattern : List String)
    (P : CallRecord → Prop) [DecidablePred P] : Bool :=
  (callsTo trace pattern).all (fun c => decide (P c))

-- Check that no matching calls exist
def noCallsExist (trace : List TraceEntry) (pattern : List String) : Prop :=
  callsTo trace pattern = []

instance (trace : List TraceEntry) (pattern : List String) :
    Decidable (noCallsExist trace pattern) :=
  inferInstanceAs (Decidable (callsTo trace pattern = []))

end JSCore
