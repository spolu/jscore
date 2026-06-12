/-
  JSCore₀ Metatheory — argAt / fieldLookup computation lemmas.

  With paths as pre-split `List String` (extractor emits segments), a goal
  like `argAt cr ["where", "projectId"] = some pid` closes by plain `simp`
  using these lemmas — no String.splitOn reasoning, no compiled-decision
  procedures, no per-example helper lemmas. The key-mismatch side conditions
  are discharged by the `:= by decide` autoParams (cheap kernel String
  equality).
-/
import JSCore.Trace

namespace JSCore

@[simp] theorem fieldLookup_nil {k : String} :
    fieldLookup ([] : List (String × Val)) k = Option.none := rfl

@[simp] theorem fieldLookup_cons_self {k : String} {v : Val}
    {rest : List (String × Val)} :
    fieldLookup ((k, v) :: rest) k = some v := by
  simp [fieldLookup, List.find?]

@[simp] theorem fieldLookup_cons_ne {k' k : String} {v : Val}
    {rest : List (String × Val)}
    (h : (k' == k) = false := by decide) :
    fieldLookup ((k', v) :: rest) k = fieldLookup rest k := by
  simp [fieldLookup, List.find?, h]

@[simp] theorem argLookup_eq_fieldLookup {args : List (String × Val)}
    {name : String} :
    argLookup args name = fieldLookup args name := rfl

@[simp] theorem valAt_nil {v : Val} : valAt v [] = some v := by
  cases v <;> rfl

@[simp] theorem valAt_obj_cons {fields : List (String × Val)}
    {seg : String} {rest : List String} :
    valAt (.obj fields) (seg :: rest) =
    (match fieldLookup fields seg with
     | some v => valAt v rest
     | Option.none => Option.none) := rfl

@[simp] theorem argAt_nil {c : CallRecord} : argAt c [] = Option.none := rfl

@[simp] theorem argAt_cons {c : CallRecord} {name : String} {rest : List String} :
    argAt c (name :: rest) =
    (match argLookup c.args name with
     | some v => valAt v rest
     | Option.none => Option.none) := rfl

end JSCore
