/-
  JSCore₀ Syntax — the core calculus for modeling TypeScript data flow.
  All 26 expression constructors from the proposal.
-/

namespace JSCore

inductive BinOp where
  | eq | neq | lt | le | gt | ge
  | add | sub | mul | div | mod
  | strConcat
  deriving Repr, BEq, DecidableEq

inductive UnOp where
  | not | neg
  deriving Repr, BEq, DecidableEq

inductive Expr where
  -- Values
  | var      : String → Expr
  | strLit   : String → Expr
  | numLit   : Int → Expr
  | boolLit  : Bool → Expr
  | none     : Expr
  -- Bindings
  | letConst : String → Expr → Expr → Expr
  | letMut   : String → Expr → Expr → Expr
  | assign   : String → Expr → Expr → Expr
  -- Data flow
  | field    : Expr → String → Expr
  | obj      : List (String × Expr) → Expr
  | spread   : Expr → List (String × Expr) → Expr
  | arr      : List Expr → Expr
  | index    : Expr → Expr → Expr
  | push     : String → Expr → Expr
  -- Control
  | seq      : Expr → Expr → Expr
  | ite      : Expr → Expr → Expr → Expr
  | forOf    : String → Expr → Expr → Expr
  | whileLoop : Nat → Expr → Expr → Expr
  | «break»  : Expr
  | ret      : Expr → Expr
  -- Effects. The target is pre-split into segments ("db.task.update" →
  -- ["db", "task", "update"]) so pattern matching never needs String.splitOn
  -- and stays kernel-decidable.
  | call     : List String → List (String × Expr) → String → Expr → Expr
  -- Errors
  | throw    : Expr → Expr
  | tryCatch : Expr → String → Expr → Expr
  -- Computation
  | binOp    : BinOp → Expr → Expr → Expr
  | unOp     : UnOp → Expr → Expr
  deriving Repr, BEq

end JSCore
