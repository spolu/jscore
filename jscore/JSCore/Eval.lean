/-
  JSCore₀ Evaluator — eval with global fuel parameter.
  Structural recursion on `fuel`.

  List-shaped sub-evaluations (object fields, array elements, call arguments,
  forOf iterations) use top-level helper functions taking an evaluation closure
  (same pattern as evalWhileAux). All of them SHORT-CIRCUIT on the first non-ok
  outcome — a throw inside an object literal, array literal, or argument list
  aborts evaluation of the enclosing expression, and a call whose argument
  evaluation fails is NOT recorded in the trace (matching JS semantics, where
  the callee is never invoked).
-/
import JSCore.Trace

namespace JSCore

def mkResult (o : Outcome) (s : Store) (t : List TraceEntry) : Result :=
  { outcome := o, store := s, trace := t }

def evalBinOp (op : BinOp) (v1 v2 : Val) : Outcome :=
  match op, v1, v2 with
  | .eq, a, b => .ok (.bool (a == b))
  | .neq, a, b => .ok (.bool (a != b))
  | .lt, .num a, .num b => .ok (.bool (a < b))
  | .le, .num a, .num b => .ok (.bool (a ≤ b))
  | .gt, .num a, .num b => .ok (.bool (a > b))
  | .ge, .num a, .num b => .ok (.bool (a ≥ b))
  | .add, .num a, .num b => .ok (.num (a + b))
  | .sub, .num a, .num b => .ok (.num (a - b))
  | .mul, .num a, .num b => .ok (.num (a * b))
  | .div, .num _, .num 0 => .error (.str "division by zero")
  | .div, .num a, .num b => .ok (.num (a / b))
  | .mod, .num _, .num 0 => .error (.str "modulo by zero")
  | .mod, .num a, .num b => .ok (.num (a % b))
  | .strConcat, .str a, .str b => .ok (.str (a ++ b))
  | _, _, _ => .error (.str "type error in binop")

def evalUnOp (op : UnOp) (v : Val) : Outcome :=
  match op, v with
  | .not, .bool b => .ok (.bool (!b))
  | .neg, .num n => .ok (.num (-n))
  | _, _ => .error (.str "type error in unop")

-- WhileLoop as a separate function with Nat recursion on loopFuel.
-- Takes evalBody and evalCond as function arguments (will be partially applied).
def evalWhileAux (loopFuel : Nat) (evalCond evalBody : Store → Result)
    (store : Store) (accTrace : List TraceEntry) : Result :=
  match loopFuel with
  | 0 => mkResult (.error (.str "fuel exhausted")) store accTrace
  | loopFuel' + 1 =>
    let rc := evalCond store
    match rc.outcome with
    | .ok (.bool true) =>
      let rb := evalBody rc.store
      match rb.outcome with
      | .ok _ => evalWhileAux loopFuel' evalCond evalBody rb.store
          (accTrace ++ rc.trace ++ rb.trace)
      | .brk => mkResult (.ok .none) rb.store (accTrace ++ rc.trace ++ rb.trace)
      | .returned v => mkResult (.returned v) rb.store (accTrace ++ rc.trace ++ rb.trace)
      | _ => mkResult rb.outcome rb.store (accTrace ++ rc.trace ++ rb.trace)
    | .ok (.bool false) => mkResult (.ok .none) rc.store (accTrace ++ rc.trace)
    | .ok _ => mkResult (.error (.str "while condition not boolean")) rc.store (accTrace ++ rc.trace)
    | _ => mkResult rc.outcome rc.store (accTrace ++ rc.trace)

/-- Evaluate named expressions (object fields / call arguments) left-to-right.
    Returns the accumulated `(key, value)` pairs and a `Result` whose outcome is
    `.ok .none` if every expression succeeded. Short-circuits on the first
    non-ok outcome: the failing outcome/store/trace are returned and the
    remaining expressions are NOT evaluated. -/
def evalPairsAux (evalFn : Store → Expr → Result) :
    List (String × Expr) → Store → List TraceEntry → List (String × Val) →
    List (String × Val) × Result
  | [], store, accTrace, accVals =>
    (accVals, mkResult (.ok .none) store accTrace)
  | (k, e) :: rest, store, accTrace, accVals =>
    let r := evalFn store e
    match r.outcome with
    | .ok v => evalPairsAux evalFn rest r.store (accTrace ++ r.trace) (accVals ++ [(k, v)])
    | _ => (accVals, mkResult r.outcome r.store (accTrace ++ r.trace))

/-- Evaluate array element expressions left-to-right.
    Same short-circuit discipline as `evalPairsAux`. -/
def evalElemsAux (evalFn : Store → Expr → Result) :
    List Expr → Store → List TraceEntry → List Val →
    List Val × Result
  | [], store, accTrace, accVals =>
    (accVals, mkResult (.ok .none) store accTrace)
  | e :: rest, store, accTrace, accVals =>
    let r := evalFn store e
    match r.outcome with
    | .ok v => evalElemsAux evalFn rest r.store (accTrace ++ r.trace) (accVals ++ [v])
    | _ => (accVals, mkResult r.outcome r.store (accTrace ++ r.trace))

/-- Run a forOf body over a list of elements. `break` stops the loop (yielding
    `.ok .none`), `return` and errors stop it propagating their outcome —
    matching JS `for...of` semantics. -/
def evalForOfAux (evalBody : Val → Store → Result) :
    List Val → Store → List TraceEntry → Result
  | [], store, accTrace => mkResult (.ok .none) store accTrace
  | elem :: rest, store, accTrace =>
    let r := evalBody elem store
    match r.outcome with
    | .ok _ => evalForOfAux evalBody rest r.store (accTrace ++ r.trace)
    | .brk => mkResult (.ok .none) r.store (accTrace ++ r.trace)
    | .returned v => mkResult (.returned v) r.store (accTrace ++ r.trace)
    | .error e => mkResult (.error e) r.store (accTrace ++ r.trace)

-- Main evaluator with global fuel
def eval (fuel : Nat) (env : Env) (store : Store) (e : Expr) : Result :=
  match fuel with
  | 0 => mkResult (.error (.str "fuel exhausted")) store []
  | fuel' + 1 =>
    match e with
    | .var x =>
      match lookup env store x with
      | some v => mkResult (.ok v) store []
      | Option.none => mkResult (.error (.str s!"undefined variable: {x}")) store []

    | .strLit s => mkResult (.ok (.str s)) store []
    | .numLit n => mkResult (.ok (.num n)) store []
    | .boolLit b => mkResult (.ok (.bool b)) store []
    | .none => mkResult (.ok .none) store []

    | .letConst x e body =>
      let r1 := eval fuel' env store e
      match r1.outcome with
      | .ok v =>
        let r2 := eval fuel' (env.set x v) r1.store body
        mkResult r2.outcome r2.store (r1.trace ++ r2.trace)
      | _ => r1

    | .letMut x e body =>
      let r1 := eval fuel' env store e
      match r1.outcome with
      | .ok v =>
        let r2 := eval fuel' env (r1.store.set x v) body
        mkResult r2.outcome r2.store (r1.trace ++ r2.trace)
      | _ => r1

    | .assign x e body =>
      let r1 := eval fuel' env store e
      match r1.outcome with
      | .ok v =>
        let r2 := eval fuel' env (r1.store.set x v) body
        mkResult r2.outcome r2.store (r1.trace ++ r2.trace)
      | _ => r1

    | .field e fname =>
      let r := eval fuel' env store e
      match r.outcome with
      | .ok (.obj fields) =>
        match fieldLookup fields fname with
        | some v => mkResult (.ok v) r.store r.trace
        | Option.none => mkResult (.ok .none) r.store r.trace
      | .ok _ => mkResult (.ok .none) r.store r.trace
      | _ => r

    | .obj pairs =>
      let pr := evalPairsAux (eval fuel' env) pairs store [] []
      match pr.2.outcome with
      | .ok _ => mkResult (.ok (.obj pr.1)) pr.2.store pr.2.trace
      | _ => pr.2

    | .spread base overrides =>
      let rb := eval fuel' env store base
      match rb.outcome with
      | .ok (.obj baseFields) =>
        let pr := evalPairsAux (eval fuel' env) overrides rb.store rb.trace []
        match pr.2.outcome with
        | .ok _ =>
          let merged := pr.1.foldl (fun acc kv => fieldSet acc kv.1 kv.2) baseFields
          mkResult (.ok (.obj merged)) pr.2.store pr.2.trace
        | _ => pr.2
      | .ok _ => mkResult (.error (.str "spread on non-object")) rb.store rb.trace
      | _ => rb

    | .arr exprs =>
      let er := evalElemsAux (eval fuel' env) exprs store [] []
      match er.2.outcome with
      | .ok _ => mkResult (.ok (.arr er.1)) er.2.store er.2.trace
      | _ => er.2

    | .index e idx =>
      let re := eval fuel' env store e
      match re.outcome with
      | .ok (.arr elems) =>
        let ri := eval fuel' env re.store idx
        match ri.outcome with
        | .ok (.num i) =>
          let idx' := if i ≥ 0 then i.toNat else 0
          match elems.get? idx' with
          | some v => mkResult (.ok v) ri.store (re.trace ++ ri.trace)
          | Option.none => mkResult (.ok .none) ri.store (re.trace ++ ri.trace)
        | .ok _ => mkResult (.error (.str "index not a number")) ri.store (re.trace ++ ri.trace)
        | _ => mkResult ri.outcome ri.store (re.trace ++ ri.trace)
      | .ok _ => mkResult (.error (.str "index on non-array")) re.store re.trace
      | _ => re

    | .push arrName valExpr =>
      let rv := eval fuel' env store valExpr
      match rv.outcome with
      | .ok v =>
        -- Store-only lookup: pushed names must be letMut-bound. Pushing an
        -- Env-bound (letConst) array errors rather than silently shadowing it
        -- in Store, preserving Env/Store disjointness. The extractor
        -- classifies pushed arrays as letMut even when declared `const`.
        match rv.store arrName with
        | some (.arr elems) =>
          let newArr := Val.arr (elems ++ [v])
          mkResult (.ok newArr) (rv.store.set arrName newArr) rv.trace
        | _ => mkResult (.error (.str s!"push on non-array: {arrName}")) rv.store rv.trace
      | _ => rv

    | .seq e1 e2 =>
      let r1 := eval fuel' env store e1
      match r1.outcome with
      | .ok _ =>
        let r2 := eval fuel' env r1.store e2
        mkResult r2.outcome r2.store (r1.trace ++ r2.trace)
      | _ => r1

    | .ite cond thn els =>
      let rc := eval fuel' env store cond
      match rc.outcome with
      | .ok (.bool true) =>
        let r := eval fuel' env rc.store thn
        mkResult r.outcome r.store (rc.trace ++ r.trace)
      | .ok (.bool false) =>
        let r := eval fuel' env rc.store els
        mkResult r.outcome r.store (rc.trace ++ r.trace)
      | .ok _ => mkResult (.error (.str "if condition not boolean")) rc.store rc.trace
      | _ => rc

    | .forOf x arrExpr body =>
      let ra := eval fuel' env store arrExpr
      match ra.outcome with
      | .ok (.arr elems) =>
        evalForOfAux (fun elem st => eval fuel' (env.set x elem) st body)
          elems ra.store ra.trace
      | .ok _ => mkResult (.error (.str "forOf on non-array")) ra.store ra.trace
      | _ => ra

    | .whileLoop loopFuel cond body =>
      evalWhileAux loopFuel
        (fun st => eval fuel' env st cond)
        (fun st => eval fuel' env st body)
        store []

    | .«break» => mkResult .brk store []

    | .ret e =>
      let r := eval fuel' env store e
      match r.outcome with
      | .ok v => mkResult (.returned v) r.store r.trace
      | _ => r

    | .call target argExprs resultBinder body =>
      let pr := evalPairsAux (eval fuel' env) argExprs store [] []
      match pr.2.outcome with
      | .ok _ =>
        let cr : CallRecord := { target := target, args := pr.1, resultId := resultBinder }
        let callTrace := pr.2.trace ++ [.call cr]
        -- Result value is universally quantified in proofs (via @ensures params).
        -- For evaluation, we use Val.none as the default result.
        let r := eval fuel' (env.set resultBinder Val.none) pr.2.store body
        mkResult r.outcome r.store (callTrace ++ r.trace)
      | _ => pr.2

    | .throw e =>
      let r := eval fuel' env store e
      match r.outcome with
      | .ok v => mkResult (.error v) r.store r.trace
      | _ => r

    | .tryCatch body errName handler =>
      let rb := eval fuel' env store body
      match rb.outcome with
      | .error v =>
        let rh := eval fuel' (env.set errName v) rb.store handler
        mkResult rh.outcome rh.store (rb.trace ++ rh.trace)
      | _ => rb

    | .binOp op e1 e2 =>
      let r1 := eval fuel' env store e1
      match r1.outcome with
      | .ok v1 =>
        let r2 := eval fuel' env r1.store e2
        match r2.outcome with
        | .ok v2 => mkResult (evalBinOp op v1 v2) r2.store (r1.trace ++ r2.trace)
        | _ => r2
      | _ => r1

    | .unOp op e =>
      let r := eval fuel' env store e
      match r.outcome with
      | .ok v => mkResult (evalUnOp op v) r.store r.trace
      | _ => r

/-- Top-level forOf used in theorems. With `evalForOfAux` this is exactly what
    eval's `forOf` case computes — the two agree definitionally (the old
    foldl-vs-explicit-recursion break mismatch is gone). -/
def evalForOf (fuel : Nat) (env : Env) (store : Store) (x : String)
    (elems : List Val) (body : Expr) (pfx : List TraceEntry) : Result :=
  evalForOfAux (fun elem st => eval fuel (env.set x elem) st body) elems store pfx

end JSCore
