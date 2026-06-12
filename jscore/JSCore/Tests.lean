/-
  JSCore₀ Semantics Regression Tests.

  Executable #guard checks pinning the evaluator's error/short-circuit
  semantics — specifically the behaviors fixed in the 2026-06 review:
  errors inside obj/arr/spread/call-argument evaluation abort the enclosing
  expression (no error swallowing, no phantom calls in the trace), and
  `break` actually stops a forOf loop.
-/
import JSCore.Eval

namespace JSCore.Tests

open JSCore

-- A throw inside an object literal aborts evaluation: the error propagates and
-- the later field's call is never made.
#guard
  (let r := eval 10 emptyEnv emptyStore
    (.obj [("a", .throw (.strLit "boom")),
           ("b", .call ["db", "x"] [] "r" (.var "r"))])
   r.outcome == .error (.str "boom") && r.trace == [])

-- A call whose argument throws is NOT recorded in the trace.
#guard
  (let r := eval 10 emptyEnv emptyStore
    (.call ["db", "y"] [("x", .throw (.strLit "bad"))] "r" (.var "r"))
   r.outcome == .error (.str "bad") && r.trace == [])

-- A throw inside an array literal aborts evaluation.
#guard
  (let r := eval 10 emptyEnv emptyStore
    (.arr [.throw (.strLit "e"), .call ["db", "z"] [] "r" (.var "r")])
   r.outcome == .error (.str "e") && r.trace == [])

-- A throw inside spread overrides aborts evaluation.
#guard
  (let r := eval 10 emptyEnv emptyStore
    (.spread (.obj [("a", .numLit 1)])
      [("b", .throw (.strLit "x")), ("c", .call ["db", "q"] [] "r" (.var "r"))])
   r.outcome == .error (.str "x") && r.trace == [])

-- break stops a forOf loop: only the first iteration's call is recorded.
#guard
  (let r := eval 10 emptyEnv emptyStore
    (.forOf "x" (.arr [.numLit 1, .numLit 2, .numLit 3])
      (.call ["db", "t"] [] "r" Expr.«break»))
   r.outcome == .ok .none && r.trace.length == 1)

-- A normal forOf over 3 elements records 3 calls.
#guard
  (let r := eval 10 emptyEnv emptyStore
    (.forOf "x" (.arr [.numLit 1, .numLit 2, .numLit 3])
      (.call ["db", "t"] [] "r" Expr.none))
   r.outcome == .ok .none && r.trace.length == 3)

-- An error inside a forOf body propagates and stops the loop.
#guard
  (let r := eval 10 emptyEnv emptyStore
    (.forOf "x" (.arr [.numLit 1, .numLit 2])
      (.seq (.call ["db", "t"] [] "r" Expr.none) (.throw (.strLit "mid"))))
   r.outcome == .error (.str "mid") && r.trace.length == 1)

-- Successful evaluation still records calls and produces values.
#guard
  (let r := eval 10 emptyEnv emptyStore
    (.obj [("a", .call ["db", "k"] [] "r" (.var "r")), ("b", .numLit 2)])
   r.outcome == .ok (.obj [("a", Val.none), ("b", .num 2)]) && r.trace.length == 1)

-- Call arguments are evaluated and recorded with their values.
#guard
  (let r := eval 10 emptyEnv emptyStore
    (.call ["db", "w"] [("amount", .numLit 42)] "r" (.var "r"))
   r.trace == [.call { target := ["db", "w"], args := [("amount", .num 42)], resultId := "r" }])

-- push works on Store-bound (letMut) arrays.
#guard
  (let r := eval 10 emptyEnv emptyStore
    (.letMut "acc" (.arr [])
      (.seq (.push "acc" (.numLit 1)) (.var "acc")))
   r.outcome == .ok (.arr [.num 1]))

-- push on an Env-bound (letConst) array errors instead of silently shadowing
-- it in the Store — Env/Store disjointness is preserved.
#guard
  (let r := eval 10 emptyEnv emptyStore
    (.letConst "acc" (.arr [])
      (.seq (.push "acc" (.numLit 1)) (.var "acc")))
   r.outcome == .error (.str "push on non-array: acc"))

-- Negative array index yields .none (JS `undefined`), not element 0.
#guard
  (let r := eval 10 emptyEnv emptyStore
    (.index (.arr [.numLit 7, .numLit 8]) (.numLit (-1)))
   r.outcome == .ok .none)

-- Out-of-bounds index yields .none; in-bounds yields the element.
#guard
  (let r := eval 10 emptyEnv emptyStore
    (.index (.arr [.numLit 7, .numLit 8]) (.numLit 5))
   r.outcome == .ok .none)
#guard
  (let r := eval 10 emptyEnv emptyStore
    (.index (.arr [.numLit 7, .numLit 8]) (.numLit 1))
   r.outcome == .ok (.num 8))

end JSCore.Tests
