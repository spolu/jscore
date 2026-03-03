/-
  JSCore₀ Metatheory — Taint Soundness.
  Changing a taint source's value doesn't change any matching call's arguments.
-/
import JSCore.Eval
import JSCore.Taint

namespace JSCore

private theorem eval_agree_on_freeVars :
    ∀ (fuel : Nat) (env env' : Env) (store : Store) (e : Expr),
      (∀ x, x ∈ freeVars e → env x = env' x) →
      eval fuel env store e = eval fuel env' store e
  | 0, env, env', store, e, h => by
      simp [eval]
  | fuel + 1, env, env', store, e, h => by
      have fold_pairs_agree :
          ∀ (ps : List (String × Expr))
            (acc : List (String × Val) × Store × List TraceEntry),
            (∀ x, x ∈ freeVarsPairs ps → env x = env' x) →
            ps.foldl
              (fun (acc : List (String × Val) × Store × List TraceEntry)
                (pair : String × Expr) =>
                let (vals, curStore, curTrace) := acc
                let r := eval fuel env curStore pair.2
                match r.outcome with
                | .ok v => (vals ++ [(pair.1, v)], r.store, curTrace ++ r.trace)
                | _ => (vals, r.store, curTrace ++ r.trace))
              acc
            =
            ps.foldl
              (fun (acc : List (String × Val) × Store × List TraceEntry)
                (pair : String × Expr) =>
                let (vals, curStore, curTrace) := acc
                let r := eval fuel env' curStore pair.2
                match r.outcome with
                | .ok v => (vals ++ [(pair.1, v)], r.store, curTrace ++ r.trace)
                | _ => (vals, r.store, curTrace ++ r.trace))
              acc := by
        intro ps
        induction ps with
        | nil =>
            intro acc hps
            rfl
        | cons p ps ihps =>
            intro acc hps
            cases acc with
            | mk vals rest =>
              cases rest with
              | mk curStore curTrace =>
                have h_head : ∀ x, x ∈ freeVars p.2 → env x = env' x := by
                  intro x hx
                  exact hps x (by simp [freeVarsPairs, hx])
                have h_eval :
                    eval fuel env curStore p.2 = eval fuel env' curStore p.2 :=
                  eval_agree_on_freeVars fuel env env' curStore p.2 h_head
                have h_tail : ∀ x, x ∈ freeVarsPairs ps → env x = env' x := by
                  intro x hx
                  exact hps x (by simp [freeVarsPairs, hx])
                have h_step :
                    (let r := eval fuel env curStore p.2
                     match r.outcome with
                     | .ok v => (vals ++ [(p.1, v)], r.store, curTrace ++ r.trace)
                     | _ => (vals, r.store, curTrace ++ r.trace))
                    =
                    (let r := eval fuel env' curStore p.2
                     match r.outcome with
                     | .ok v => (vals ++ [(p.1, v)], r.store, curTrace ++ r.trace)
                     | _ => (vals, r.store, curTrace ++ r.trace)) := by
                  simp [h_eval]
                simpa [List.foldl, h_step] using
                  ihps
                    (let r := eval fuel env' curStore p.2
                     match r.outcome with
                     | .ok v => (vals ++ [(p.1, v)], r.store, curTrace ++ r.trace)
                     | _ => (vals, r.store, curTrace ++ r.trace))
                    h_tail

      have fold_exprs_agree :
          ∀ (es : List Expr) (acc : List Val × Store × List TraceEntry),
            (∀ x, x ∈ freeVarsList es → env x = env' x) →
            es.foldl
              (fun (acc : List Val × Store × List TraceEntry) (ex : Expr) =>
                let (vals, curStore, curTrace) := acc
                let r := eval fuel env curStore ex
                match r.outcome with
                | .ok v => (vals ++ [v], r.store, curTrace ++ r.trace)
                | _ => (vals, r.store, curTrace ++ r.trace))
              acc
            =
            es.foldl
              (fun (acc : List Val × Store × List TraceEntry) (ex : Expr) =>
                let (vals, curStore, curTrace) := acc
                let r := eval fuel env' curStore ex
                match r.outcome with
                | .ok v => (vals ++ [v], r.store, curTrace ++ r.trace)
                | _ => (vals, r.store, curTrace ++ r.trace))
              acc := by
        intro es
        induction es with
        | nil =>
            intro acc hes
            rfl
        | cons ex es ihes =>
            intro acc hes
            cases acc with
            | mk vals rest =>
              cases rest with
              | mk curStore curTrace =>
                have h_head : ∀ x, x ∈ freeVars ex → env x = env' x := by
                  intro x hx
                  exact hes x (by simp [freeVarsList, hx])
                have h_eval :
                    eval fuel env curStore ex = eval fuel env' curStore ex :=
                  eval_agree_on_freeVars fuel env env' curStore ex h_head
                have h_tail : ∀ x, x ∈ freeVarsList es → env x = env' x := by
                  intro x hx
                  exact hes x (by simp [freeVarsList, hx])
                have h_step :
                    (let r := eval fuel env curStore ex
                     match r.outcome with
                     | .ok v => (vals ++ [v], r.store, curTrace ++ r.trace)
                     | _ => (vals, r.store, curTrace ++ r.trace))
                    =
                    (let r := eval fuel env' curStore ex
                     match r.outcome with
                     | .ok v => (vals ++ [v], r.store, curTrace ++ r.trace)
                     | _ => (vals, r.store, curTrace ++ r.trace)) := by
                  simp [h_eval]
                simpa [List.foldl, h_step] using
                  ihes
                    (let r := eval fuel env' curStore ex
                     match r.outcome with
                     | .ok v => (vals ++ [v], r.store, curTrace ++ r.trace)
                     | _ => (vals, r.store, curTrace ++ r.trace))
                    h_tail

      cases e with
      | var x =>
          have hx : env x = env' x := h x (by simp [freeVars])
          simp [eval, lookup, hx]
      | strLit _ =>
          simp [eval]
      | numLit _ =>
          simp [eval]
      | boolLit _ =>
          simp [eval]
      | none =>
          simp [eval]
      | letConst x e body =>
          have h_e : ∀ y, y ∈ freeVars e → env y = env' y := by
            intro y hy; exact h y (by simp [freeVars, hy])
          have h_body_flt : ∀ y, y ∈ (freeVars body).filter (· != x) → env y = env' y := by
            intro y hy; exact h y (by simp [freeVars, hy])
          have h_e_eq : eval fuel env store e = eval fuel env' store e :=
            eval_agree_on_freeVars fuel env env' store e h_e
          rw [eval, eval, ← h_e_eq]
          cases h_out : (eval fuel env store e).outcome <;> simp [h_out]
          case ok v =>
            have h_body_set : ∀ y, y ∈ freeVars body → (env.set x v) y = (env'.set x v) y := by
              intro y hy
              by_cases hyx : y = x
              · simp [Env.set, hyx]
              · have hyflt : y ∈ (freeVars body).filter (· != x) := by simp [hy, hyx]
                have hyEq := h_body_flt y hyflt
                simp [Env.set, hyx, hyEq]
            have h_body_eq :
                eval fuel (env.set x v) (eval fuel env store e).store body =
                eval fuel (env'.set x v) (eval fuel env store e).store body :=
              eval_agree_on_freeVars fuel (env.set x v) (env'.set x v)
                (eval fuel env store e).store body h_body_set
            simp [h_body_eq]
      | letMut x e body =>
          have h_e : ∀ y, y ∈ freeVars e → env y = env' y := by
            intro y hy; exact h y (by simp [freeVars, hy])
          have h_body : ∀ y, y ∈ freeVars body → env y = env' y := by
            intro y hy; exact h y (by simp [freeVars, hy])
          have h_e_eq : eval fuel env store e = eval fuel env' store e :=
            eval_agree_on_freeVars fuel env env' store e h_e
          rw [eval, eval, ← h_e_eq]
          cases h_out : (eval fuel env store e).outcome <;> simp [h_out]
          case ok v =>
            have h_body_eq :
                eval fuel env ((eval fuel env store e).store.set x v) body =
                eval fuel env' ((eval fuel env store e).store.set x v) body :=
              eval_agree_on_freeVars fuel env env'
                ((eval fuel env store e).store.set x v) body h_body
            simp [h_body_eq]
      | assign x e body =>
          have h_e : ∀ y, y ∈ freeVars e → env y = env' y := by
            intro y hy; exact h y (by simp [freeVars, hy])
          have h_body : ∀ y, y ∈ freeVars body → env y = env' y := by
            intro y hy; exact h y (by simp [freeVars, hy])
          have h_e_eq : eval fuel env store e = eval fuel env' store e :=
            eval_agree_on_freeVars fuel env env' store e h_e
          rw [eval, eval, ← h_e_eq]
          cases h_out : (eval fuel env store e).outcome <;> simp [h_out]
          case ok v =>
            have h_body_eq :
                eval fuel env ((eval fuel env store e).store.set x v) body =
                eval fuel env' ((eval fuel env store e).store.set x v) body :=
              eval_agree_on_freeVars fuel env env'
                ((eval fuel env store e).store.set x v) body h_body
            simp [h_body_eq]
      | field e _ =>
          have h_e : ∀ y, y ∈ freeVars e → env y = env' y := by
            intro y hy; exact h y (by simp [freeVars, hy])
          have h_e_eq : eval fuel env store e = eval fuel env' store e :=
            eval_agree_on_freeVars fuel env env' store e h_e
          simp [eval, ← h_e_eq]
      | obj pairs =>
          have h_pairs : ∀ y, y ∈ freeVarsPairs pairs → env y = env' y := by
            intro y hy; exact h y (by simpa [freeVars] using hy)
          have h_fold := fold_pairs_agree pairs ([], store, []) h_pairs
          simpa [eval] using congrArg (fun t => mkResult (.ok (.obj t.1)) t.2.1 t.2.2) h_fold
      | spread base overrides =>
          have h_base : ∀ y, y ∈ freeVars base → env y = env' y := by
            intro y hy; exact h y (by simp [freeVars, hy])
          have h_overrides : ∀ y, y ∈ freeVarsPairs overrides → env y = env' y := by
            intro y hy; exact h y (by simp [freeVars, hy])
          have h_base_eq : eval fuel env store base = eval fuel env' store base :=
            eval_agree_on_freeVars fuel env env' store base h_base
          rw [eval, eval, ← h_base_eq]
          cases h_out : (eval fuel env store base).outcome <;> simp [h_out]
          case ok v =>
            cases v <;> simp [h_out]
            case obj baseFields =>
              have h_fold := fold_pairs_agree overrides ([], (eval fuel env store base).store, []) h_overrides
              have h_fold' :
                  List.foldl
                      (fun acc pair =>
                        match (eval fuel env acc.2.fst pair.snd).outcome with
                        | Outcome.ok v =>
                          (acc.fst ++ [(pair.fst, v)], (eval fuel env acc.2.fst pair.snd).store,
                            acc.2.snd ++ (eval fuel env acc.2.fst pair.snd).trace)
                        | x =>
                          (acc.fst, (eval fuel env acc.2.fst pair.snd).store,
                            acc.2.snd ++ (eval fuel env acc.2.fst pair.snd).trace))
                      ([], (eval fuel env store base).store, []) overrides
                    =
                  List.foldl
                      (fun acc pair =>
                        match (eval fuel env' acc.2.fst pair.snd).outcome with
                        | Outcome.ok v =>
                          (acc.fst ++ [(pair.fst, v)], (eval fuel env' acc.2.fst pair.snd).store,
                            acc.2.snd ++ (eval fuel env' acc.2.fst pair.snd).trace)
                        | x =>
                          (acc.fst, (eval fuel env' acc.2.fst pair.snd).store,
                            acc.2.snd ++ (eval fuel env' acc.2.fst pair.snd).trace))
                      ([], (eval fuel env store base).store, []) overrides := by
                simpa using h_fold
              exact
                congrArg
                  (fun t =>
                    mkResult
                      (.ok (.obj (List.foldl (fun acc x => fieldSet acc x.fst x.snd) baseFields t.fst)))
                      t.snd.fst
                      ((eval fuel env store base).trace ++ t.snd.snd))
                  h_fold'
      | arr exprs =>
          have h_exprs : ∀ y, y ∈ freeVarsList exprs → env y = env' y := by
            intro y hy; exact h y (by simpa [freeVars] using hy)
          have h_fold := fold_exprs_agree exprs ([], store, []) h_exprs
          simpa [eval] using congrArg (fun t => mkResult (.ok (.arr t.1)) t.2.1 t.2.2) h_fold
      | index e idx =>
          have h_e : ∀ y, y ∈ freeVars e → env y = env' y := by
            intro y hy; exact h y (by simp [freeVars, hy])
          have h_idx : ∀ y, y ∈ freeVars idx → env y = env' y := by
            intro y hy; exact h y (by simp [freeVars, hy])
          have h_e_eq : eval fuel env store e = eval fuel env' store e :=
            eval_agree_on_freeVars fuel env env' store e h_e
          rw [eval, eval, ← h_e_eq]
          cases h_out : (eval fuel env store e).outcome <;> simp [h_out]
          case ok v =>
            cases v <;> simp [h_out]
            case arr _ =>
              have h_idx_eq :
                  eval fuel env (eval fuel env store e).store idx =
                  eval fuel env' (eval fuel env store e).store idx :=
                eval_agree_on_freeVars fuel env env'
                  (eval fuel env store e).store idx h_idx
              simp [h_idx_eq]
      | push arrName valExpr =>
          have h_arr : env arrName = env' arrName := by
            exact h arrName (by simp [freeVars])
          have h_val : ∀ y, y ∈ freeVars valExpr → env y = env' y := by
            intro y hy; exact h y (by simp [freeVars, hy])
          have h_val_eq : eval fuel env store valExpr = eval fuel env' store valExpr :=
            eval_agree_on_freeVars fuel env env' store valExpr h_val
          rw [eval, eval, ← h_val_eq]
          have h_lookup :
              lookup env (eval fuel env store valExpr).store arrName =
              lookup env' (eval fuel env store valExpr).store arrName := by
            simp [lookup, h_arr]
          cases h_out : (eval fuel env store valExpr).outcome <;> simp [h_out, h_lookup]
      | seq e1 e2 =>
          have h_e1 : ∀ y, y ∈ freeVars e1 → env y = env' y := by
            intro y hy; exact h y (by simp [freeVars, hy])
          have h_e2 : ∀ y, y ∈ freeVars e2 → env y = env' y := by
            intro y hy; exact h y (by simp [freeVars, hy])
          have h_e1_eq : eval fuel env store e1 = eval fuel env' store e1 :=
            eval_agree_on_freeVars fuel env env' store e1 h_e1
          rw [eval, eval, ← h_e1_eq]
          cases h_out : (eval fuel env store e1).outcome <;> simp [h_out]
          case ok _ =>
            have h_e2_eq :
                eval fuel env (eval fuel env store e1).store e2 =
                eval fuel env' (eval fuel env store e1).store e2 :=
              eval_agree_on_freeVars fuel env env'
                (eval fuel env store e1).store e2 h_e2
            simp [h_e2_eq]
      | ite cond thn els =>
          have h_cond : ∀ y, y ∈ freeVars cond → env y = env' y := by
            intro y hy; exact h y (by simp [freeVars, hy])
          have h_thn : ∀ y, y ∈ freeVars thn → env y = env' y := by
            intro y hy; exact h y (by simp [freeVars, hy])
          have h_els : ∀ y, y ∈ freeVars els → env y = env' y := by
            intro y hy; exact h y (by simp [freeVars, hy])
          have h_cond_eq : eval fuel env store cond = eval fuel env' store cond :=
            eval_agree_on_freeVars fuel env env' store cond h_cond
          rw [eval, eval, ← h_cond_eq]
          cases h_out : (eval fuel env store cond).outcome <;> simp [h_out]
          case ok v =>
            cases v with
            | bool b =>
                cases b with
                | true =>
                    have h_thn_eq :
                        eval fuel env (eval fuel env store cond).store thn =
                        eval fuel env' (eval fuel env store cond).store thn :=
                      eval_agree_on_freeVars fuel env env'
                        (eval fuel env store cond).store thn h_thn
                    simp [h_thn_eq]
                | false =>
                    have h_els_eq :
                        eval fuel env (eval fuel env store cond).store els =
                        eval fuel env' (eval fuel env store cond).store els :=
                      eval_agree_on_freeVars fuel env env'
                        (eval fuel env store cond).store els h_els
                    simp [h_els_eq]
            | _ =>
                simp
      | forOf x arrExpr body =>
          have h_arr : ∀ y, y ∈ freeVars arrExpr → env y = env' y := by
            intro y hy; exact h y (by simp [freeVars, hy])
          have h_body_flt : ∀ y, y ∈ (freeVars body).filter (· != x) → env y = env' y := by
            intro y hy; exact h y (by simp [freeVars, hy])
          have h_arr_eq : eval fuel env store arrExpr = eval fuel env' store arrExpr :=
            eval_agree_on_freeVars fuel env env' store arrExpr h_arr
          rw [eval, eval, ← h_arr_eq]
          cases h_out : (eval fuel env store arrExpr).outcome <;> simp [h_out]
          case ok v =>
            cases v <;> simp [h_out]
            case arr elems =>
              have fold_forOf_agree :
                  ∀ (vs : List Val) (acc : Result),
                    vs.foldl
                      (fun (acc : Result) elem =>
                        match acc.outcome with
                        | .ok _ =>
                          let r := eval fuel (env.set x elem) acc.store body
                          match r.outcome with
                          | .brk => mkResult (.ok .none) r.store (acc.trace ++ r.trace)
                          | .returned v => mkResult (.returned v) r.store (acc.trace ++ r.trace)
                          | _ => mkResult r.outcome r.store (acc.trace ++ r.trace)
                        | _ => acc)
                      acc
                    =
                    vs.foldl
                      (fun (acc : Result) elem =>
                        match acc.outcome with
                        | .ok _ =>
                          let r := eval fuel (env'.set x elem) acc.store body
                          match r.outcome with
                          | .brk => mkResult (.ok .none) r.store (acc.trace ++ r.trace)
                          | .returned v => mkResult (.returned v) r.store (acc.trace ++ r.trace)
                          | _ => mkResult r.outcome r.store (acc.trace ++ r.trace)
                        | _ => acc)
                      acc := by
                intro vs
                induction vs with
                | nil =>
                    intro acc
                    rfl
                | cons hd tl iht =>
                    intro acc
                    have h_body_eq_hd :
                        eval fuel (env.set x hd) acc.store body =
                        eval fuel (env'.set x hd) acc.store body := by
                      apply eval_agree_on_freeVars fuel (env.set x hd) (env'.set x hd) acc.store body
                      intro y hy
                      by_cases hyx : y = x
                      · simp [Env.set, hyx]
                      · have hyflt : y ∈ (freeVars body).filter (· != x) := by simp [hy, hyx]
                        have hyEq := h_body_flt y hyflt
                        simp [Env.set, hyx, hyEq]
                    have h_step :
                        (match acc.outcome with
                         | .ok _ =>
                           let r := eval fuel (env.set x hd) acc.store body
                           match r.outcome with
                           | .brk => mkResult (.ok .none) r.store (acc.trace ++ r.trace)
                           | .returned v => mkResult (.returned v) r.store (acc.trace ++ r.trace)
                           | _ => mkResult r.outcome r.store (acc.trace ++ r.trace)
                         | _ => acc)
                        =
                        (match acc.outcome with
                         | .ok _ =>
                           let r := eval fuel (env'.set x hd) acc.store body
                           match r.outcome with
                           | .brk => mkResult (.ok .none) r.store (acc.trace ++ r.trace)
                           | .returned v => mkResult (.returned v) r.store (acc.trace ++ r.trace)
                           | _ => mkResult r.outcome r.store (acc.trace ++ r.trace)
                         | _ => acc) := by
                      simp [h_body_eq_hd]
                    simpa [List.foldl, h_step] using
                      iht
                        (match acc.outcome with
                         | .ok _ =>
                           let r := eval fuel (env'.set x hd) acc.store body
                           match r.outcome with
                           | .brk => mkResult (.ok .none) r.store (acc.trace ++ r.trace)
                           | .returned v => mkResult (.returned v) r.store (acc.trace ++ r.trace)
                           | _ => mkResult r.outcome r.store (acc.trace ++ r.trace)
                         | _ => acc)
              have h_fold := fold_forOf_agree elems
                (mkResult (.ok .none)
                  (eval fuel env store arrExpr).store
                  (eval fuel env store arrExpr).trace)
              simpa [h_fold]
      | whileLoop loopFuel cond body =>
          have h_cond : ∀ y, y ∈ freeVars cond → env y = env' y := by
            intro y hy; exact h y (by simp [freeVars, hy])
          have h_body : ∀ y, y ∈ freeVars body → env y = env' y := by
            intro y hy; exact h y (by simp [freeVars, hy])
          have h_cond_fn :
              (fun st => eval fuel env st cond) =
              (fun st => eval fuel env' st cond) := by
            funext st
            exact eval_agree_on_freeVars fuel env env' st cond h_cond
          have h_body_fn :
              (fun st => eval fuel env st body) =
              (fun st => eval fuel env' st body) := by
            funext st
            exact eval_agree_on_freeVars fuel env env' st body h_body
          simp [eval, h_cond_fn, h_body_fn]
      | «break» =>
          simp [eval]
      | ret e =>
          have h_e : ∀ y, y ∈ freeVars e → env y = env' y := by
            intro y hy; exact h y (by simp [freeVars, hy])
          have h_e_eq : eval fuel env store e = eval fuel env' store e :=
            eval_agree_on_freeVars fuel env env' store e h_e
          simp [eval, ← h_e_eq]
      | call target argExprs resultBinder body =>
          have h_args : ∀ y, y ∈ freeVarsPairs argExprs → env y = env' y := by
            intro y hy; exact h y (by simp [freeVars, hy])
          have h_body_flt :
              ∀ y, y ∈ (freeVars body).filter (· != resultBinder) → env y = env' y := by
            intro y hy; exact h y (by simp [freeVars, hy])
          have h_args_fold := fold_pairs_agree argExprs ([], store, []) h_args
          have h_body_set :
              ∀ y, y ∈ freeVars body →
                (env.set resultBinder Val.none) y = (env'.set resultBinder Val.none) y := by
            intro y hy
            by_cases hyb : y = resultBinder
            · simp [Env.set, hyb]
            · have hyflt : y ∈ (freeVars body).filter (· != resultBinder) := by simp [hy, hyb]
              have hyEq := h_body_flt y hyflt
              simp [Env.set, hyb, hyEq]
          have h_body_eq :
              eval fuel
                (env.set resultBinder Val.none)
                ((argExprs.foldl
                  (fun (acc : List (String × Val) × Store × List TraceEntry)
                    (pair : String × Expr) =>
                    let (vals, curStore, curTrace) := acc
                    let r := eval fuel env curStore pair.2
                    match r.outcome with
                    | .ok v => (vals ++ [(pair.1, v)], r.store, curTrace ++ r.trace)
                    | _ => (vals, r.store, curTrace ++ r.trace))
                  ([], store, [])).2.1)
                body
              =
              eval fuel
                (env'.set resultBinder Val.none)
                ((argExprs.foldl
                  (fun (acc : List (String × Val) × Store × List TraceEntry)
                    (pair : String × Expr) =>
                    let (vals, curStore, curTrace) := acc
                    let r := eval fuel env curStore pair.2
                    match r.outcome with
                    | .ok v => (vals ++ [(pair.1, v)], r.store, curTrace ++ r.trace)
                    | _ => (vals, r.store, curTrace ++ r.trace))
                  ([], store, [])).2.1)
                body :=
            eval_agree_on_freeVars fuel
              (env.set resultBinder Val.none)
              (env'.set resultBinder Val.none)
              ((argExprs.foldl
                (fun (acc : List (String × Val) × Store × List TraceEntry)
                  (pair : String × Expr) =>
                  let (vals, curStore, curTrace) := acc
                  let r := eval fuel env curStore pair.2
                  match r.outcome with
                  | .ok v => (vals ++ [(pair.1, v)], r.store, curTrace ++ r.trace)
                  | _ => (vals, r.store, curTrace ++ r.trace))
                ([], store, [])).2.1)
              body h_body_set
          have h_args_fold_norm :
              List.foldl
                  (fun acc pair =>
                    match (eval fuel env acc.2.fst pair.snd).outcome with
                    | Outcome.ok v =>
                      (acc.fst ++ [(pair.fst, v)], (eval fuel env acc.2.fst pair.snd).store,
                        acc.2.snd ++ (eval fuel env acc.2.fst pair.snd).trace)
                    | x =>
                      (acc.fst, (eval fuel env acc.2.fst pair.snd).store,
                        acc.2.snd ++ (eval fuel env acc.2.fst pair.snd).trace))
                  ([], store, []) argExprs
                =
              List.foldl
                  (fun acc pair =>
                    match (eval fuel env' acc.2.fst pair.snd).outcome with
                    | Outcome.ok v =>
                      (acc.fst ++ [(pair.fst, v)], (eval fuel env' acc.2.fst pair.snd).store,
                        acc.2.snd ++ (eval fuel env' acc.2.fst pair.snd).trace)
                    | x =>
                      (acc.fst, (eval fuel env' acc.2.fst pair.snd).store,
                        acc.2.snd ++ (eval fuel env' acc.2.fst pair.snd).trace))
                  ([], store, []) argExprs := by
            simpa using h_args_fold
          have h_body_eq_at :
              ∀ st,
                eval fuel (env.set resultBinder Val.none) st body =
                eval fuel (env'.set resultBinder Val.none) st body := by
            intro st
            exact eval_agree_on_freeVars fuel
              (env.set resultBinder Val.none)
              (env'.set resultBinder Val.none)
              st body h_body_set
          let foldL : List (String × Val) × Store × List TraceEntry :=
            List.foldl
              (fun acc pair =>
                match (eval fuel env acc.2.fst pair.snd).outcome with
                | Outcome.ok v =>
                  (acc.fst ++ [(pair.fst, v)], (eval fuel env acc.2.fst pair.snd).store,
                    acc.2.snd ++ (eval fuel env acc.2.fst pair.snd).trace)
                | x =>
                  (acc.fst, (eval fuel env acc.2.fst pair.snd).store,
                    acc.2.snd ++ (eval fuel env acc.2.fst pair.snd).trace))
              ([], store, []) argExprs
          let foldR : List (String × Val) × Store × List TraceEntry :=
            List.foldl
              (fun acc pair =>
                match (eval fuel env' acc.2.fst pair.snd).outcome with
                | Outcome.ok v =>
                  (acc.fst ++ [(pair.fst, v)], (eval fuel env' acc.2.fst pair.snd).store,
                    acc.2.snd ++ (eval fuel env' acc.2.fst pair.snd).trace)
                | x =>
                  (acc.fst, (eval fuel env' acc.2.fst pair.snd).store,
                    acc.2.snd ++ (eval fuel env' acc.2.fst pair.snd).trace))
              ([], store, []) argExprs
          rw [eval, eval]
          change
            (match foldL with
            | (argVals, argStore, argTrace) =>
              let cr : CallRecord := { target := target, args := argVals, resultId := resultBinder }
              let callTrace := argTrace ++ [TraceEntry.call cr]
              let resultVal := Val.none
              let r := eval fuel (env.set resultBinder resultVal) argStore body
              mkResult r.outcome r.store (callTrace ++ r.trace))
            =
            (match foldR with
            | (argVals, argStore, argTrace) =>
              let cr : CallRecord := { target := target, args := argVals, resultId := resultBinder }
              let callTrace := argTrace ++ [TraceEntry.call cr]
              let resultVal := Val.none
              let r := eval fuel (env'.set resultBinder resultVal) argStore body
              mkResult r.outcome r.store (callTrace ++ r.trace))
          have h_fold : foldL = foldR := by
            simpa [foldL, foldR] using h_args_fold_norm
          cases h_foldL : foldL with
          | mk argVals rest =>
            cases h_rest : rest with
            | mk argStore argTrace =>
              have h_foldR : foldR = (argVals, argStore, argTrace) := by
                simpa [h_foldL, h_rest] using h_fold.symm
              rw [h_foldR]
              simp [h_foldL, h_rest, h_body_eq_at argStore]
      | throw e =>
          have h_e : ∀ y, y ∈ freeVars e → env y = env' y := by
            intro y hy; exact h y (by simp [freeVars, hy])
          have h_e_eq : eval fuel env store e = eval fuel env' store e :=
            eval_agree_on_freeVars fuel env env' store e h_e
          simp [eval, ← h_e_eq]
      | tryCatch body errName handler =>
          have h_body : ∀ y, y ∈ freeVars body → env y = env' y := by
            intro y hy; exact h y (by simp [freeVars, hy])
          have h_handler_flt :
              ∀ y, y ∈ (freeVars handler).filter (· != errName) → env y = env' y := by
            intro y hy; exact h y (by simp [freeVars, hy])
          have h_body_eq : eval fuel env store body = eval fuel env' store body :=
            eval_agree_on_freeVars fuel env env' store body h_body
          rw [eval, eval, ← h_body_eq]
          cases h_out : (eval fuel env store body).outcome <;> simp [h_out]
          case error v =>
            have h_handler_set :
                ∀ y, y ∈ freeVars handler →
                  (env.set errName v) y = (env'.set errName v) y := by
              intro y hy
              by_cases hyb : y = errName
              · simp [Env.set, hyb]
              · have hyflt : y ∈ (freeVars handler).filter (· != errName) := by simp [hy, hyb]
                have hyEq := h_handler_flt y hyflt
                simp [Env.set, hyb, hyEq]
            have h_handler_eq :
                eval fuel (env.set errName v) (eval fuel env store body).store handler =
                eval fuel (env'.set errName v) (eval fuel env store body).store handler :=
              eval_agree_on_freeVars fuel (env.set errName v) (env'.set errName v)
                (eval fuel env store body).store handler h_handler_set
            simp [h_handler_eq]
      | binOp op e1 e2 =>
          have h_e1 : ∀ y, y ∈ freeVars e1 → env y = env' y := by
            intro y hy; exact h y (by simp [freeVars, hy])
          have h_e2 : ∀ y, y ∈ freeVars e2 → env y = env' y := by
            intro y hy; exact h y (by simp [freeVars, hy])
          have h_e1_eq : eval fuel env store e1 = eval fuel env' store e1 :=
            eval_agree_on_freeVars fuel env env' store e1 h_e1
          rw [eval, eval, ← h_e1_eq]
          cases h_out : (eval fuel env store e1).outcome <;> simp [h_out]
          case ok _ =>
            have h_e2_eq :
                eval fuel env (eval fuel env store e1).store e2 =
                eval fuel env' (eval fuel env store e1).store e2 :=
              eval_agree_on_freeVars fuel env env'
                (eval fuel env store e1).store e2 h_e2
            simp [h_e2_eq]
      | unOp op e =>
          have h_e : ∀ y, y ∈ freeVars e → env y = env' y := by
            intro y hy; exact h y (by simp [freeVars, hy])
          have h_e_eq : eval fuel env store e = eval fuel env' store e :=
            eval_agree_on_freeVars fuel env env' store e h_e
          simp [eval, ← h_e_eq]

-- Helper: if an expression's free variables don't contain source,
-- then evaluation is identical regardless of source's value in env.
-- This is the key lemma for taint soundness.
theorem eval_independent_of_source (fuel : Nat) (env env' : Env) (store : Store)
    (e : Expr) (source : String)
    (h_env : ∀ x, x ≠ source → env x = env' x)
    (h_not_free : source ∉ freeVars e) :
    eval fuel env store e = eval fuel env' store e := by
  apply eval_agree_on_freeVars fuel env env' store e
  intro x hx
  by_cases hxs : x = source
  · subst hxs
    exact False.elim (h_not_free hx)
  · exact h_env x hxs

-- Main taint soundness theorem:
-- If no call matching pattern has any argument tainted by source,
-- then changing source's value doesn't change any matching call's arguments.
theorem taint_soundness (fuel : Nat) (prog : Expr) (source pattern : String)
    (h : notTaintedIn prog source pattern = true) :
    ∀ env env' store,
      (∀ x, x ≠ source → env x = env' x) →
      callsTo (eval fuel env store prog).trace pattern =
      callsTo (eval fuel env' store prog).trace pattern := by
  intro env env' store h_env
  have h_not_free : source ∉ freeVars prog := by
    by_cases hnf : source ∉ freeVars prog
    · exact hnf
    · have h_not_tainted : decide (source ∉ freeVars prog) && (callExprsIn prog pattern).all
          (fun ci => ci.namedArgs.all (fun (_, argExpr) => !taintedBy prog source argExpr)) = true := by
        simpa [notTaintedIn] using h
      simp [hnf] at h_not_tainted
  have h_eval :=
    eval_independent_of_source fuel env env' store prog source h_env h_not_free
  simp [h_eval]

end JSCore
