/-
  JSCore₀ Metatheory — Fuel Monotonicity.

  `eval`'s fuel decreases per AST depth (not per loop iteration: forOf/while
  bodies are re-run at the same fuel), so any fuel ≥ the term's structural
  depth yields the same result. `eval_fuel_mono` makes that precise; it is
  what lets generated theorems assume `fuel ≥ N` instead of pinning one
  concrete fuel value.

  `Expr.depth` mirrors the extractor's `depthFuel` (extractor/src/extract.ts);
  the extractor emits `h_fuel : fuel ≥ depthFuel + 1`, and `by decide`
  discharges `Expr.depth body ≤ N` per generated theorem.
-/
import JSCore.Eval
import JSCore.Metatheory.EvalEq

namespace JSCore

-- Structural depth of an expression: the fuel needed to evaluate it.
mutual
  def Expr.depth : Expr → Nat
    | .var _ => 1
    | .strLit _ => 1
    | .numLit _ => 1
    | .boolLit _ => 1
    | .none => 1
    | .letConst _ e body => 1 + max e.depth body.depth
    | .letMut _ e body => 1 + max e.depth body.depth
    | .assign _ e body => 1 + max e.depth body.depth
    | .field e _ => 1 + e.depth
    | .obj pairs => 1 + depthPairs pairs
    | .spread base overrides => 1 + max base.depth (depthPairs overrides)
    | .arr exprs => 1 + depthList exprs
    | .index e idx => 1 + max e.depth idx.depth
    | .push _ valExpr => 1 + valExpr.depth
    | .seq e1 e2 => 1 + max e1.depth e2.depth
    | .ite c t f => 1 + max c.depth (max t.depth f.depth)
    | .forOf _ arrExpr body => 1 + max arrExpr.depth body.depth
    | .whileLoop _ c body => 1 + max c.depth body.depth
    | .«break» => 1
    | .ret e => 1 + e.depth
    | .call _ args _ body => 1 + max (depthPairs args) body.depth
    | .throw e => 1 + e.depth
    | .tryCatch body _ handler => 1 + max body.depth handler.depth
    | .binOp _ e1 e2 => 1 + max e1.depth e2.depth
    | .unOp _ e => 1 + e.depth

  def depthPairs : List (String × Expr) → Nat
    | [] => 0
    | (_, e) :: rest => max e.depth (depthPairs rest)

  def depthList : List Expr → Nat
    | [] => 0
    | e :: rest => max e.depth (depthList rest)
end

theorem Expr.depth_pos (e : Expr) : 1 ≤ e.depth := by
  cases e <;> (simp only [Expr.depth]; omega)

theorem mem_depthPairs_le : ∀ {pairs : List (String × Expr)} {p : String × Expr},
    p ∈ pairs → p.2.depth ≤ depthPairs pairs := by
  intro pairs
  induction pairs with
  | nil => intro p h; cases h
  | cons hd tl ih =>
    intro p h
    obtain ⟨k, e⟩ := hd
    simp only [depthPairs]
    cases h with
    | head => exact Nat.le_max_left _ _
    | tail _ hmem => exact Nat.le_trans (ih hmem) (Nat.le_max_right _ _)

theorem mem_depthList_le : ∀ {exprs : List Expr} {e : Expr},
    e ∈ exprs → e.depth ≤ depthList exprs := by
  intro exprs
  induction exprs with
  | nil => intro e h; cases h
  | cons hd tl ih =>
    intro e h
    simp only [depthList]
    cases h with
    | head => exact Nat.le_max_left _ _
    | tail _ hmem => exact Nat.le_trans (ih hmem) (Nat.le_max_right _ _)

-- Congruence lemmas: the list-evaluation helpers only depend on their
-- evaluation closures pointwise.

theorem evalPairsAux_congr {f g : Store → Expr → Result}
    (pairs : List (String × Expr))
    (h : ∀ p ∈ pairs, ∀ st, f st p.2 = g st p.2) :
    ∀ (st : Store) (tr : List TraceEntry) (vals : List (String × Val)),
    evalPairsAux f pairs st tr vals = evalPairsAux g pairs st tr vals := by
  induction pairs with
  | nil => intros; rfl
  | cons hd tl ih =>
    obtain ⟨k, e⟩ := hd
    intro st tr vals
    rw [evalPairsAux_cons, evalPairsAux_cons,
        show f st e = g st e from h (k, e) (List.mem_cons_self _ _) st]
    cases ho : (g st e).outcome with
    | ok v =>
      simp only [ho]
      exact ih (fun p hp st' => h p (List.mem_cons_of_mem _ hp) st') _ _ _
    | error v => simp only [ho]
    | brk => simp only [ho]
    | returned v => simp only [ho]

theorem evalElemsAux_congr {f g : Store → Expr → Result}
    (exprs : List Expr)
    (h : ∀ e ∈ exprs, ∀ st, f st e = g st e) :
    ∀ (st : Store) (tr : List TraceEntry) (vals : List Val),
    evalElemsAux f exprs st tr vals = evalElemsAux g exprs st tr vals := by
  induction exprs with
  | nil => intros; rfl
  | cons hd tl ih =>
    intro st tr vals
    rw [evalElemsAux_cons, evalElemsAux_cons,
        show f st hd = g st hd from h hd (List.mem_cons_self _ _) st]
    cases ho : (g st hd).outcome with
    | ok v =>
      simp only [ho]
      exact ih (fun e he st' => h e (List.mem_cons_of_mem _ he) st') _ _ _
    | error v => simp only [ho]
    | brk => simp only [ho]
    | returned v => simp only [ho]

theorem evalForOfAux_congr {b1 b2 : Val → Store → Result}
    (h : ∀ elem st, b1 elem st = b2 elem st) :
    ∀ (elems : List Val) (st : Store) (tr : List TraceEntry),
    evalForOfAux b1 elems st tr = evalForOfAux b2 elems st tr := by
  intro elems
  induction elems with
  | nil => intros; rfl
  | cons hd tl ih =>
    intro st tr
    rw [evalForOfAux_cons, evalForOfAux_cons, h hd st]
    cases ho : (b2 hd st).outcome with
    | ok v => simp only [ho]; exact ih _ _
    | error e => simp only [ho]
    | brk => simp only [ho]
    | returned v => simp only [ho]

theorem evalWhileAux_congr {c1 c2 b1 b2 : Store → Result}
    (hc : ∀ st, c1 st = c2 st) (hb : ∀ st, b1 st = b2 st) :
    ∀ (loopFuel : Nat) (st : Store) (tr : List TraceEntry),
    evalWhileAux loopFuel c1 b1 st tr = evalWhileAux loopFuel c2 b2 st tr := by
  intro loopFuel
  induction loopFuel with
  | zero => intros; rfl
  | succ lf' ih =>
    intro st tr
    simp only [evalWhileAux]
    rw [hc st]
    cases hoc : (c2 st).outcome with
    | ok v =>
      cases v with
      | bool b =>
        cases b with
        | true =>
          simp only [hoc]
          rw [hb]
          cases hob : (b2 (c2 st).store).outcome with
          | ok v' => simp only [hob]; exact ih _ _
          | error e => simp only [hob]
          | brk => simp only [hob]
          | returned v' => simp only [hob]
        | false => simp only [hoc]
      | str _ => simp only [hoc]
      | num _ => simp only [hoc]
      | none => simp only [hoc]
      | obj _ => simp only [hoc]
      | arr _ => simp only [hoc]
    | error v => simp only [hoc]
    | brk => simp only [hoc]
    | returned v => simp only [hoc]

/-- Fuel monotonicity: once fuel covers the term's structural depth, adding
    more fuel does not change the result. -/
theorem eval_fuel_mono :
    ∀ (n : Nat) (e : Expr), Expr.depth e ≤ n →
    ∀ (m : Nat), n ≤ m →
    ∀ (env : Env) (store : Store),
    eval m env store e = eval n env store e := by
  intro n
  induction n with
  | zero =>
    intro e hdep
    exact absurd hdep (by have := Expr.depth_pos e; omega)
  | succ n' ih =>
    intro e hdep m hm env store
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hm' : n' ≤ m' := by omega
    cases e with
    | var x => rw [eval_var_eq, eval_var_eq]
    | strLit s => rw [eval_strLit_eq, eval_strLit_eq]
    | numLit i => rw [eval_numLit_eq, eval_numLit_eq]
    | boolLit b => rw [eval_boolLit_eq, eval_boolLit_eq]
    | none => rw [eval_none_eq, eval_none_eq]
    | «break» => rw [eval_break_eq, eval_break_eq]
    | ret e =>
      have h1 : e.depth ≤ n' := by simp only [Expr.depth] at hdep; omega
      rw [eval_ret_eq, eval_ret_eq, ih e h1 m' hm']
    | throw e =>
      have h1 : e.depth ≤ n' := by simp only [Expr.depth] at hdep; omega
      rw [eval_throw_eq, eval_throw_eq, ih e h1 m' hm']
    | unOp op e =>
      have h1 : e.depth ≤ n' := by simp only [Expr.depth] at hdep; omega
      rw [eval_unOp_eq, eval_unOp_eq, ih e h1 m' hm']
    | field e fname =>
      have h1 : e.depth ≤ n' := by simp only [Expr.depth] at hdep; omega
      rw [eval_field_eq, eval_field_eq, ih e h1 m' hm']
    | push arrName valExpr =>
      have h1 : valExpr.depth ≤ n' := by simp only [Expr.depth] at hdep; omega
      rw [eval_push_eq, eval_push_eq, ih valExpr h1 m' hm']
    | seq e1 e2 =>
      have h1 : e1.depth ≤ n' := by simp only [Expr.depth] at hdep; omega
      have h2 : e2.depth ≤ n' := by simp only [Expr.depth] at hdep; omega
      rw [eval_seq_eq, eval_seq_eq, ih e1 h1 m' hm']
      cases ho : (eval n' env store e1).outcome with
      | ok v => simp only [ho]; rw [ih e2 h2 m' hm']
      | error v => simp only [ho]
      | brk => simp only [ho]
      | returned v => simp only [ho]
    | letConst x e1 body =>
      have h1 : e1.depth ≤ n' := by simp only [Expr.depth] at hdep; omega
      have h2 : body.depth ≤ n' := by simp only [Expr.depth] at hdep; omega
      rw [eval_letConst_eq, eval_letConst_eq, ih e1 h1 m' hm']
      cases ho : (eval n' env store e1).outcome with
      | ok v => simp only [ho]; rw [ih body h2 m' hm']
      | error v => simp only [ho]
      | brk => simp only [ho]
      | returned v => simp only [ho]
    | letMut x e1 body =>
      have h1 : e1.depth ≤ n' := by simp only [Expr.depth] at hdep; omega
      have h2 : body.depth ≤ n' := by simp only [Expr.depth] at hdep; omega
      rw [eval_letMut_eq, eval_letMut_eq, ih e1 h1 m' hm']
      cases ho : (eval n' env store e1).outcome with
      | ok v => simp only [ho]; rw [ih body h2 m' hm']
      | error v => simp only [ho]
      | brk => simp only [ho]
      | returned v => simp only [ho]
    | assign x e1 body =>
      have h1 : e1.depth ≤ n' := by simp only [Expr.depth] at hdep; omega
      have h2 : body.depth ≤ n' := by simp only [Expr.depth] at hdep; omega
      rw [eval_assign_eq, eval_assign_eq, ih e1 h1 m' hm']
      cases ho : (eval n' env store e1).outcome with
      | ok v => simp only [ho]; rw [ih body h2 m' hm']
      | error v => simp only [ho]
      | brk => simp only [ho]
      | returned v => simp only [ho]
    | binOp op e1 e2 =>
      have h1 : e1.depth ≤ n' := by simp only [Expr.depth] at hdep; omega
      have h2 : e2.depth ≤ n' := by simp only [Expr.depth] at hdep; omega
      rw [eval_binOp_eq, eval_binOp_eq, ih e1 h1 m' hm']
      cases ho : (eval n' env store e1).outcome with
      | ok v => simp only [ho]; rw [ih e2 h2 m' hm']
      | error v => simp only [ho]
      | brk => simp only [ho]
      | returned v => simp only [ho]
    | ite c t f =>
      have hc : c.depth ≤ n' := by simp only [Expr.depth] at hdep; omega
      have ht : t.depth ≤ n' := by simp only [Expr.depth] at hdep; omega
      have hf : f.depth ≤ n' := by simp only [Expr.depth] at hdep; omega
      rw [eval_ite_eq, eval_ite_eq, ih c hc m' hm']
      cases ho : (eval n' env store c).outcome with
      | ok v =>
        cases v with
        | bool b =>
          cases b with
          | true => simp only [ho]; rw [ih t ht m' hm']
          | false => simp only [ho]; rw [ih f hf m' hm']
        | str _ => simp only [ho]
        | num _ => simp only [ho]
        | none => simp only [ho]
        | obj _ => simp only [ho]
        | arr _ => simp only [ho]
      | error v => simp only [ho]
      | brk => simp only [ho]
      | returned v => simp only [ho]
    | tryCatch body errName handler =>
      have h1 : body.depth ≤ n' := by simp only [Expr.depth] at hdep; omega
      have h2 : handler.depth ≤ n' := by simp only [Expr.depth] at hdep; omega
      rw [eval_tryCatch_eq, eval_tryCatch_eq, ih body h1 m' hm']
      cases ho : (eval n' env store body).outcome with
      | error v => simp only [ho]; rw [ih handler h2 m' hm']
      | ok v => simp only [ho]
      | brk => simp only [ho]
      | returned v => simp only [ho]
    | index e idx =>
      have h1 : e.depth ≤ n' := by simp only [Expr.depth] at hdep; omega
      have h2 : idx.depth ≤ n' := by simp only [Expr.depth] at hdep; omega
      rw [eval_index_eq, eval_index_eq, ih e h1 m' hm']
      cases ho : (eval n' env store e).outcome with
      | ok v =>
        cases v with
        | arr elems => simp only [ho]; rw [ih idx h2 m' hm']
        | str _ => simp only [ho]
        | num _ => simp only [ho]
        | bool _ => simp only [ho]
        | none => simp only [ho]
        | obj _ => simp only [ho]
      | error v => simp only [ho]
      | brk => simp only [ho]
      | returned v => simp only [ho]
    | obj pairs =>
      have hp : ∀ p ∈ pairs, ∀ st, eval m' env st p.2 = eval n' env st p.2 := by
        intro p hmem st
        have : p.2.depth ≤ n' := by
          have := mem_depthPairs_le hmem
          simp only [Expr.depth] at hdep
          omega
        exact ih p.2 this m' hm' env st
      rw [eval_obj_eq, eval_obj_eq, evalPairsAux_congr pairs hp]
    | arr exprs =>
      have he : ∀ e ∈ exprs, ∀ st, eval m' env st e = eval n' env st e := by
        intro e hmem st
        have : e.depth ≤ n' := by
          have := mem_depthList_le hmem
          simp only [Expr.depth] at hdep
          omega
        exact ih e this m' hm' env st
      rw [eval_arr_eq, eval_arr_eq, evalElemsAux_congr exprs he]
    | spread base overrides =>
      have hb : base.depth ≤ n' := by simp only [Expr.depth] at hdep; omega
      have hov : ∀ p ∈ overrides, ∀ st, eval m' env st p.2 = eval n' env st p.2 := by
        intro p hmem st
        have : p.2.depth ≤ n' := by
          have := mem_depthPairs_le hmem
          simp only [Expr.depth] at hdep
          omega
        exact ih p.2 this m' hm' env st
      rw [eval_spread_eq, eval_spread_eq, ih base hb m' hm']
      cases ho : (eval n' env store base).outcome with
      | ok v =>
        cases v with
        | obj baseFields => simp only [ho]; rw [evalPairsAux_congr overrides hov]
        | str _ => simp only [ho]
        | num _ => simp only [ho]
        | bool _ => simp only [ho]
        | none => simp only [ho]
        | arr _ => simp only [ho]
      | error v => simp only [ho]
      | brk => simp only [ho]
      | returned v => simp only [ho]
    | call target args resultBinder body =>
      have hbody : body.depth ≤ n' := by simp only [Expr.depth] at hdep; omega
      have hargs : ∀ p ∈ args, ∀ st, eval m' env st p.2 = eval n' env st p.2 := by
        intro p hmem st
        have : p.2.depth ≤ n' := by
          have := mem_depthPairs_le hmem
          simp only [Expr.depth] at hdep
          omega
        exact ih p.2 this m' hm' env st
      rw [eval_call_eq, eval_call_eq, evalPairsAux_congr args hargs]
      cases ho : (evalPairsAux (eval n' env) args store [] []).2.outcome with
      | ok v => simp only [ho]; rw [ih body hbody m' hm']
      | error v => simp only [ho]
      | brk => simp only [ho]
      | returned v => simp only [ho]
    | forOf x arrExpr body =>
      have ha : arrExpr.depth ≤ n' := by simp only [Expr.depth] at hdep; omega
      have hb : body.depth ≤ n' := by simp only [Expr.depth] at hdep; omega
      rw [eval_forOf_eq, eval_forOf_eq, ih arrExpr ha m' hm']
      cases ho : (eval n' env store arrExpr).outcome with
      | ok v =>
        cases v with
        | arr elems =>
          simp only [ho, evalForOf]
          exact evalForOfAux_congr
            (fun elem st => ih body hb m' hm' (env.set x elem) st) elems _ _
        | str _ => simp only [ho]
        | num _ => simp only [ho]
        | bool _ => simp only [ho]
        | none => simp only [ho]
        | obj _ => simp only [ho]
      | error v => simp only [ho]
      | brk => simp only [ho]
      | returned v => simp only [ho]
    | whileLoop loopFuel c body =>
      have hc : c.depth ≤ n' := by simp only [Expr.depth] at hdep; omega
      have hb : body.depth ≤ n' := by simp only [Expr.depth] at hdep; omega
      rw [eval_whileLoop_eq, eval_whileLoop_eq]
      exact evalWhileAux_congr
        (fun st => ih c hc m' hm' env st)
        (fun st => ih body hb m' hm' env st)
        loopFuel store []

/-- Corollary: any sufficient fuel computes the same result as `depth e`. -/
theorem eval_at_depth (e : Expr) (n : Nat) (h : Expr.depth e ≤ n)
    (env : Env) (store : Store) :
    eval n env store e = eval e.depth env store e :=
  eval_fuel_mono e.depth e (Nat.le_refl _) n h env store

end JSCore
