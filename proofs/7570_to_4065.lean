-- Equation7570 → Equation4065
-- Recorded verdict: false
-- Premise: x = y ◇ (x ◇ ((y ◇ (x ◇ y)) ◇ y))
-- Conclusion: x ◇ x = ((x ◇ x) ◇ x) ◇ x
-- Original submission SHA-256: 8f5bb91d336cf2167bc2233ed1796f6df9566ce0b32c02db2f9ea422fac0dccd
-- Generator: equational-challenges standalone v1
-- All project definitions are embedded in this file.
import Lean.Elab.Tactic.Omega

-- Embedded module: JudgeMagma.Magma
section
/- Magma class, ◇ notation, and helpers for building finite magmas. -/

class Magma (α : Type _) where
  /-- The binary magma operation, written `◇`. -/
  op : α → α → α

@[inherit_doc] infix:65 " ◇ " => Magma.op

/-- Build a `Magma (Fin n)` from a flat list of values.
    Entry at index `i*n + j` gives the result of `i ◇ j`.
    Usage: `instance : Magma (Fin 3) := magmaFin 3 [0,0,0, 0,0,0, 0,0,1]`

    Marked `@[implicit_reducible]` because Lean 4.32 requires class-valued
    definitions to be transparent to instance resolution. Deliberately not
    plain `@[reducible]`: that would unfold the table literal during general
    unification too, which is pure cost for the large `Fin n` tables here. -/
@[implicit_reducible]
def magmaFin (n : Nat) (table : List Nat) : Magma (Fin n) where
  op a b :=
    let idx := a.val * n + b.val
    ⟨table[idx]! % n, Nat.mod_lt _ (Fin.pos a)⟩
end

-- Embedded module: JudgeProblem
section
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = y ◇ (x ◇ ((y ◇ (x ◇ y)) ◇ y))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G), x ◇ x = ((x ◇ x) ◇ x) ◇ x
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Original submission body
                             
                   
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace submission
inductive CM where
  | e : CM
  | k : CM → CM
  | p : CM → CM → CM
deriving DecidableEq
namespace CM
def L : CM → CM | e => e | k _ => e | p a _ => a
def R : CM → CM | e => e | k _ => e | p _ b => b
def U : CM → CM | e => e | k a => a | p _ _ => e
def sz : CM → Nat
  | e => 0
  | k a => sz a + 1
  | p a b => (sz a + 1) + (sz b + 1)
theorem sz_lt_p_left (a b : CM) : sz a < sz (p a b) := by
  change sz a < (sz a + 1) + (sz b + 1)
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (sz a))
    (Nat.le_add_right (sz a + 1) (sz b + 1))
theorem sz_lt_p_right (a b : CM) : sz b < sz (p a b) := by
  change sz b < (sz a + 1) + (sz b + 1)
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (sz b))
    (Nat.le_add_left (sz b + 1) (sz a + 1))
mutual
inductive Code : CM → CM → CM → Prop
  | law (x y H0 : CM)
      (s0 : Step x y H0) :
      Code y (p x (p (p y H0) y)) x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_y q_H0 : CM, Step q_x q_y q_H0 ∧ a = q_y ∧ b = (p q_x (p (p q_y q_H0) q_y)) ∧ o = q_x := by
  cases h with
  | law x y H0 s0 =>
    exact ⟨_, _, _, by assumption, rfl, rfl, rfl⟩
def getOut (a b : CM) : CM := (L b)
theorem code_get {a b o : CM} (h : Code a b o) : getOut a b = o := by
  cases h <;> rfl
theorem code_unique {a b o q : CM} (h : Code a b o) (k : Code a b q) : o = q :=
  (code_get h).symm.trans (code_get k)
theorem code_bounds {a b o : CM} (h : Code a b o) :
    sz a < sz b ∧ sz o < sz b := by
  cases h with
  | law x y H0 s0 =>
    cases s0 with
    | raw =>
      simp only [getOut, L, R, U, sz] <;> omega
    | hit h0 =>
      simp only [getOut, L, R, U, sz] <;> omega

noncomputable def eval (a b : CM) : CM := by
  classical
  exact if h : ∃ o, Code a b o then Classical.choose h else p a b
theorem eval_hit {{a b o : CM}} (h : Code a b o) : eval a b = o := by
  rw [eval, dif_pos ⟨o, h⟩]
  exact code_unique (Classical.choose_spec ⟨o, h⟩) h
theorem eval_raw {{a b : CM}} (h : ¬ ∃ o, Code a b o) : eval a b = p a b := by
  rw [eval, dif_neg h]
theorem eval_step (a b : CM) : Step a b (eval a b) := by
  by_cases h : ∃ o, Code a b o
  · rcases h with ⟨o, hc⟩
    rw [eval_hit hc]
    exact Step.hit hc
  · rw [eval_raw h]
    exact Step.raw a b
theorem nr0 (x y H0 : CM)
    (s0 : Step x y H0) :
    ¬ ∃ o, Code y H0 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_y, q_H0, qs0, ha, hb, ho⟩
  cases s0 with
  | raw =>
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change y = q_y at e0
      have e1 := congrArg (fun q => (L q)) hb
      change x = q_x at e1
      have e2 := congrArg (fun q => (R q)) hb
      change y = (p (p q_y (p q_x q_y)) q_y) at e2
      have cyc : q_y = (p (p q_y (p q_x q_y)) q_y) := Eq.trans (Eq.symm (Eq.trans (Eq.trans (Eq.symm (rfl)) (Eq.trans (e0) (rfl))) (rfl))) (Eq.trans (e2) (rfl))
      have hlt : sz q_y < sz (p (p q_y (p q_x q_y)) q_y) := Nat.lt_trans (sz_lt_p_left q_y (p q_x q_y)) (sz_lt_p_left (p q_y (p q_x q_y)) q_y)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit h1 =>
      have e0 := congrArg (fun q => q) ha
      change y = q_y at e0
      have e1 := congrArg (fun q => (L q)) hb
      change x = q_x at e1
      have e2 := congrArg (fun q => (R q)) hb
      change y = (p (p q_y q_H0) q_y) at e2
      have cyc : q_y = (p (p q_y q_H0) q_y) := Eq.trans (Eq.symm (Eq.trans (Eq.trans (Eq.symm (rfl)) (Eq.trans (e0) (rfl))) (rfl))) (Eq.trans (e2) (rfl))
      have hlt : sz q_y < sz (p (p q_y q_H0) q_y) := Nat.lt_trans (sz_lt_p_left q_y q_H0) (sz_lt_p_left (p q_y q_H0) q_y)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit h0 =>
    cases qs0 with
    | raw =>
      have hcB := code_bounds hc
      have h0B := code_bounds h0
      have p0 := congrArg (fun q => q) ha
      change y = q_y at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => q) hb
      change H0 = (p q_x (p (p q_y (p q_x q_y)) q_y)) at p1
      have z1 := congrArg sz p1
      have hx : sz q_y < sz (p q_x (p (p q_y (p q_x q_y)) q_y)) := by
        have q := hcB.1
        have eu : sz y = sz q_y := congrArg sz (Eq.trans (p0) (rfl))
        have ev : sz H0 = sz (p q_x (p (p q_y (p q_x q_y)) q_y)) := congrArg sz (Eq.trans (p1) (rfl))
        have q1 : sz q_y < sz H0 := lt_of_eq_of_lt eu.symm q
        exact lt_of_lt_of_eq q1 ev
      have hy : sz (p q_x (p (p q_y (p q_x q_y)) q_y)) < sz q_y := by
        have q := h0B.2
        have ev : sz H0 = sz (p q_x (p (p q_y (p q_x q_y)) q_y)) := congrArg sz (Eq.trans (p1) (rfl))
        have eu : sz y = sz q_y := congrArg sz (Eq.trans (p0) (rfl))
        have q1 : sz (p q_x (p (p q_y (p q_x q_y)) q_y)) < sz y := lt_of_eq_of_lt ev.symm q
        exact lt_of_lt_of_eq q1 eu
      exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
    | hit h1 =>
      have hcB := code_bounds hc
      have h0B := code_bounds h0
      have h1B := code_bounds h1
      have p0 := congrArg (fun q => q) ha
      change y = q_y at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => q) hb
      change H0 = (p q_x (p (p q_y q_H0) q_y)) at p1
      have z1 := congrArg sz p1
      have hx : sz q_y < sz (p q_x (p (p q_y q_H0) q_y)) := by
        have q := hcB.1
        have eu : sz y = sz q_y := congrArg sz (Eq.trans (p0) (rfl))
        have ev : sz H0 = sz (p q_x (p (p q_y q_H0) q_y)) := congrArg sz (Eq.trans (p1) (rfl))
        have q1 : sz q_y < sz H0 := lt_of_eq_of_lt eu.symm q
        exact lt_of_lt_of_eq q1 ev
      have hy : sz (p q_x (p (p q_y q_H0) q_y)) < sz q_y := by
        have q := h0B.2
        have ev : sz H0 = sz (p q_x (p (p q_y q_H0) q_y)) := congrArg sz (Eq.trans (p1) (rfl))
        have eu : sz y = sz q_y := congrArg sz (Eq.trans (p0) (rfl))
        have q1 : sz (p q_x (p (p q_y q_H0) q_y)) < sz y := lt_of_eq_of_lt ev.symm q
        exact lt_of_lt_of_eq q1 eu
      exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
theorem nr1 (x y H0 : CM)
    (s0 : Step x y H0) :
    ¬ ∃ o, Code (p y H0) y o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_y, q_H0, qs0, ha, hb, ho⟩
  cases s0 with
  | raw =>
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change (p y (p x y)) = q_y at e0
      have e1 := congrArg (fun q => q) hb
      change y = (p q_x (p (p q_y (p q_x q_y)) q_y)) at e1
      have cyc : y = (p q_x (p (p (p y (p x y)) (p q_x (p y (p x y)))) (p y (p x y)))) := Eq.trans (Eq.symm (rfl)) (Eq.trans (e1) (congrArg (fun z => p q_x z) (Eq.trans (congrArg (fun z => p z q_y) (Eq.trans (congrArg (fun z => p z (p q_x q_y)) (Eq.trans (Eq.symm (Eq.trans (Eq.symm (rfl)) (Eq.trans (e0) (rfl)))) (rfl))) (congrArg (fun z => p (p y (p x y)) z) (congrArg (fun z => p q_x z) (Eq.trans (Eq.symm (Eq.trans (Eq.symm (rfl)) (Eq.trans (e0) (rfl)))) (rfl)))))) (congrArg (fun z => p (p (p y (p x y)) (p q_x (p y (p x y)))) z) (Eq.trans (Eq.symm (Eq.trans (Eq.symm (rfl)) (Eq.trans (e0) (rfl)))) (rfl))))))
      have hlt : sz y < sz (p q_x (p (p (p y (p x y)) (p q_x (p y (p x y)))) (p y (p x y)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left y (p x y)) (sz_lt_p_left (p y (p x y)) (p q_x (p y (p x y))))) (sz_lt_p_left (p (p y (p x y)) (p q_x (p y (p x y)))) (p y (p x y)))) (sz_lt_p_right q_x (p (p (p y (p x y)) (p q_x (p y (p x y)))) (p y (p x y))))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit h1 =>
      have e0 := congrArg (fun q => q) ha
      change (p y (p x y)) = q_y at e0
      have e1 := congrArg (fun q => q) hb
      change y = (p q_x (p (p q_y q_H0) q_y)) at e1
      have cyc : y = (p q_x (p (p (p y (p x y)) q_H0) (p y (p x y)))) := Eq.trans (Eq.symm (rfl)) (Eq.trans (e1) (congrArg (fun z => p q_x z) (Eq.trans (congrArg (fun z => p z q_y) (congrArg (fun z => p z q_H0) (Eq.trans (Eq.symm (Eq.trans (Eq.symm (rfl)) (Eq.trans (e0) (rfl)))) (rfl)))) (congrArg (fun z => p (p (p y (p x y)) q_H0) z) (Eq.trans (Eq.symm (Eq.trans (Eq.symm (rfl)) (Eq.trans (e0) (rfl)))) (rfl))))))
      have hlt : sz y < sz (p q_x (p (p (p y (p x y)) q_H0) (p y (p x y)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left y (p x y)) (sz_lt_p_left (p y (p x y)) q_H0)) (sz_lt_p_left (p (p y (p x y)) q_H0) (p y (p x y)))) (sz_lt_p_right q_x (p (p (p y (p x y)) q_H0) (p y (p x y))))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit h0 =>
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change (p y H0) = q_y at e0
      have e1 := congrArg (fun q => q) hb
      change y = (p q_x (p (p q_y (p q_x q_y)) q_y)) at e1
      have cyc : y = (p q_x (p (p (p y H0) (p q_x (p y H0))) (p y H0))) := Eq.trans (Eq.symm (rfl)) (Eq.trans (e1) (congrArg (fun z => p q_x z) (Eq.trans (congrArg (fun z => p z q_y) (Eq.trans (congrArg (fun z => p z (p q_x q_y)) (Eq.trans (Eq.symm (Eq.trans (Eq.symm (rfl)) (Eq.trans (e0) (rfl)))) (rfl))) (congrArg (fun z => p (p y H0) z) (congrArg (fun z => p q_x z) (Eq.trans (Eq.symm (Eq.trans (Eq.symm (rfl)) (Eq.trans (e0) (rfl)))) (rfl)))))) (congrArg (fun z => p (p (p y H0) (p q_x (p y H0))) z) (Eq.trans (Eq.symm (Eq.trans (Eq.symm (rfl)) (Eq.trans (e0) (rfl)))) (rfl))))))
      have hlt : sz y < sz (p q_x (p (p (p y H0) (p q_x (p y H0))) (p y H0))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left y H0) (sz_lt_p_left (p y H0) (p q_x (p y H0)))) (sz_lt_p_left (p (p y H0) (p q_x (p y H0))) (p y H0))) (sz_lt_p_right q_x (p (p (p y H0) (p q_x (p y H0))) (p y H0)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit h1 =>
      have e0 := congrArg (fun q => q) ha
      change (p y H0) = q_y at e0
      have e1 := congrArg (fun q => q) hb
      change y = (p q_x (p (p q_y q_H0) q_y)) at e1
      have cyc : y = (p q_x (p (p (p y H0) q_H0) (p y H0))) := Eq.trans (Eq.symm (rfl)) (Eq.trans (e1) (congrArg (fun z => p q_x z) (Eq.trans (congrArg (fun z => p z q_y) (congrArg (fun z => p z q_H0) (Eq.trans (Eq.symm (Eq.trans (Eq.symm (rfl)) (Eq.trans (e0) (rfl)))) (rfl)))) (congrArg (fun z => p (p (p y H0) q_H0) z) (Eq.trans (Eq.symm (Eq.trans (Eq.symm (rfl)) (Eq.trans (e0) (rfl)))) (rfl))))))
      have hlt : sz y < sz (p q_x (p (p (p y H0) q_H0) (p y H0))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left y H0) (sz_lt_p_left (p y H0) q_H0)) (sz_lt_p_left (p (p y H0) q_H0) (p y H0))) (sz_lt_p_right q_x (p (p (p y H0) q_H0) (p y H0)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr2 (x y H0 : CM)
    (s0 : Step x y H0) :
    ¬ ∃ o, Code x (p (p y H0) y) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_y, q_H0, qs0, ha, hb, ho⟩
  cases s0 with
  | raw =>
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change x = q_y at e0
      have e1 := congrArg (fun q => (L q)) hb
      change (p y (p x y)) = q_x at e1
      have e2 := congrArg (fun q => (R q)) hb
      change y = (p (p q_y (p q_x q_y)) q_y) at e2
      have cyc : y = (p (p q_y (p (p y (p q_y y)) q_y)) q_y) := Eq.trans (Eq.symm (rfl)) (Eq.trans (e2) (congrArg (fun z => p z q_y) (congrArg (fun z => p q_y z) (congrArg (fun z => p z q_y) (Eq.trans (Eq.symm (Eq.trans (Eq.symm (congrArg (fun z => p y z) (congrArg (fun z => p z y) (Eq.trans (Eq.trans (Eq.symm (rfl)) (Eq.trans (e0) (rfl))) (rfl))))) (Eq.trans (e1) (rfl)))) (rfl))))))
      have hlt : sz y < sz (p (p q_y (p (p y (p q_y y)) q_y)) q_y) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left y (p q_y y)) (sz_lt_p_left (p y (p q_y y)) q_y)) (sz_lt_p_right q_y (p (p y (p q_y y)) q_y))) (sz_lt_p_left (p q_y (p (p y (p q_y y)) q_y)) q_y)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit h1 =>
      have hcB := code_bounds hc
      have h1B := code_bounds h1
      have p0 := congrArg (fun q => q) ha
      change x = q_y at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => (L q)) hb
      change (p y (p x y)) = q_x at p1
      have z1 := congrArg sz p1
      have p2 := congrArg (fun q => (R q)) hb
      change y = (p (p q_y q_H0) q_y) at p2
      have z2 := congrArg sz p2
      have badlt : sz q_y < sz q_x := by
        rw [Eq.trans (p1.symm) (Eq.trans (congrArg (fun z => p z (p x y)) (Eq.trans (p2) (rfl))) (congrArg (fun z => p (p (p q_y q_H0) q_y) z) (Eq.trans (congrArg (fun z => p z y) (Eq.trans (p0) (rfl))) (congrArg (fun z => p q_y z) (Eq.trans (p2) (rfl))))))]
        exact Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_y q_H0) (sz_lt_p_left (p q_y q_H0) q_y)) (sz_lt_p_left (p (p q_y q_H0) q_y) (p q_y (p (p q_y q_H0) q_y)))
      exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) h1B.1).elim
  | hit h0 =>
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change x = q_y at e0
      have e1 := congrArg (fun q => (L q)) hb
      change (p y H0) = q_x at e1
      have e2 := congrArg (fun q => (R q)) hb
      change y = (p (p q_y (p q_x q_y)) q_y) at e2
      have cyc : y = (p (p q_y (p (p y H0) q_y)) q_y) := Eq.trans (Eq.symm (rfl)) (Eq.trans (e2) (congrArg (fun z => p z q_y) (congrArg (fun z => p q_y z) (congrArg (fun z => p z q_y) (Eq.trans (Eq.symm (Eq.trans (Eq.symm (rfl)) (Eq.trans (e1) (rfl)))) (rfl))))))
      have hlt : sz y < sz (p (p q_y (p (p y H0) q_y)) q_y) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left y H0) (sz_lt_p_left (p y H0) q_y)) (sz_lt_p_right q_y (p (p y H0) q_y))) (sz_lt_p_left (p q_y (p (p y H0) q_y)) q_y)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit h1 =>
      have hcB := code_bounds hc
      have h0B := code_bounds h0
      have h1B := code_bounds h1
      have p0 := congrArg (fun q => q) ha
      change x = q_y at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => (L q)) hb
      change (p y H0) = q_x at p1
      have z1 := congrArg sz p1
      have p2 := congrArg (fun q => (R q)) hb
      change y = (p (p q_y q_H0) q_y) at p2
      have z2 := congrArg sz p2
      have badlt : sz q_y < sz q_x := by
        rw [Eq.trans (p1.symm) (congrArg (fun z => p z H0) (Eq.trans (p2) (rfl)))]
        exact Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_y q_H0) (sz_lt_p_left (p q_y q_H0) q_y)) (sz_lt_p_left (p (p q_y q_H0) q_y) H0)
      exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) h1B.1).elim
theorem source_holds (x y : CM) :
    x = (eval y (eval x (eval (eval y (eval x y)) y))) := by
  let H0 := eval x y
  have e0a : x = x := by
    change x = x
    rfl
  have e0b : y = y := by
    change y = y
    rfl
  have s0 : Step x y H0 := by
    rw [← e0a, ← e0b]
    exact eval_step x y
  change x = (eval y (eval x (eval (eval y H0) y)))
  have rawEq : (eval y (eval x (eval (eval y H0) y))) = (eval y (p x (p (p y H0) y))) := by
    calc
      (eval y (eval x (eval (eval y H0) y))) = (eval y (eval x (eval (p y H0) y))) := congrArg (fun q => (eval y (eval x (eval q y)))) (eval_raw (nr0 x y H0 s0))
      _ = (eval y (eval x (p (p y H0) y))) := congrArg (fun q => (eval y (eval x q))) (eval_raw (nr1 x y H0 s0))
      _ = (eval y (p x (p (p y H0) y))) := congrArg (fun q => (eval y q)) (eval_raw (nr2 x y H0 s0))
  exact (eval_hit (Code.law x y H0 s0)).symm.trans rawEq.symm
noncomputable instance instMagma2 : Magma CM where op := eval
theorem nt0 : ¬ ∃ o, Code CM.e CM.e o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_y, q_H0, s0, ha, hb, ho⟩
  have bad := congrArg (fun q => (L (R q))) hb
  change CM.e = (p q_y q_H0) at bad
  cases bad
theorem nt1 : ¬ ∃ o, Code (CM.p CM.e CM.e) CM.e o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_y, q_H0, s0, ha, hb, ho⟩
  have bad := congrArg (fun q => (L (R q))) hb
  change CM.e = (p q_y q_H0) at bad
  cases bad
theorem nt2 : ¬ ∃ o, Code (CM.p (CM.p CM.e CM.e) CM.e) CM.e o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_y, q_H0, s0, ha, hb, ho⟩
  have bad := congrArg (fun q => (L (R q))) hb
  change CM.e = (p q_y q_H0) at bad
  cases bad
end CM
end submission
open submission
open submission.CM
noncomputable def submission : Goal := by
  refine ⟨CM, CM.instMagma2, ?_, ?_⟩
  · intro x y
    exact CM.source_holds x y
  · intro target
    have bad := target CM.e
    have hl : (eval CM.e CM.e) = (CM.p CM.e CM.e) := (eval_raw nt0)
    have hr : (eval (eval (eval CM.e CM.e) CM.e) CM.e) = (CM.p (CM.p (CM.p CM.e CM.e) CM.e) CM.e) := by
      calc
        (eval (eval (eval CM.e CM.e) CM.e) CM.e) = (eval (eval (CM.p CM.e CM.e) CM.e) CM.e) := congrArg (fun q => (eval (eval q CM.e) CM.e)) (eval_raw nt0)
        _ = (eval (CM.p (CM.p CM.e CM.e) CM.e) CM.e) := congrArg (fun q => (eval q CM.e)) (eval_raw nt1)
        _ = (CM.p (CM.p (CM.p CM.e CM.e) CM.e) CM.e) := (eval_raw nt2)
    have bad2 := hl.symm.trans (bad.trans hr)
    exact Bool.noConfusion (congrArg (fun q => match (L q) with | e => false | k _ => false | p _ _ => true) bad2)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_7570_to_4065 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_7570_to_4065
