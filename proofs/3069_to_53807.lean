-- Equation3069 → Equation53807
-- Recorded verdict: false
-- Premise: x = (((x ◇ y) ◇ x) ◇ y) ◇ y
-- Conclusion: x ◇ (x ◇ x) = x ◇ (x ◇ (x ◇ x))
-- Original submission SHA-256: 39b4a08ca31341b59f11145eab99d60496e98329a3b3807b258ad46f5bcf3e92
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (((x ◇ y) ◇ x) ◇ y) ◇ y
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G), x ◇ (x ◇ x) = x ◇ (x ◇ (x ◇ x))
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
      Code (p (p H0 x) y) y x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_y q_H0 : CM, Step q_x q_y q_H0 ∧ a = (p (p q_H0 q_x) q_y) ∧ b = q_y ∧ o = q_x := by
  cases h with
  | law x y H0 s0 =>
    exact ⟨_, _, _, by assumption, rfl, rfl, rfl⟩
def getOut (a b : CM) : CM := (R (L a))
theorem code_get {a b o : CM} (h : Code a b o) : getOut a b = o := by
  cases h <;> rfl
theorem code_unique {a b o q : CM} (h : Code a b o) (k : Code a b q) : o = q :=
  (code_get h).symm.trans (code_get k)
theorem code_bounds {a b o : CM} (h : Code a b o) :
    sz b < sz a ∧ sz o < sz a := by
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
    ¬ ∃ o, Code H0 x o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_y, q_H0, qs0, ha, hb, ho⟩
  cases s0 with
  | raw =>
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => (L q)) ha
      change x = (p (p q_x q_y) q_x) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change y = q_y at e1
      have e2 := congrArg (fun q => q) hb
      change x = q_y at e2
      have cyc : q_y = (p (p q_x q_y) q_x) := Eq.symm (Eq.trans (Eq.symm (Eq.trans (Eq.trans (Eq.symm (rfl)) (Eq.trans (e0) (rfl))) (rfl))) (Eq.trans (e2) (rfl)))
      have hlt : sz q_y < sz (p (p q_x q_y) q_x) := Nat.lt_trans (sz_lt_p_right q_x q_y) (sz_lt_p_left (p q_x q_y) q_x)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit h1 =>
      have hcB := code_bounds hc
      have h1B := code_bounds h1
      have p0 := congrArg (fun q => (L q)) ha
      change x = (p q_H0 q_x) at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => (R q)) ha
      change y = q_y at p1
      have z1 := congrArg sz p1
      have p2 := congrArg (fun q => q) hb
      change x = q_y at p2
      have z2 := congrArg sz p2
      have badlt : sz q_x < sz q_y := by
        rw [Eq.trans (p2.symm) (Eq.trans (p0) (rfl))]
        exact sz_lt_p_right q_H0 q_x
      exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) h1B.1).elim
  | hit h0 =>
    cases qs0 with
    | raw =>
      have hcB := code_bounds hc
      have h0B := code_bounds h0
      have p0 := congrArg (fun q => q) ha
      change H0 = (p (p (p q_x q_y) q_x) q_y) at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => q) hb
      change x = q_y at p1
      have z1 := congrArg sz p1
      have hx : sz q_y < sz (p (p (p q_x q_y) q_x) q_y) := by
        have q := hcB.1
        have eu : sz x = sz q_y := congrArg sz (Eq.trans (p1) (rfl))
        have ev : sz H0 = sz (p (p (p q_x q_y) q_x) q_y) := congrArg sz (Eq.trans (p0) (rfl))
        have q1 : sz q_y < sz H0 := lt_of_eq_of_lt eu.symm q
        exact lt_of_lt_of_eq q1 ev
      have hy : sz (p (p (p q_x q_y) q_x) q_y) < sz q_y := by
        have q := h0B.2
        have ev : sz H0 = sz (p (p (p q_x q_y) q_x) q_y) := congrArg sz (Eq.trans (p0) (rfl))
        have eu : sz x = sz q_y := congrArg sz (Eq.trans (p1) (rfl))
        have q1 : sz (p (p (p q_x q_y) q_x) q_y) < sz x := lt_of_eq_of_lt ev.symm q
        exact lt_of_lt_of_eq q1 eu
      exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
    | hit h1 =>
      have hcB := code_bounds hc
      have h0B := code_bounds h0
      have h1B := code_bounds h1
      have p0 := congrArg (fun q => q) ha
      change H0 = (p (p q_H0 q_x) q_y) at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => q) hb
      change x = q_y at p1
      have z1 := congrArg sz p1
      have hx : sz q_y < sz (p (p q_H0 q_x) q_y) := by
        have q := hcB.1
        have eu : sz x = sz q_y := congrArg sz (Eq.trans (p1) (rfl))
        have ev : sz H0 = sz (p (p q_H0 q_x) q_y) := congrArg sz (Eq.trans (p0) (rfl))
        have q1 : sz q_y < sz H0 := lt_of_eq_of_lt eu.symm q
        exact lt_of_lt_of_eq q1 ev
      have hy : sz (p (p q_H0 q_x) q_y) < sz q_y := by
        have q := h0B.2
        have ev : sz H0 = sz (p (p q_H0 q_x) q_y) := congrArg sz (Eq.trans (p0) (rfl))
        have eu : sz x = sz q_y := congrArg sz (Eq.trans (p1) (rfl))
        have q1 : sz (p (p q_H0 q_x) q_y) < sz x := lt_of_eq_of_lt ev.symm q
        exact lt_of_lt_of_eq q1 eu
      exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
theorem nr1 (x y H0 : CM)
    (s0 : Step x y H0) :
    ¬ ∃ o, Code (p H0 x) y o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_y, q_H0, qs0, ha, hb, ho⟩
  cases s0 with
  | raw =>
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => (L (L q))) ha
      change x = (p q_x q_y) at e0
      have e1 := congrArg (fun q => (R (L q))) ha
      change y = q_x at e1
      have e2 := congrArg (fun q => (R q)) ha
      change x = q_y at e2
      have e3 := congrArg (fun q => q) hb
      change y = q_y at e3
      have cyc : q_y = (p q_x q_y) := Eq.symm (Eq.trans (Eq.symm (Eq.trans (Eq.trans (Eq.symm (rfl)) (Eq.trans (e0) (rfl))) (rfl))) (Eq.trans (e2) (rfl)))
      have hlt : sz q_y < sz (p q_x q_y) := sz_lt_p_right q_x q_y
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit h1 =>
      have hcB := code_bounds hc
      have h1B := code_bounds h1
      have p0 := congrArg (fun q => (L (L q))) ha
      change x = q_H0 at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => (R (L q))) ha
      change y = q_x at p1
      have z1 := congrArg sz p1
      have p2 := congrArg (fun q => (R q)) ha
      change x = q_y at p2
      have z2 := congrArg sz p2
      have p3 := congrArg (fun q => q) hb
      change y = q_y at p3
      have z3 := congrArg sz p3
      simp only [getOut, L, R, U, sz] at hcB h1B z0 z1 z2 z3
      omega
  | hit h0 =>
    cases qs0 with
    | raw =>
      have hcB := code_bounds hc
      have h0B := code_bounds h0
      have p0 := congrArg (fun q => (L q)) ha
      change H0 = (p (p q_x q_y) q_x) at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => (R q)) ha
      change x = q_y at p1
      have z1 := congrArg sz p1
      have p2 := congrArg (fun q => q) hb
      change y = q_y at p2
      have z2 := congrArg sz p2
      have hx := h0B.1
      rw [Eq.trans (p2) (rfl), Eq.trans (p1) (rfl)] at hx
      have selflt : sz q_y < sz q_y := hx
      exact (Nat.lt_irrefl _ selflt).elim
    | hit h1 =>
      have hcB := code_bounds hc
      have h0B := code_bounds h0
      have h1B := code_bounds h1
      have p0 := congrArg (fun q => (L q)) ha
      change H0 = (p q_H0 q_x) at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => (R q)) ha
      change x = q_y at p1
      have z1 := congrArg sz p1
      have p2 := congrArg (fun q => q) hb
      change y = q_y at p2
      have z2 := congrArg sz p2
      have hx := h0B.1
      rw [Eq.trans (p2) (rfl), Eq.trans (p1) (rfl)] at hx
      have selflt : sz q_y < sz q_y := hx
      exact (Nat.lt_irrefl _ selflt).elim
theorem source_holds (x y : CM) :
    x = (eval (eval (eval (eval x y) x) y) y) := by
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
  change x = (eval (eval (eval H0 x) y) y)
  have rawEq : (eval (eval (eval H0 x) y) y) = (eval (p (p H0 x) y) y) := by
    calc
      (eval (eval (eval H0 x) y) y) = (eval (eval (p H0 x) y) y) := congrArg (fun q => (eval (eval q y) y)) (eval_raw (nr0 x y H0 s0))
      _ = (eval (p (p H0 x) y) y) := congrArg (fun q => (eval q y)) (eval_raw (nr1 x y H0 s0))
  exact (eval_hit (Code.law x y H0 s0)).symm.trans rawEq.symm
noncomputable instance instMagma2 : Magma CM where op := eval
theorem nt0 : ¬ ∃ o, Code CM.e CM.e o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_y, q_H0, s0, ha, hb, ho⟩
  have bad := congrArg (fun q => (L q)) ha
  change CM.e = (p q_H0 q_x) at bad
  cases bad
theorem nt1 : ¬ ∃ o, Code CM.e (CM.p CM.e CM.e) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_y, q_H0, s0, ha, hb, ho⟩
  have bad := congrArg (fun q => (L q)) ha
  change CM.e = (p q_H0 q_x) at bad
  cases bad
theorem nt2 : ¬ ∃ o, Code CM.e (CM.p CM.e (CM.p CM.e CM.e)) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_y, q_H0, s0, ha, hb, ho⟩
  have bad := congrArg (fun q => (L q)) ha
  change CM.e = (p q_H0 q_x) at bad
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
    have hl : (eval CM.e (eval CM.e CM.e)) = (CM.p CM.e (CM.p CM.e CM.e)) := by
      calc
        (eval CM.e (eval CM.e CM.e)) = (eval CM.e (CM.p CM.e CM.e)) := congrArg (fun q => (eval CM.e q)) (eval_raw nt0)
        _ = (CM.p CM.e (CM.p CM.e CM.e)) := (eval_raw nt1)
    have hr : (eval CM.e (eval CM.e (eval CM.e CM.e))) = (CM.p CM.e (CM.p CM.e (CM.p CM.e CM.e))) := by
      calc
        (eval CM.e (eval CM.e (eval CM.e CM.e))) = (eval CM.e (eval CM.e (CM.p CM.e CM.e))) := congrArg (fun q => (eval CM.e (eval CM.e q))) (eval_raw nt0)
        _ = (eval CM.e (CM.p CM.e (CM.p CM.e CM.e))) := congrArg (fun q => (eval CM.e q)) (eval_raw nt1)
        _ = (CM.p CM.e (CM.p CM.e (CM.p CM.e CM.e))) := (eval_raw nt2)
    have bad2 := hl.symm.trans (bad.trans hr)
    exact Bool.noConfusion (congrArg (fun q => match (R (R q)) with | e => false | k _ => false | p _ _ => true) bad2)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_3069_to_53807 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_3069_to_53807
