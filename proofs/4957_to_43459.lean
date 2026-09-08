-- Equation4957 → Equation43459
-- Recorded verdict: false
-- Premise: x = y ◇ (x ◇ (y ◇ (z ◇ (x ◇ z))))
-- Conclusion: x ◇ x = y ◇ ((z ◇ z) ◇ (w ◇ u))
-- Original submission SHA-256: 4b60c8fcfb4ae25ccf741f554323d3fb5fb564b4a1e1cd21f5e8c467adaf3cb0
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (x ◇ (y ◇ (z ◇ (x ◇ z))))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ x = y ◇ ((z ◇ z) ◇ (w ◇ u))
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
  | law (x v0 v1 H0 : CM)
      (s0 : Step v0 x H0) :
      Code (p (p (p H0 v0) v1) x) v1 x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_H0 : CM, Step q_v0 q_x q_H0 ∧ a = (p (p (p q_H0 q_v0) q_v1) q_x) ∧ b = q_v1 ∧ o = q_x := by
  cases h
  exact ⟨_, _, _, _, by assumption, rfl, rfl, rfl⟩
def getOut (a b : CM) : CM := (R a)
theorem code_get {a b o : CM} (h : Code a b o) : getOut a b = o := by
  cases h <;> rfl
theorem code_unique {a b o q : CM} (h : Code a b o) (k : Code a b q) : o = q :=
  (code_get h).symm.trans (code_get k)
theorem code_bounds {a b o : CM} (h : Code a b o) : sz b < sz a ∧ sz o < sz a := by
  rcases code_shape h with ⟨q_x, q_v0, q_v1, q_H0, s0, ha, hb, ho⟩
  subst a
  subst b
  subst o
  exact ⟨Nat.lt_trans (sz_lt_p_right (p q_H0 q_v0) q_v1) (sz_lt_p_left (p (p q_H0 q_v0) q_v1) q_x), sz_lt_p_right (p (p q_H0 q_v0) q_v1) q_x⟩

theorem step_ne_first {a b : CM} : ¬ Step a b a := by
  intro h
  cases h with
  | hit hc =>
    have hb := (code_bounds hc).2
    omega
theorem step_bound {a b o : CM} (h : Step a b o) :
    sz b < sz (p o a) := by
  cases h with
  | raw => simp [sz] <;> omega
  | hit hc =>
    have hb := (code_bounds hc).1
    simp [sz] at hb ⊢ <;> omega

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
theorem nr0 (x v0 v1 H0 : CM)
    (s0 : Step v0 x H0) :
    ¬ ∃ o, Code H0 v0 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have s0B := step_bound s0
  cases s0 with
  | raw =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => (L q)) ha
      change v0 = (p (p (p q_v0 q_x) q_v0) q_v1) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change x = q_x at e1
      have e2 := congrArg (fun q => q) hb
      change v0 = q_v1 at e2
      have cyc : q_v1 = (p (p (p q_v0 q_x) q_v0) q_v1) := Eq.symm (Eq.trans (Eq.symm (Eq.trans (Eq.trans (Eq.symm (rfl)) (Eq.trans (e0) (rfl))) (rfl))) (Eq.trans (e2) (rfl)))
      have hlt : sz q_v1 < sz (p (p (p q_v0 q_x) q_v0) q_v1) := sz_lt_p_right (p (p q_v0 q_x) q_v0) q_v1
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have e0 := congrArg (fun q => (L q)) ha
      change v0 = (p (p q_H0 q_v0) q_v1) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change x = q_x at e1
      have e2 := congrArg (fun q => q) hb
      change v0 = q_v1 at e2
      have cyc : q_v1 = (p (p q_H0 q_v0) q_v1) := Eq.symm (Eq.trans (Eq.symm (Eq.trans (Eq.trans (Eq.symm (rfl)) (Eq.trans (e0) (rfl))) (rfl))) (Eq.trans (e2) (rfl)))
      have hlt : sz q_v1 < sz (p (p q_H0 q_v0) q_v1) := sz_lt_p_right (p q_H0 q_v0) q_v1
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit s0h =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have hcB := code_bounds hc
      have s0hB := code_bounds s0h
      have s0B := s0B
      have qs0B := qs0B
      have p0 := ha
      change H0 = (p (p (p (p q_v0 q_x) q_v0) q_v1) q_x) at p0
      have z0 := congrArg sz p0
      have p1 := hb
      change v0 = q_v1 at p1
      have z1 := congrArg sz p1
      have p2 := ho
      change o = q_x at p2
      have z2 := congrArg sz p2
      have hx : sz q_v1 < sz (p (p (p (p q_v0 q_x) q_v0) q_v1) q_x) := by
        have q := hcB.1
        have eu : sz v0 = sz q_v1 := congrArg sz (Eq.trans (p1) (rfl))
        have ev : sz H0 = sz (p (p (p (p q_v0 q_x) q_v0) q_v1) q_x) := congrArg sz (Eq.trans (p0) (rfl))
        have q1 : sz q_v1 < sz H0 := lt_of_eq_of_lt eu.symm q
        exact lt_of_lt_of_eq q1 ev
      have hy : sz (p (p (p (p q_v0 q_x) q_v0) q_v1) q_x) < sz q_v1 := by
        have q := s0hB.2
        have ev : sz H0 = sz (p (p (p (p q_v0 q_x) q_v0) q_v1) q_x) := congrArg sz (Eq.trans (p0) (rfl))
        have eu : sz v0 = sz q_v1 := congrArg sz (Eq.trans (p1) (rfl))
        have q1 : sz (p (p (p (p q_v0 q_x) q_v0) q_v1) q_x) < sz v0 := lt_of_eq_of_lt ev.symm q
        exact lt_of_lt_of_eq q1 eu
      exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
    | hit qs0h =>
      have hcB := code_bounds hc
      have s0hB := code_bounds s0h
      have qs0hB := code_bounds qs0h
      have s0B := s0B
      have qs0B := qs0B
      have p0 := ha
      change H0 = (p (p (p q_H0 q_v0) q_v1) q_x) at p0
      have z0 := congrArg sz p0
      have p1 := hb
      change v0 = q_v1 at p1
      have z1 := congrArg sz p1
      have p2 := ho
      change o = q_x at p2
      have z2 := congrArg sz p2
      have hx : sz q_v1 < sz (p (p (p q_H0 q_v0) q_v1) q_x) := by
        have q := hcB.1
        have eu : sz v0 = sz q_v1 := congrArg sz (Eq.trans (p1) (rfl))
        have ev : sz H0 = sz (p (p (p q_H0 q_v0) q_v1) q_x) := congrArg sz (Eq.trans (p0) (rfl))
        have q1 : sz q_v1 < sz H0 := lt_of_eq_of_lt eu.symm q
        exact lt_of_lt_of_eq q1 ev
      have hy : sz (p (p (p q_H0 q_v0) q_v1) q_x) < sz q_v1 := by
        have q := s0hB.2
        have ev : sz H0 = sz (p (p (p q_H0 q_v0) q_v1) q_x) := congrArg sz (Eq.trans (p0) (rfl))
        have eu : sz v0 = sz q_v1 := congrArg sz (Eq.trans (p1) (rfl))
        have q1 : sz (p (p (p q_H0 q_v0) q_v1) q_x) < sz v0 := lt_of_eq_of_lt ev.symm q
        exact lt_of_lt_of_eq q1 eu
      exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
theorem nr1 (x v0 v1 H0 : CM)
    (s0 : Step v0 x H0) :
    ¬ ∃ o, Code (p H0 v0) v1 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have s0B := step_bound s0
  cases s0 with
  | raw =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => (L (L q))) ha
      change v0 = (p (p q_v0 q_x) q_v0) at e0
      have e1 := congrArg (fun q => (R (L q))) ha
      change x = q_v1 at e1
      have e2 := congrArg (fun q => (R q)) ha
      change v0 = q_x at e2
      have e3 := congrArg (fun q => q) hb
      change v1 = q_v1 at e3
      have cyc : q_x = (p (p q_v0 q_x) q_v0) := Eq.symm (Eq.trans (Eq.symm (Eq.trans (Eq.trans (Eq.symm (rfl)) (Eq.trans (e0) (rfl))) (rfl))) (Eq.trans (e2) (rfl)))
      have hlt : sz q_x < sz (p (p q_v0 q_x) q_v0) := Nat.lt_trans (sz_lt_p_right q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) q_v0)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have hcB := code_bounds hc
      have qs0hB := code_bounds qs0h
      have s0B := s0B
      have qs0B := qs0B
      have p0 := congrArg (fun q => (L (L q))) (ha)
      change v0 = (p q_H0 q_v0) at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => (R (L q))) (ha)
      change x = q_v1 at p1
      have z1 := congrArg sz p1
      have p2 := congrArg (fun q => (R q)) (ha)
      change v0 = q_x at p2
      have z2 := congrArg sz p2
      have p3 := hb
      change v1 = q_v1 at p3
      have z3 := congrArg sz p3
      have p4 := ho
      change o = q_x at p4
      have z4 := congrArg sz p4
      have badlt : sz q_v0 < sz q_x := by
        rw [Eq.trans (p2.symm) (Eq.trans (p0) (rfl))]
        exact sz_lt_p_right q_H0 q_v0
      exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) qs0hB.1).elim
  | hit s0h =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have hcB := code_bounds hc
      have s0hB := code_bounds s0h
      have s0B := s0B
      have qs0B := qs0B
      have p0 := congrArg (fun q => (L q)) (ha)
      change H0 = (p (p (p q_v0 q_x) q_v0) q_v1) at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => (R q)) (ha)
      change v0 = q_x at p1
      have z1 := congrArg sz p1
      have p2 := hb
      change v1 = q_v1 at p2
      have z2 := congrArg sz p2
      have p3 := ho
      change o = q_x at p3
      have z3 := congrArg sz p3
      have badlt : sz v0 < sz H0 := by
        rw [Eq.trans (p1) (rfl), Eq.trans (p0) (rfl)]
        exact Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) q_v0)) (sz_lt_p_left (p (p q_v0 q_x) q_v0) q_v1)
      exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) s0hB.2).elim
    | hit qs0h =>
      have hcB := code_bounds hc
      have s0hB := code_bounds s0h
      have qs0hB := code_bounds qs0h
      have s0B := s0B
      have qs0B := qs0B
      have p0 := congrArg (fun q => (L q)) (ha)
      change H0 = (p (p q_H0 q_v0) q_v1) at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => (R q)) (ha)
      change v0 = q_x at p1
      have z1 := congrArg sz p1
      have p2 := hb
      change v1 = q_v1 at p2
      have z2 := congrArg sz p2
      have p3 := ho
      change o = q_x at p3
      have z3 := congrArg sz p3
      simp only [getOut, L, R, U, sz] at hcB s0hB qs0hB z0 z1 z2 z3
      omega
theorem nr2 (x v0 v1 H0 : CM)
    (s0 : Step v0 x H0) :
    ¬ ∃ o, Code (p (p H0 v0) v1) x o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have s0B := step_bound s0
  cases s0 with
  | raw =>
    have he : q_H0 = q_v0 := Eq.trans (Eq.trans (Eq.trans (Eq.symm (Eq.trans (Eq.trans (Eq.symm (rfl)) (Eq.trans (congrArg (fun q => (L (L (L q)))) (ha)) (rfl))) (rfl))) (Eq.trans (congrArg (fun q => (R (L q))) (ha)) (rfl))) (rfl)) (Eq.symm (Eq.trans (Eq.trans (Eq.symm (Eq.trans (Eq.trans (Eq.symm (rfl)) (Eq.trans (congrArg (fun q => (R (L (L q)))) (ha)) (rfl))) (rfl))) (Eq.trans (hb) (rfl))) (rfl)))
    exact step_ne_first (by simpa only [he] using qs0)
  | hit s0h =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have hcB := code_bounds hc
      have s0hB := code_bounds s0h
      have s0B := s0B
      have qs0B := qs0B
      have p0 := congrArg (fun q => (L (L q))) (ha)
      change H0 = (p (p q_v0 q_x) q_v0) at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => (R (L q))) (ha)
      change v0 = q_v1 at p1
      have z1 := congrArg sz p1
      have p2 := congrArg (fun q => (R q)) (ha)
      change v1 = q_x at p2
      have z2 := congrArg sz p2
      have p3 := hb
      change x = q_v1 at p3
      have z3 := congrArg sz p3
      have p4 := ho
      change o = q_x at p4
      have z4 := congrArg sz p4
      have hx := s0hB.1
      rw [Eq.trans (p3) (rfl), Eq.trans (p1) (rfl)] at hx
      have selflt : sz q_v1 < sz q_v1 := hx
      exact (Nat.lt_irrefl _ selflt).elim
    | hit qs0h =>
      have hcB := code_bounds hc
      have s0hB := code_bounds s0h
      have qs0hB := code_bounds qs0h
      have s0B := s0B
      have qs0B := qs0B
      have p0 := congrArg (fun q => (L (L q))) (ha)
      change H0 = (p q_H0 q_v0) at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => (R (L q))) (ha)
      change v0 = q_v1 at p1
      have z1 := congrArg sz p1
      have p2 := congrArg (fun q => (R q)) (ha)
      change v1 = q_x at p2
      have z2 := congrArg sz p2
      have p3 := hb
      change x = q_v1 at p3
      have z3 := congrArg sz p3
      have p4 := ho
      change o = q_x at p4
      have z4 := congrArg sz p4
      have hx := s0hB.1
      rw [Eq.trans (p3) (rfl), Eq.trans (p1) (rfl)] at hx
      have selflt : sz q_v1 < sz q_v1 := hx
      exact (Nat.lt_irrefl _ selflt).elim
theorem source_holds (x v0 v1 : CM) :
    x = (eval (eval (eval (eval (eval v0 x) v0) v1) x) v1) := by
  let H0 := eval v0 x
  have e0a : v0 = v0 := by
    change v0 = v0
    rfl
  have e0b : x = x := by
    change x = x
    rfl
  have s0 : Step v0 x H0 := by
    rw [← e0a, ← e0b]
    exact eval_step v0 x
  change x = (eval (eval (eval (eval H0 v0) v1) x) v1)
  have rawEq : (eval (eval (eval (eval H0 v0) v1) x) v1) = (eval (p (p (p H0 v0) v1) x) v1) := by
    calc
      (eval (eval (eval (eval H0 v0) v1) x) v1) = (eval (eval (eval (p H0 v0) v1) x) v1) := congrArg (fun q => (eval (eval (eval q v1) x) v1)) (eval_raw (nr0 x v0 v1 H0 s0))
      _ = (eval (eval (p (p H0 v0) v1) x) v1) := congrArg (fun q => (eval (eval q x) v1)) (eval_raw (nr1 x v0 v1 H0 s0))
      _ = (eval (p (p (p H0 v0) v1) x) v1) := congrArg (fun q => (eval q v1)) (eval_raw (nr2 x v0 v1 H0 s0))
  exact (eval_hit (Code.law x v0 v1 H0 s0)).symm.trans rawEq.symm
noncomputable instance instMagma2 : Magma CM where op a b := eval b a
theorem nt0 : ¬ ∃ o, Code CM.e CM.e o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, s0, ha, hb, ho⟩
  have bad := congrArg (fun q => (L (L q))) ha
  change CM.e = (p q_H0 q_v0) at bad
  cases bad
theorem nt1 : ¬ ∃ o, Code (CM.p CM.e CM.e) (CM.p CM.e CM.e) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, s0, ha, hb, ho⟩
  have bad := congrArg (fun q => (L (L q))) ha
  change CM.e = (p q_H0 q_v0) at bad
  cases bad
theorem nt2 : ¬ ∃ o, Code (CM.p (CM.p CM.e CM.e) (CM.p CM.e CM.e)) CM.e o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, s0, ha, hb, ho⟩
  have bad := congrArg (fun q => (L (L q))) ha
  change CM.e = (p q_H0 q_v0) at bad
  cases bad
end CM
end submission
open submission
open submission.CM
noncomputable def submission : Goal := by
  refine ⟨CM, CM.instMagma2, ?_, ?_⟩
  · intro q0 q1 q2
    exact CM.source_holds q0 q2 q1
  · intro target
    have bad := target CM.e CM.e CM.e CM.e CM.e
    have hl : (eval CM.e CM.e) = (CM.p CM.e CM.e) := (eval_raw nt0)
    have hr : (eval (eval (eval CM.e CM.e) (eval CM.e CM.e)) CM.e) = (CM.p (CM.p (CM.p CM.e CM.e) (CM.p CM.e CM.e)) CM.e) := by
      calc
        (eval (eval (eval CM.e CM.e) (eval CM.e CM.e)) CM.e) = (eval (eval (CM.p CM.e CM.e) (eval CM.e CM.e)) CM.e) := congrArg (fun q => (eval (eval q (eval CM.e CM.e)) CM.e)) (eval_raw nt0)
        _ = (eval (eval (CM.p CM.e CM.e) (CM.p CM.e CM.e)) CM.e) := congrArg (fun q => (eval (eval (CM.p CM.e CM.e) q) CM.e)) (eval_raw nt0)
        _ = (eval (CM.p (CM.p CM.e CM.e) (CM.p CM.e CM.e)) CM.e) := congrArg (fun q => (eval q CM.e)) (eval_raw nt1)
        _ = (CM.p (CM.p (CM.p CM.e CM.e) (CM.p CM.e CM.e)) CM.e) := (eval_raw nt2)
    have bad2 := hl.symm.trans (bad.trans hr)
    exact Bool.noConfusion (congrArg (fun q => match (L q) with | e => false | k _ => false | p _ _ => true) bad2)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_4957_to_43459 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_4957_to_43459
