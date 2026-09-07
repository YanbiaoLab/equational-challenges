-- Equation7594 → Equation8607
-- Recorded verdict: false
-- Premise: x = y ◇ (x ◇ ((y ◇ (z ◇ z)) ◇ x))
-- Conclusion: x = y ◇ (y ◇ (((y ◇ y) ◇ y) ◇ x))
-- Original submission SHA-256: 9b4d65f005fba98a43ed3eb934bf87b5af2e199be0919202ff3215fa70447572
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (x ◇ ((y ◇ (z ◇ z)) ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = y ◇ (y ◇ (((y ◇ y) ◇ y) ◇ x))
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
      (s0 : Step (p v0 (p v1 v1)) x H0) :
      Code v0 (p x H0) x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_H0 : CM, Step (p q_v0 (p q_v1 q_v1)) q_x q_H0 ∧ a = q_v0 ∧ b = (p q_x q_H0) ∧ o = q_x := by
  cases h with
  | law x v0 v1 H0 s0 =>
    exact ⟨_, _, _, _, by assumption, rfl, rfl, rfl⟩
def getOut (a b : CM) : CM := (L b)
theorem code_get {a b o : CM} (h : Code a b o) : getOut a b = o := by
  cases h <;> rfl
theorem code_unique {a b o q : CM} (h : Code a b o) (k : Code a b q) : o = q :=
  (code_get h).symm.trans (code_get k)
def CodeArg :=
  PSigma fun a : CM => PSigma fun b : CM => PSigma fun o : CM => Code a b o
theorem code_bounds_core (q : CodeArg) : sz q.1 < sz q.2.1 ∧ sz q.2.2.1 < sz q.2.1 := by
  rcases q with ⟨a, b, o, h⟩
  cases h with
  | law x v0 v1 H0 s0 =>
    cases s0 with
    | raw =>
      simp only [getOut, L, R, U, sz] <;> omega
    | hit s0h =>
      have s0hB := code_bounds_core ⟨_, _, _, s0h⟩
      simp only [getOut, L, R, U, sz] at s0hB ⊢ <;> omega
termination_by sz q.2.1
decreasing_by simp_all only [sz] <;> omega
theorem code_bounds {a b o : CM} (h : Code a b o) : sz a < sz b ∧ sz o < sz b :=
  code_bounds_core ⟨a, b, o, h⟩
theorem step_ne_second {a b : CM} : ¬ Step a b b := by
  intro h
  cases h with
  | hit hc =>
    have hb := (code_bounds hc).2
    omega
theorem step_bound {a b o : CM} (h : Step a b o) :
    sz a < sz (p o b) := by
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
theorem nr0 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code v1 v1 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have qs0B := step_bound qs0
  cases qs0 with
  | raw =>
    have e0 := congrArg (fun q => q) ha
    change v1 = q_v0 at e0
    have e1 := congrArg (fun q => q) hb
    change v1 = (p q_x (p (p q_v0 (p q_v1 q_v1)) q_x)) at e1
    have cyc : q_v0 = (p q_x (p (p q_v0 (p q_v1 q_v1)) q_x)) := Eq.trans (Eq.symm (Eq.trans (Eq.trans (Eq.symm (rfl)) (Eq.trans (e0) (rfl))) (rfl))) (Eq.trans (e1) (rfl))
    have hlt : sz q_v0 < sz (p q_x (p (p q_v0 (p q_v1 q_v1)) q_x)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 (p q_v1 q_v1)) (sz_lt_p_left (p q_v0 (p q_v1 q_v1)) q_x)) (sz_lt_p_right q_x (p (p q_v0 (p q_v1 q_v1)) q_x))
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have hcB := code_bounds hc
    have qs0hB := code_bounds qs0h
    have qs0B := qs0B
    have p0 := ha
    change v1 = q_v0 at p0
    have z0 := congrArg sz p0
    have p1 := hb
    change v1 = (p q_x q_H0) at p1
    have z1 := congrArg sz p1
    have p2 := ho
    change o = q_x at p2
    have z2 := congrArg sz p2
    simp only [getOut, L, R, U, sz] at hcB qs0hB qs0B z0 z1 z2
    omega
theorem nr1 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code v0 (p v1 v1) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have he : q_H0 = q_x := Eq.trans (rfl) (Eq.symm (Eq.trans (Eq.trans (Eq.symm (Eq.trans (Eq.trans (Eq.symm (rfl)) (Eq.trans (congrArg (fun q => (L q)) (hb)) (rfl))) (rfl))) (Eq.trans (congrArg (fun q => (R q)) (hb)) (rfl))) (rfl)))
  exact step_ne_second (by simpa only [he] using qs0)
theorem nr2 (x v0 v1 H0 : CM)
    (s0 : Step (p v0 (p v1 v1)) x H0) :
    ¬ ∃ o, Code x H0 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have s0B := step_bound s0
  cases s0 with
  | raw =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change x = q_v0 at e0
      have e1 := congrArg (fun q => (L q)) hb
      change (p v0 (p v1 v1)) = q_x at e1
      have e2 := congrArg (fun q => (R q)) hb
      change x = (p (p q_v0 (p q_v1 q_v1)) q_x) at e2
      have cyc : q_v0 = (p (p q_v0 (p q_v1 q_v1)) (p v0 (p v1 v1))) := Eq.trans (Eq.symm (Eq.trans (Eq.trans (Eq.symm (rfl)) (Eq.trans (e0) (rfl))) (rfl))) (Eq.trans (e2) (congrArg (fun q => p (p q_v0 (p q_v1 q_v1)) q) (Eq.trans (Eq.symm (Eq.trans (Eq.symm (rfl)) (Eq.trans (e1) (rfl)))) (rfl))))
      have hlt : sz q_v0 < sz (p (p q_v0 (p q_v1 q_v1)) (p v0 (p v1 v1))) := Nat.lt_trans (sz_lt_p_left q_v0 (p q_v1 q_v1)) (sz_lt_p_left (p q_v0 (p q_v1 q_v1)) (p v0 (p v1 v1)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      rcases code_shape qs0h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0s0, u0a, u0b, u0o⟩
      have u0s0B := step_bound u0s0
      cases u0s0 with
      | raw =>
        have cyc : q_H0 = (p (p q_H0 (p q_v1 q_v1)) (p u0_v1 u0_v1)) := Eq.trans (Eq.symm (rfl)) (Eq.trans (u0o) (Eq.trans (Eq.symm (Eq.trans (Eq.symm (Eq.trans (Eq.trans (Eq.symm (rfl)) (Eq.trans (congrArg (fun q => L q) (Eq.trans (Eq.symm (rfl)) (Eq.trans (congrArg (fun q => R q) (Eq.trans (Eq.symm (Eq.trans (Eq.symm (Eq.trans (Eq.symm (rfl)) (Eq.trans (congrArg (fun q => (L q)) (hb)) (rfl)))) (rfl))) (Eq.trans (u0b) (congrArg (fun q => p u0_x q) (congrArg (fun q => p q u0_x) (congrArg (fun q => p q (p u0_v1 u0_v1)) (Eq.trans (Eq.symm (Eq.trans (Eq.symm (congrArg (fun q => p q (p q_v1 q_v1)) (Eq.trans (Eq.trans (Eq.symm (Eq.trans (Eq.trans (Eq.symm (rfl)) (Eq.trans (ha) (rfl))) (rfl))) (Eq.trans (congrArg (fun q => (R q)) (hb)) (rfl))) (rfl)))) (Eq.trans (u0a) (rfl)))) (rfl)))))))) (rfl)))) (rfl))) (rfl))) (Eq.trans (congrArg (fun q => R q) (Eq.trans (Eq.symm (rfl)) (Eq.trans (congrArg (fun q => R q) (Eq.trans (Eq.symm (Eq.trans (Eq.symm (Eq.trans (Eq.symm (rfl)) (Eq.trans (congrArg (fun q => (L q)) (hb)) (rfl)))) (rfl))) (Eq.trans (u0b) (congrArg (fun q => p u0_x q) (congrArg (fun q => p q u0_x) (congrArg (fun q => p q (p u0_v1 u0_v1)) (Eq.trans (Eq.symm (Eq.trans (Eq.symm (congrArg (fun q => p q (p q_v1 q_v1)) (Eq.trans (Eq.trans (Eq.symm (Eq.trans (Eq.trans (Eq.symm (rfl)) (Eq.trans (ha) (rfl))) (rfl))) (Eq.trans (congrArg (fun q => (R q)) (hb)) (rfl))) (rfl)))) (Eq.trans (u0a) (rfl)))) (rfl)))))))) (rfl)))) (rfl)))) (rfl)))
        have hlt : sz q_H0 < sz (p (p q_H0 (p q_v1 q_v1)) (p u0_v1 u0_v1)) := Nat.lt_trans (sz_lt_p_left q_H0 (p q_v1 q_v1)) (sz_lt_p_left (p q_H0 (p q_v1 q_v1)) (p u0_v1 u0_v1))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit u0s0h =>
        have hcB := code_bounds hc
        have qs0hB := code_bounds qs0h
        have u0s0hB := code_bounds u0s0h
        have s0B := s0B
        have qs0B := qs0B
        have u0s0B := u0s0B
        have p0 := ha
        change x = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (L q)) (hb)
        change (p v0 (p v1 v1)) = q_x at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (R q)) (hb)
        change x = q_H0 at p2
        have z2 := congrArg sz p2
        have p3 := ho
        change o = q_x at p3
        have z3 := congrArg sz p3
        have p4 := u0a
        change (p q_v0 (p q_v1 q_v1)) = u0_v0 at p4
        have z4 := congrArg sz p4
        have p5 := u0b
        change q_x = (p u0_x u0_H0) at p5
        have z5 := congrArg sz p5
        have p6 := u0o
        change q_H0 = u0_x at p6
        have z6 := congrArg sz p6
        simp only [getOut, L, R, U, sz] at hcB qs0hB u0s0hB s0B qs0B u0s0B z0 z1 z2 z3 z4 z5 z6
        omega
  | hit s0h =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have hcB := code_bounds hc
      have s0hB := code_bounds s0h
      have s0B := s0B
      have qs0B := qs0B
      have p0 := ha
      change x = q_v0 at p0
      have z0 := congrArg sz p0
      have p1 := hb
      change H0 = (p q_x (p (p q_v0 (p q_v1 q_v1)) q_x)) at p1
      have z1 := congrArg sz p1
      have p2 := ho
      change o = q_x at p2
      have z2 := congrArg sz p2
      simp only [getOut, L, R, U, sz] at hcB s0hB s0B qs0B z0 z1 z2
      omega
    | hit qs0h =>
      have hcB := code_bounds hc
      have s0hB := code_bounds s0h
      have qs0hB := code_bounds qs0h
      have s0B := s0B
      have qs0B := qs0B
      have p0 := ha
      change x = q_v0 at p0
      have z0 := congrArg sz p0
      have p1 := hb
      change H0 = (p q_x q_H0) at p1
      have z1 := congrArg sz p1
      have p2 := ho
      change o = q_x at p2
      have z2 := congrArg sz p2
      simp only [getOut, L, R, U, sz] at hcB s0hB qs0hB s0B qs0B z0 z1 z2
      omega
theorem source_holds (x v0 v1 : CM) :
    x = (eval v0 (eval x (eval (eval v0 (eval v1 v1)) x))) := by
  let H0 := eval (eval v0 (eval v1 v1)) x
  have e0a : (eval v0 (eval v1 v1)) = (p v0 (p v1 v1)) := by
    change (eval v0 (eval v1 v1)) = (p v0 (p v1 v1))
    calc
      (eval v0 (eval v1 v1)) = (eval v0 (p v1 v1)) := congrArg (fun q => (eval v0 q)) (eval_raw (nr0 x v0 v1))
      _ = (p v0 (p v1 v1)) := (eval_raw (nr1 x v0 v1))
  have e0b : x = x := by
    change x = x
    rfl
  have s0 : Step (p v0 (p v1 v1)) x H0 := by
    rw [← e0a, ← e0b]
    exact eval_step (eval v0 (eval v1 v1)) x
  change x = (eval v0 (eval x H0))
  have rawEq : (eval v0 (eval x H0)) = (eval v0 (p x H0)) := congrArg (fun q => (eval v0 q)) (eval_raw (nr2 x v0 v1 H0 s0))
  exact (eval_hit (Code.law x v0 v1 H0 s0)).symm.trans rawEq.symm
noncomputable instance instMagma2 : Magma CM where op := eval
theorem nt0 : ¬ ∃ o, Code CM.e CM.e o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, s0, ha, hb, ho⟩
  have bad := congrArg (fun q => q) hb
  change CM.e = (p q_x q_H0) at bad
  cases bad
theorem nt1 : ¬ ∃ o, Code (CM.p CM.e CM.e) CM.e o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, s0, ha, hb, ho⟩
  have bad := congrArg (fun q => q) hb
  change CM.e = (p q_x q_H0) at bad
  cases bad
theorem nt2 : ¬ ∃ o, Code (CM.p (CM.p CM.e CM.e) CM.e) CM.e o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, s0, ha, hb, ho⟩
  have bad := congrArg (fun q => q) hb
  change CM.e = (p q_x q_H0) at bad
  cases bad
theorem nt3 : ¬ ∃ o, Code CM.e (CM.p (CM.p (CM.p CM.e CM.e) CM.e) CM.e) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, s0, ha, hb, ho⟩
  have s0B := step_bound s0
  cases s0 with
  | raw =>
    have hcB := code_bounds hc
    have s0B := s0B
    have p0 := ha
    change e = q_v0 at p0
    have z0 := congrArg sz p0
    have p1 := congrArg (fun q => (L q)) (hb)
    change (p (p e e) e) = q_x at p1
    have z1 := congrArg sz p1
    have p2 := congrArg (fun q => (R q)) (hb)
    change e = (p (p q_v0 (p q_v1 q_v1)) q_x) at p2
    have z2 := congrArg sz p2
    have p3 := ho
    change o = q_x at p3
    have z3 := congrArg sz p3
    simp only [getOut, L, R, U, sz] at hcB s0B z0 z1 z2 z3
    omega
  | hit s0h =>
    have hcB := code_bounds hc
    have s0hB := code_bounds s0h
    have s0B := s0B
    have p0 := ha
    change e = q_v0 at p0
    have z0 := congrArg sz p0
    have p1 := congrArg (fun q => (L q)) (hb)
    change (p (p e e) e) = q_x at p1
    have z1 := congrArg sz p1
    have p2 := congrArg (fun q => (R q)) (hb)
    change e = q_H0 at p2
    have z2 := congrArg sz p2
    have p3 := ho
    change o = q_x at p3
    have z3 := congrArg sz p3
    simp only [getOut, L, R, U, sz] at hcB s0hB s0B z0 z1 z2 z3
    omega
theorem nt4 : ¬ ∃ o, Code CM.e (CM.p CM.e (CM.p (CM.p (CM.p CM.e CM.e) CM.e) CM.e)) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, s0, ha, hb, ho⟩
  have s0B := step_bound s0
  cases s0 with
  | raw =>
    have hcB := code_bounds hc
    have s0B := s0B
    have p0 := ha
    change e = q_v0 at p0
    have z0 := congrArg sz p0
    have p1 := congrArg (fun q => (L q)) (hb)
    change e = q_x at p1
    have z1 := congrArg sz p1
    have p2 := congrArg (fun q => (L (L (R q)))) (hb)
    change (p e e) = q_v0 at p2
    have z2 := congrArg sz p2
    have p3 := congrArg (fun q => (R (L (R q)))) (hb)
    change e = (p q_v1 q_v1) at p3
    have z3 := congrArg sz p3
    have p4 := congrArg (fun q => (R (R q))) (hb)
    change e = q_x at p4
    have z4 := congrArg sz p4
    have p5 := ho
    change o = q_x at p5
    have z5 := congrArg sz p5
    simp only [getOut, L, R, U, sz] at hcB s0B z0 z1 z2 z3 z4 z5
    omega
  | hit s0h =>
    have hcB := code_bounds hc
    have s0hB := code_bounds s0h
    have s0B := s0B
    have p0 := ha
    change e = q_v0 at p0
    have z0 := congrArg sz p0
    have p1 := congrArg (fun q => (L q)) (hb)
    change e = q_x at p1
    have z1 := congrArg sz p1
    have p2 := congrArg (fun q => (R q)) (hb)
    change (p (p (p e e) e) e) = q_H0 at p2
    have z2 := congrArg sz p2
    have p3 := ho
    change o = q_x at p3
    have z3 := congrArg sz p3
    simp only [getOut, L, R, U, sz] at hcB s0hB s0B z0 z1 z2 z3
    omega
end CM
end submission
open submission
open submission.CM
noncomputable def submission : Goal := by
  refine ⟨CM, CM.instMagma2, ?_, ?_⟩
  · intro x v0 v1
    exact CM.source_holds x v0 v1
  · intro target
    have bad := target CM.e CM.e
    have hl : CM.e = CM.e := rfl
    have hr : (eval CM.e (eval CM.e (eval (eval (eval CM.e CM.e) CM.e) CM.e))) = (CM.p CM.e (CM.p CM.e (CM.p (CM.p (CM.p CM.e CM.e) CM.e) CM.e))) := by
      calc
        (eval CM.e (eval CM.e (eval (eval (eval CM.e CM.e) CM.e) CM.e))) = (eval CM.e (eval CM.e (eval (eval (CM.p CM.e CM.e) CM.e) CM.e))) := congrArg (fun q => (eval CM.e (eval CM.e (eval (eval q CM.e) CM.e)))) (eval_raw nt0)
        _ = (eval CM.e (eval CM.e (eval (CM.p (CM.p CM.e CM.e) CM.e) CM.e))) := congrArg (fun q => (eval CM.e (eval CM.e (eval q CM.e)))) (eval_raw nt1)
        _ = (eval CM.e (eval CM.e (CM.p (CM.p (CM.p CM.e CM.e) CM.e) CM.e))) := congrArg (fun q => (eval CM.e (eval CM.e q))) (eval_raw nt2)
        _ = (eval CM.e (CM.p CM.e (CM.p (CM.p (CM.p CM.e CM.e) CM.e) CM.e))) := congrArg (fun q => (eval CM.e q)) (eval_raw nt3)
        _ = (CM.p CM.e (CM.p CM.e (CM.p (CM.p (CM.p CM.e CM.e) CM.e) CM.e))) := (eval_raw nt4)
    have bad2 := hl.symm.trans (bad.trans hr)
    exact Bool.noConfusion (congrArg (fun q => match q with | e => false | k _ => false | p _ _ => true) bad2)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_7594_to_8607 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_7594_to_8607
