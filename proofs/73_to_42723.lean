-- Equation73 → Equation42723
-- Recorded verdict: false
-- Premise: x = y ◇ (y ◇ (x ◇ y))
-- Conclusion: x ◇ y = x ◇ (z ◇ ((z ◇ y) ◇ z))
-- Original submission SHA-256: 8febf4f9994e7fbef12a7b7c8dbb1229820717a11fe213b27d55ce2972b7b9de
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = y ◇ (y ◇ (x ◇ y))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = x ◇ (z ◇ ((z ◇ y) ◇ z))
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
      Code y (p y H0) x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_y q_H0 : CM, Step q_x q_y q_H0 ∧ a = q_y ∧ b = (p q_y q_H0) ∧ o = q_x := by
  cases h with
  | law x y H0 s0 =>
    exact ⟨_, _, _, by assumption, rfl, rfl, rfl⟩
def getKey (c : CM) : CM := (L c)
theorem code_key {a b o : CM} (h : Code a b o) : getKey b = a := by
  cases h <;> rfl
theorem code_key_unique {a q b o : CM} (h : Code a b o) (k : Code q b o) : a = q :=
  (code_key h).symm.trans (code_key k)
theorem code_key_small {a b o : CM} (h : Code a b o) : sz a < sz b := by
  rcases code_shape h with ⟨q_x, q_y, q_H0, s0, ha, hb, ho⟩
  subst a
  subst b
  exact sz_lt_p_left q_y q_H0
theorem code_bounds {a b o : CM} (h : Code a b o) :
    sz a < sz b ∧ sz o < sz b := by
  rcases code_shape h with ⟨q_x, q_y, q_H0, s0, ha, hb, ho⟩
  subst a
  subst b
  subst o
  constructor
  · exact sz_lt_p_left q_y q_H0
  ·
    cases s0 with
    | raw =>
      exact Nat.lt_trans (sz_lt_p_left q_x q_y) (sz_lt_p_right q_y (p q_x q_y))
    | hit h0 =>
      exact Nat.lt_trans (code_key_small h0) (sz_lt_p_left q_y q_H0)
theorem step_first_unique {a q b o : CM} (h : Step a b o) (k : Step q b o) : a = q := by
  cases h with
  | raw =>
    cases k with
    | raw => rfl
    | hit hc =>
      have hb := code_bounds hc
      have hp := sz_lt_p_right a b
      exact (Nat.not_lt_of_ge (Nat.le_of_lt hp) hb.2).elim
  | hit hc =>
    cases k with
    | raw =>
      have hb := code_bounds hc
      have hp := sz_lt_p_right q b
      exact (Nat.not_lt_of_ge (Nat.le_of_lt hp) hb.2).elim
    | hit hk => exact code_key_unique hc hk
theorem code_unique {a b o q : CM} (h : Code a b o) (k : Code a b q) : o = q := by
  rcases code_shape h with ⟨q_x, q_y, q_H0, hs0, ha, hb, ho⟩
  rcases code_shape k with ⟨r_q_x, r_q_y, r_q_H0, rs0, ka, kb, ko⟩
  have et := congrArg (fun z => (R z)) (hb.symm.trans kb)
  have eo := congrArg (fun z => (L z)) (hb.symm.trans kb)
  change q_H0 = r_q_H0 at et
  change q_y = r_q_y at eo
  rw [eo.symm, et.symm] at rs0
  have er := step_first_unique hs0 rs0
  have ex : q_x = r_q_x := er
  exact ho.trans (ex.trans ko.symm)

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
      change x = q_y at e1
      have e2 := congrArg (fun q => (R q)) hb
      change y = (p q_x q_y) at e2
      have cyc : q_y = (p q_x q_y) := Eq.trans (Eq.symm (Eq.trans (Eq.trans (Eq.symm (rfl)) (Eq.trans (e0) (rfl))) (rfl))) (Eq.trans (e2) (rfl))
      have hlt : sz q_y < sz (p q_x q_y) := sz_lt_p_right q_x q_y
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit h1 =>
      have hcB := code_bounds hc
      have h1B := code_bounds h1
      have p0 := congrArg (fun q => q) ha
      change y = q_y at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => (L q)) hb
      change x = q_y at p1
      have z1 := congrArg sz p1
      have p2 := congrArg (fun q => (R q)) hb
      change y = q_H0 at p2
      have z2 := congrArg sz p2
      have hx := h1B.2
      rw [Eq.trans (p2.symm) (Eq.trans (p0) (rfl))] at hx
      have selflt : sz q_y < sz q_y := hx
      exact (Nat.lt_irrefl _ selflt).elim
  | hit h0 =>
    cases qs0 with
    | raw =>
      have hcB := code_bounds hc
      have h0B := code_bounds h0
      have p0 := congrArg (fun q => q) ha
      change y = q_y at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => q) hb
      change H0 = (p q_y (p q_x q_y)) at p1
      have z1 := congrArg sz p1
      have hx : sz q_y < sz (p q_y (p q_x q_y)) := by
        have q := hcB.1
        have eu : sz y = sz q_y := congrArg sz (Eq.trans (p0) (rfl))
        have ev : sz H0 = sz (p q_y (p q_x q_y)) := congrArg sz (Eq.trans (p1) (rfl))
        have q1 : sz q_y < sz H0 := lt_of_eq_of_lt eu.symm q
        exact lt_of_lt_of_eq q1 ev
      have hy : sz (p q_y (p q_x q_y)) < sz q_y := by
        have q := h0B.2
        have ev : sz H0 = sz (p q_y (p q_x q_y)) := congrArg sz (Eq.trans (p1) (rfl))
        have eu : sz y = sz q_y := congrArg sz (Eq.trans (p0) (rfl))
        have q1 : sz (p q_y (p q_x q_y)) < sz y := lt_of_eq_of_lt ev.symm q
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
      change H0 = (p q_y q_H0) at p1
      have z1 := congrArg sz p1
      have hx : sz q_y < sz (p q_y q_H0) := by
        have q := hcB.1
        have eu : sz y = sz q_y := congrArg sz (Eq.trans (p0) (rfl))
        have ev : sz H0 = sz (p q_y q_H0) := congrArg sz (Eq.trans (p1) (rfl))
        have q1 : sz q_y < sz H0 := lt_of_eq_of_lt eu.symm q
        exact lt_of_lt_of_eq q1 ev
      have hy : sz (p q_y q_H0) < sz q_y := by
        have q := h0B.2
        have ev : sz H0 = sz (p q_y q_H0) := congrArg sz (Eq.trans (p1) (rfl))
        have eu : sz y = sz q_y := congrArg sz (Eq.trans (p0) (rfl))
        have q1 : sz (p q_y q_H0) < sz y := lt_of_eq_of_lt ev.symm q
        exact lt_of_lt_of_eq q1 eu
      exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
theorem source_holds (x y : CM) :
    x = (eval y (eval y (eval x y))) := by
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
  change x = (eval y (eval y H0))
  have rawEq : (eval y (eval y H0)) = (eval y (p y H0)) := congrArg (fun q => (eval y q)) (eval_raw (nr0 x y H0 s0))
  exact (eval_hit (Code.law x y H0 s0)).symm.trans rawEq.symm
noncomputable instance instMagma2 : Magma CM where op := eval
theorem nt0 : ¬ ∃ o, Code (CM.k CM.e) CM.e o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_y, q_H0, s0, ha, hb, ho⟩
  have bad := congrArg (fun q => q) hb
  change CM.e = (p q_y q_H0) at bad
  cases bad
theorem nt1 : ¬ ∃ o, Code CM.e CM.e o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_y, q_H0, s0, ha, hb, ho⟩
  have bad := congrArg (fun q => q) hb
  change CM.e = (p q_y q_H0) at bad
  cases bad
theorem nt2 : ¬ ∃ o, Code (CM.p CM.e CM.e) CM.e o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_y, q_H0, s0, ha, hb, ho⟩
  have bad := congrArg (fun q => q) hb
  change CM.e = (p q_y q_H0) at bad
  cases bad
theorem nt3 : ¬ ∃ o, Code CM.e (CM.p (CM.p CM.e CM.e) CM.e) o := by
  rintro ⟨o, hc⟩
  have hk := code_key hc
  change (CM.p CM.e CM.e) = CM.e at hk
  exact Bool.noConfusion (congrArg (fun q => match q with | e => true | k _ => false | p _ _ => false) hk)
theorem nt4 : ¬ ∃ o, Code (CM.k CM.e) (CM.p CM.e (CM.p (CM.p CM.e CM.e) CM.e)) o := by
  rintro ⟨o, hc⟩
  have hk := code_key hc
  change CM.e = (CM.k CM.e) at hk
  exact Bool.noConfusion (congrArg (fun q => match q with | e => false | k _ => true | p _ _ => false) hk)
end CM
end submission
open submission
open submission.CM
noncomputable def submission : Goal := by
  refine ⟨CM, CM.instMagma2, ?_, ?_⟩
  · intro x y
    exact CM.source_holds x y
  · intro target
    have bad := target (CM.k CM.e) CM.e CM.e
    have hl : (eval (CM.k CM.e) CM.e) = (CM.p (CM.k CM.e) CM.e) := (eval_raw nt0)
    have hr : (eval (CM.k CM.e) (eval CM.e (eval (eval CM.e CM.e) CM.e))) = (CM.p (CM.k CM.e) (CM.p CM.e (CM.p (CM.p CM.e CM.e) CM.e))) := by
      calc
        (eval (CM.k CM.e) (eval CM.e (eval (eval CM.e CM.e) CM.e))) = (eval (CM.k CM.e) (eval CM.e (eval (CM.p CM.e CM.e) CM.e))) := congrArg (fun q => (eval (CM.k CM.e) (eval CM.e (eval q CM.e)))) (eval_raw nt1)
        _ = (eval (CM.k CM.e) (eval CM.e (CM.p (CM.p CM.e CM.e) CM.e))) := congrArg (fun q => (eval (CM.k CM.e) (eval CM.e q))) (eval_raw nt2)
        _ = (eval (CM.k CM.e) (CM.p CM.e (CM.p (CM.p CM.e CM.e) CM.e))) := congrArg (fun q => (eval (CM.k CM.e) q)) (eval_raw nt3)
        _ = (CM.p (CM.k CM.e) (CM.p CM.e (CM.p (CM.p CM.e CM.e) CM.e))) := (eval_raw nt4)
    have bad2 := hl.symm.trans (bad.trans hr)
    exact Bool.noConfusion (congrArg (fun q => match (R q) with | e => false | k _ => false | p _ _ => true) bad2)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_73_to_42723 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_73_to_42723
