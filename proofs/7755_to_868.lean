-- Equation7755 → Equation868
-- Recorded verdict: false
-- Premise: x = y ◇ (y ◇ ((z ◇ (x ◇ x)) ◇ y))
-- Conclusion: x = x ◇ ((y ◇ z) ◇ (w ◇ u))
-- Original submission SHA-256: c1fe61ca7d03e65e323acacd85491e851629c266508312aaf793b701a15d8091
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (y ◇ ((z ◇ (x ◇ x)) ◇ y))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = x ◇ ((y ◇ z) ◇ (w ◇ u))
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
      (s0 : Step (p v1 (p x x)) v0 H0) :
      Code v0 (p v0 H0) x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_H0 : CM, Step (p q_v1 (p q_x q_x)) q_v0 q_H0 ∧ a = q_v0 ∧ b = (p q_v0 q_H0) ∧ o = q_x := by
  cases h
  exact ⟨_, _, _, _, by assumption, rfl, rfl, rfl⟩
def getKey (c : CM) : CM := (L c)
theorem code_key {a b o : CM} (h : Code a b o) : getKey b = a := by
  cases h <;> rfl
theorem code_key_unique {a q b o : CM} (h : Code a b o) (k : Code q b o) : a = q :=
  (code_key h).symm.trans (code_key k)
theorem code_key_small {a b o : CM} (h : Code a b o) : sz a < sz b := by
  rcases code_shape h with ⟨q_x, q_v0, q_v1, q_H0, s0, ha, hb, ho⟩
  subst a
  subst b
  exact sz_lt_p_left q_v0 q_H0
theorem code_bounds {a b o : CM} (h : Code a b o) :
    sz a < sz b ∧ sz o < sz b := by
  rcases code_shape h with ⟨q_x, q_v0, q_v1, q_H0, s0, ha, hb, ho⟩
  subst a
  subst b
  subst o
  constructor
  · exact sz_lt_p_left q_v0 q_H0
  ·
    cases s0 with
    | raw =>
      exact Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_x q_x) (sz_lt_p_right q_v1 (p q_x q_x))) (sz_lt_p_left (p q_v1 (p q_x q_x)) q_v0)) (sz_lt_p_right q_v0 (p (p q_v1 (p q_x q_x)) q_v0))
    | hit h0 =>
      exact Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_x q_x) (sz_lt_p_right q_v1 (p q_x q_x))) (code_key_small h0)) (sz_lt_p_left q_v0 q_H0)
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
  rcases code_shape h with ⟨q_x, q_v0, q_v1, q_H0, hs0, ha, hb, ho⟩
  rcases code_shape k with ⟨r_q_x, r_q_v0, r_q_v1, r_q_H0, rs0, ka, kb, ko⟩
  have et := congrArg (fun z => (R z)) (hb.symm.trans kb)
  have eo := congrArg (fun z => (L z)) (hb.symm.trans kb)
  change q_H0 = r_q_H0 at et
  change q_v0 = r_q_v0 at eo
  rw [eo.symm, et.symm] at rs0
  have er := step_first_unique hs0 rs0
  have ex : q_x = r_q_x := congrArg (fun z => (L (R z))) er
  exact ho.trans (ex.trans ko.symm)
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
    ¬ ∃ o, Code x x o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have qs0B := step_bound qs0
  cases qs0 with
  | raw =>
    have e0 := congrArg (fun q => q) ha
    change x = q_v0 at e0
    have e1 := congrArg (fun q => q) hb
    change x = (p q_v0 (p (p q_v1 (p q_x q_x)) q_v0)) at e1
    have cyc : q_v0 = (p q_v0 (p (p q_v1 (p q_x q_x)) q_v0)) := Eq.trans (Eq.symm (Eq.trans (Eq.trans (Eq.symm (rfl)) (Eq.trans (e0) (rfl))) (rfl))) (Eq.trans (e1) (rfl))
    have hlt : sz q_v0 < sz (p q_v0 (p (p q_v1 (p q_x q_x)) q_v0)) := sz_lt_p_left q_v0 (p (p q_v1 (p q_x q_x)) q_v0)
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have e0 := congrArg (fun q => q) ha
    change x = q_v0 at e0
    have e1 := congrArg (fun q => q) hb
    change x = (p q_v0 q_H0) at e1
    have cyc : q_v0 = (p q_v0 q_H0) := Eq.trans (Eq.symm (Eq.trans (Eq.trans (Eq.symm (rfl)) (Eq.trans (e0) (rfl))) (rfl))) (Eq.trans (e1) (rfl))
    have hlt : sz q_v0 < sz (p q_v0 q_H0) := sz_lt_p_left q_v0 q_H0
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr1 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code v1 (p x x) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have he : q_H0 = q_v0 := Eq.trans (rfl) (Eq.symm (Eq.trans (Eq.trans (Eq.symm (Eq.trans (Eq.trans (Eq.symm (rfl)) (Eq.trans (congrArg (fun q => (L q)) (hb)) (rfl))) (rfl))) (Eq.trans (congrArg (fun q => (R q)) (hb)) (rfl))) (rfl)))
  exact step_ne_second (by simpa only [he] using qs0)
theorem nr2 (x v0 v1 H0 : CM)
    (s0 : Step (p v1 (p x x)) v0 H0) :
    ¬ ∃ o, Code v0 H0 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have s0B := step_bound s0
  cases s0 with
  | raw =>
    have he : q_H0 = q_v0 := Eq.trans (Eq.trans (Eq.symm (Eq.trans (Eq.symm (Eq.trans (Eq.trans (Eq.symm (rfl)) (Eq.trans (ha) (rfl))) (Eq.trans (Eq.symm (Eq.trans (Eq.symm (rfl)) (Eq.trans (congrArg (fun q => (L q)) (hb)) (rfl)))) (rfl)))) (Eq.trans (congrArg (fun q => (R q)) (hb)) (rfl)))) (rfl)) (Eq.symm (Eq.trans (Eq.symm (Eq.trans (Eq.symm (rfl)) (Eq.trans (congrArg (fun q => (L q)) (hb)) (rfl)))) (rfl)))
    exact step_ne_second (by simpa only [he] using qs0)
  | hit s0h =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have hcB := code_bounds hc
      have s0hB := code_bounds s0h
      have s0B := s0B
      have qs0B := qs0B
      have p0 := ha
      change v0 = q_v0 at p0
      have z0 := congrArg sz p0
      have p1 := hb
      change H0 = (p q_v0 (p (p q_v1 (p q_x q_x)) q_v0)) at p1
      have z1 := congrArg sz p1
      have p2 := ho
      change o = q_x at p2
      have z2 := congrArg sz p2
      have hx : sz q_v0 < sz (p q_v0 (p (p q_v1 (p q_x q_x)) q_v0)) := by
        have q := hcB.1
        have eu : sz v0 = sz q_v0 := congrArg sz (Eq.trans (p0) (rfl))
        have ev : sz H0 = sz (p q_v0 (p (p q_v1 (p q_x q_x)) q_v0)) := congrArg sz (Eq.trans (p1) (rfl))
        have q1 : sz q_v0 < sz H0 := lt_of_eq_of_lt eu.symm q
        exact lt_of_lt_of_eq q1 ev
      have hy : sz (p q_v0 (p (p q_v1 (p q_x q_x)) q_v0)) < sz q_v0 := by
        have q := s0hB.2
        have ev : sz H0 = sz (p q_v0 (p (p q_v1 (p q_x q_x)) q_v0)) := congrArg sz (Eq.trans (p1) (rfl))
        have eu : sz v0 = sz q_v0 := congrArg sz (Eq.trans (p0) (rfl))
        have q1 : sz (p q_v0 (p (p q_v1 (p q_x q_x)) q_v0)) < sz v0 := lt_of_eq_of_lt ev.symm q
        exact lt_of_lt_of_eq q1 eu
      exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
    | hit qs0h =>
      have hcB := code_bounds hc
      have s0hB := code_bounds s0h
      have qs0hB := code_bounds qs0h
      have s0B := s0B
      have qs0B := qs0B
      have p0 := ha
      change v0 = q_v0 at p0
      have z0 := congrArg sz p0
      have p1 := hb
      change H0 = (p q_v0 q_H0) at p1
      have z1 := congrArg sz p1
      have p2 := ho
      change o = q_x at p2
      have z2 := congrArg sz p2
      have hx : sz q_v0 < sz (p q_v0 q_H0) := by
        have q := hcB.1
        have eu : sz v0 = sz q_v0 := congrArg sz (Eq.trans (p0) (rfl))
        have ev : sz H0 = sz (p q_v0 q_H0) := congrArg sz (Eq.trans (p1) (rfl))
        have q1 : sz q_v0 < sz H0 := lt_of_eq_of_lt eu.symm q
        exact lt_of_lt_of_eq q1 ev
      have hy : sz (p q_v0 q_H0) < sz q_v0 := by
        have q := s0hB.2
        have ev : sz H0 = sz (p q_v0 q_H0) := congrArg sz (Eq.trans (p1) (rfl))
        have eu : sz v0 = sz q_v0 := congrArg sz (Eq.trans (p0) (rfl))
        have q1 : sz (p q_v0 q_H0) < sz v0 := lt_of_eq_of_lt ev.symm q
        exact lt_of_lt_of_eq q1 eu
      exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
theorem source_holds (x v0 v1 : CM) :
    x = (eval v0 (eval v0 (eval (eval v1 (eval x x)) v0))) := by
  let H0 := eval (eval v1 (eval x x)) v0
  have e0a : (eval v1 (eval x x)) = (p v1 (p x x)) := by
    change (eval v1 (eval x x)) = (p v1 (p x x))
    calc
      (eval v1 (eval x x)) = (eval v1 (p x x)) := congrArg (fun q => (eval v1 q)) (eval_raw (nr0 x v0 v1))
      _ = (p v1 (p x x)) := (eval_raw (nr1 x v0 v1))
  have e0b : v0 = v0 := by
    change v0 = v0
    rfl
  have s0 : Step (p v1 (p x x)) v0 H0 := by
    rw [← e0a, ← e0b]
    exact eval_step (eval v1 (eval x x)) v0
  change x = (eval v0 (eval v0 H0))
  have rawEq : (eval v0 (eval v0 H0)) = (eval v0 (p v0 H0)) := congrArg (fun q => (eval v0 q)) (eval_raw (nr2 x v0 v1 H0 s0))
  exact (eval_hit (Code.law x v0 v1 H0 s0)).symm.trans rawEq.symm
noncomputable instance instMagma2 : Magma CM where op := eval
theorem nt0 : ¬ ∃ o, Code CM.e CM.e o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, s0, ha, hb, ho⟩
  have bad := congrArg (fun q => q) hb
  change CM.e = (p q_v0 q_H0) at bad
  cases bad
theorem nt1 : ¬ ∃ o, Code (CM.p CM.e CM.e) (CM.p CM.e CM.e) o := by
  rintro ⟨o, hc⟩
  have hk := code_key hc
  change CM.e = (CM.p CM.e CM.e) at hk
  exact Bool.noConfusion (congrArg (fun q => match q with | e => false | k _ => false | p _ _ => true) hk)
theorem nt2 : ¬ ∃ o, Code CM.e (CM.p (CM.p CM.e CM.e) (CM.p CM.e CM.e)) o := by
  rintro ⟨o, hc⟩
  have hk := code_key hc
  change (CM.p CM.e CM.e) = CM.e at hk
  exact Bool.noConfusion (congrArg (fun q => match q with | e => true | k _ => false | p _ _ => false) hk)
end CM
end submission
open submission
open submission.CM
noncomputable def submission : Goal := by
  refine ⟨CM, CM.instMagma2, ?_, ?_⟩
  · intro x v0 v1
    exact CM.source_holds x v0 v1
  · intro target
    have bad := target CM.e CM.e CM.e CM.e CM.e
    have hl : CM.e = CM.e := rfl
    have hr : (eval CM.e (eval (eval CM.e CM.e) (eval CM.e CM.e))) = (CM.p CM.e (CM.p (CM.p CM.e CM.e) (CM.p CM.e CM.e))) := by
      calc
        (eval CM.e (eval (eval CM.e CM.e) (eval CM.e CM.e))) = (eval CM.e (eval (CM.p CM.e CM.e) (eval CM.e CM.e))) := congrArg (fun q => (eval CM.e (eval q (eval CM.e CM.e)))) (eval_raw nt0)
        _ = (eval CM.e (eval (CM.p CM.e CM.e) (CM.p CM.e CM.e))) := congrArg (fun q => (eval CM.e (eval (CM.p CM.e CM.e) q))) (eval_raw nt0)
        _ = (eval CM.e (CM.p (CM.p CM.e CM.e) (CM.p CM.e CM.e))) := congrArg (fun q => (eval CM.e q)) (eval_raw nt1)
        _ = (CM.p CM.e (CM.p (CM.p CM.e CM.e) (CM.p CM.e CM.e))) := (eval_raw nt2)
    have bad2 := hl.symm.trans (bad.trans hr)
    exact Bool.noConfusion (congrArg (fun q => match q with | e => false | k _ => false | p _ _ => true) bad2)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_7755_to_868 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_7755_to_868
