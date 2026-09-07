-- Equation10211 → Equation36662
-- Recorded verdict: false
-- Premise: x = y ◇ ((x ◇ y) ◇ ((y ◇ y) ◇ y))
-- Conclusion: x = (((y ◇ y) ◇ y) ◇ (x ◇ y)) ◇ y
-- Original submission SHA-256: 11359ac16262440cfd89c42a21b3684a234f2a1b055d623f8bb0cc51772f34ae
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = y ◇ ((x ◇ y) ◇ ((y ◇ y) ◇ y))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (((y ◇ y) ◇ y) ◇ (x ◇ y)) ◇ y
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
      Code y (p H0 (p (p y y) y)) x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_y q_H0 : CM, Step q_x q_y q_H0 ∧ a = q_y ∧ b = (p q_H0 (p (p q_y q_y) q_y)) ∧ o = q_x := by
  cases h with
  | law x y H0 s0 =>
    exact ⟨_, _, _, by assumption, rfl, rfl, rfl⟩
def getKey (c : CM) : CM := (L (L (R c)))
theorem code_key {a b o : CM} (h : Code a b o) : getKey b = a := by
  cases h <;> rfl
theorem code_key_unique {a q b o : CM} (h : Code a b o) (k : Code q b o) : a = q :=
  (code_key h).symm.trans (code_key k)
theorem code_key_small {a b o : CM} (h : Code a b o) : sz a < sz b := by
  rcases code_shape h with ⟨q_x, q_y, q_H0, s0, ha, hb, ho⟩
  subst a
  subst b
  exact Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_y q_y) (sz_lt_p_left (p q_y q_y) q_y)) (sz_lt_p_right q_H0 (p (p q_y q_y) q_y))
theorem code_bounds {a b o : CM} (h : Code a b o) :
    sz a < sz b ∧ sz o < sz b := by
  rcases code_shape h with ⟨q_x, q_y, q_H0, s0, ha, hb, ho⟩
  subst a
  subst b
  subst o
  constructor
  · exact Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_y q_y) (sz_lt_p_left (p q_y q_y) q_y)) (sz_lt_p_right q_H0 (p (p q_y q_y) q_y))
  ·
    cases s0 with
    | raw =>
      exact Nat.lt_trans (sz_lt_p_left q_x q_y) (sz_lt_p_left (p q_x q_y) (p (p q_y q_y) q_y))
    | hit h0 =>
      exact Nat.lt_trans (code_key_small h0) (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_y q_y) (sz_lt_p_left (p q_y q_y) q_y)) (sz_lt_p_right q_H0 (p (p q_y q_y) q_y)))
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
  have et := congrArg (fun z => (L z)) (hb.symm.trans kb)
  have eo := congrArg (fun z => (L (L (R z)))) (hb.symm.trans kb)
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
theorem nr0 (x y : CM)
 :
    ¬ ∃ o, Code y y o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_y, q_H0, qs0, ha, hb, ho⟩
  cases qs0 with
  | raw =>
    have e0 := congrArg (fun q => q) ha
    change y = q_y at e0
    have e1 := congrArg (fun q => q) hb
    change y = (p (p q_x q_y) (p (p q_y q_y) q_y)) at e1
    have cyc : q_y = (p (p q_x q_y) (p (p q_y q_y) q_y)) := Eq.trans (Eq.symm (Eq.trans (Eq.trans (Eq.symm (rfl)) (Eq.trans (e0) (rfl))) (rfl))) (Eq.trans (e1) (rfl))
    have hlt : sz q_y < sz (p (p q_x q_y) (p (p q_y q_y) q_y)) := Nat.lt_trans (sz_lt_p_right q_x q_y) (sz_lt_p_left (p q_x q_y) (p (p q_y q_y) q_y))
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit h0 =>
    have e0 := congrArg (fun q => q) ha
    change y = q_y at e0
    have e1 := congrArg (fun q => q) hb
    change y = (p q_H0 (p (p q_y q_y) q_y)) at e1
    have cyc : q_y = (p q_H0 (p (p q_y q_y) q_y)) := Eq.trans (Eq.symm (Eq.trans (Eq.trans (Eq.symm (rfl)) (Eq.trans (e0) (rfl))) (rfl))) (Eq.trans (e1) (rfl))
    have hlt : sz q_y < sz (p q_H0 (p (p q_y q_y) q_y)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_y q_y) (sz_lt_p_left (p q_y q_y) q_y)) (sz_lt_p_right q_H0 (p (p q_y q_y) q_y))
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr1 (x y : CM)
 :
    ¬ ∃ o, Code (p y y) y o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_y, q_H0, qs0, ha, hb, ho⟩
  cases qs0 with
  | raw =>
    have e0 := congrArg (fun q => q) ha
    change (p y y) = q_y at e0
    have e1 := congrArg (fun q => q) hb
    change y = (p (p q_x q_y) (p (p q_y q_y) q_y)) at e1
    have cyc : y = (p (p q_x (p y y)) (p (p (p y y) (p y y)) (p y y))) := Eq.trans (Eq.symm (rfl)) (Eq.trans (e1) (Eq.trans (congrArg (fun z => p z (p (p q_y q_y) q_y)) (congrArg (fun z => p q_x z) (Eq.trans (Eq.symm (Eq.trans (Eq.symm (rfl)) (Eq.trans (e0) (rfl)))) (rfl)))) (congrArg (fun z => p (p q_x (p y y)) z) (Eq.trans (congrArg (fun z => p z q_y) (Eq.trans (congrArg (fun z => p z q_y) (Eq.trans (Eq.symm (Eq.trans (Eq.symm (rfl)) (Eq.trans (e0) (rfl)))) (rfl))) (congrArg (fun z => p (p y y) z) (Eq.trans (Eq.symm (Eq.trans (Eq.symm (rfl)) (Eq.trans (e0) (rfl)))) (rfl))))) (congrArg (fun z => p (p (p y y) (p y y)) z) (Eq.trans (Eq.symm (Eq.trans (Eq.symm (rfl)) (Eq.trans (e0) (rfl)))) (rfl)))))))
    have hlt : sz y < sz (p (p q_x (p y y)) (p (p (p y y) (p y y)) (p y y))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left y y) (sz_lt_p_right q_x (p y y))) (sz_lt_p_left (p q_x (p y y)) (p (p (p y y) (p y y)) (p y y)))
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit h0 =>
    have e0 := congrArg (fun q => q) ha
    change (p y y) = q_y at e0
    have e1 := congrArg (fun q => q) hb
    change y = (p q_H0 (p (p q_y q_y) q_y)) at e1
    have cyc : y = (p q_H0 (p (p (p y y) (p y y)) (p y y))) := Eq.trans (Eq.symm (rfl)) (Eq.trans (e1) (congrArg (fun z => p q_H0 z) (Eq.trans (congrArg (fun z => p z q_y) (Eq.trans (congrArg (fun z => p z q_y) (Eq.trans (Eq.symm (Eq.trans (Eq.symm (rfl)) (Eq.trans (e0) (rfl)))) (rfl))) (congrArg (fun z => p (p y y) z) (Eq.trans (Eq.symm (Eq.trans (Eq.symm (rfl)) (Eq.trans (e0) (rfl)))) (rfl))))) (congrArg (fun z => p (p (p y y) (p y y)) z) (Eq.trans (Eq.symm (Eq.trans (Eq.symm (rfl)) (Eq.trans (e0) (rfl)))) (rfl))))))
    have hlt : sz y < sz (p q_H0 (p (p (p y y) (p y y)) (p y y))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left y y) (sz_lt_p_left (p y y) (p y y))) (sz_lt_p_left (p (p y y) (p y y)) (p y y))) (sz_lt_p_right q_H0 (p (p (p y y) (p y y)) (p y y)))
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr2 (x y H0 : CM)
    (s0 : Step x y H0) :
    ¬ ∃ o, Code H0 (p (p y y) y) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_y, q_H0, qs0, ha, hb, ho⟩
  cases s0 with
  | raw =>
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change (p x y) = q_y at e0
      have e1 := congrArg (fun q => (L (L q))) hb
      change y = q_x at e1
      have e2 := congrArg (fun q => (R (L q))) hb
      change y = q_y at e2
      have e3 := congrArg (fun q => (R q)) hb
      change y = (p (p q_y q_y) q_y) at e3
      have cyc : q_x = (p x q_x) := Eq.trans (Eq.symm (Eq.trans (Eq.trans (Eq.symm (rfl)) (Eq.trans (e1) (rfl))) (rfl))) (Eq.trans (e2) (Eq.trans (Eq.symm (Eq.trans (Eq.symm (rfl)) (Eq.trans (e0) (rfl)))) (congrArg (fun z => p x z) (Eq.trans (Eq.trans (Eq.symm (rfl)) (Eq.trans (e1) (rfl))) (rfl)))))
      have hlt : sz q_x < sz (p x q_x) := sz_lt_p_right x q_x
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit h1 =>
      have e0 := congrArg (fun q => q) ha
      change (p x y) = q_y at e0
      have e1 := congrArg (fun q => (L q)) hb
      change (p y y) = q_H0 at e1
      have e2 := congrArg (fun q => (R q)) hb
      change y = (p (p q_y q_y) q_y) at e2
      have cyc : y = (p (p (p x y) (p x y)) (p x y)) := Eq.trans (Eq.symm (rfl)) (Eq.trans (e2) (Eq.trans (congrArg (fun z => p z q_y) (Eq.trans (congrArg (fun z => p z q_y) (Eq.trans (Eq.symm (Eq.trans (Eq.symm (rfl)) (Eq.trans (e0) (rfl)))) (rfl))) (congrArg (fun z => p (p x y) z) (Eq.trans (Eq.symm (Eq.trans (Eq.symm (rfl)) (Eq.trans (e0) (rfl)))) (rfl))))) (congrArg (fun z => p (p (p x y) (p x y)) z) (Eq.trans (Eq.symm (Eq.trans (Eq.symm (rfl)) (Eq.trans (e0) (rfl)))) (rfl)))))
      have hlt : sz y < sz (p (p (p x y) (p x y)) (p x y)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right x y) (sz_lt_p_left (p x y) (p x y))) (sz_lt_p_left (p (p x y) (p x y)) (p x y))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit h0 =>
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change H0 = q_y at e0
      have e1 := congrArg (fun q => (L (L q))) hb
      change y = q_x at e1
      have e2 := congrArg (fun q => (R (L q))) hb
      change y = q_y at e2
      have e3 := congrArg (fun q => (R q)) hb
      change y = (p (p q_y q_y) q_y) at e3
      have cyc : q_y = (p (p q_y q_y) q_y) := Eq.trans (Eq.symm (Eq.trans (Eq.trans (Eq.symm (rfl)) (Eq.trans (e1) (rfl))) (Eq.trans (Eq.trans (Eq.symm (Eq.trans (Eq.trans (Eq.symm (rfl)) (Eq.trans (e1) (rfl))) (rfl))) (Eq.trans (e2) (rfl))) (rfl)))) (Eq.trans (e3) (rfl))
      have hlt : sz q_y < sz (p (p q_y q_y) q_y) := Nat.lt_trans (sz_lt_p_left q_y q_y) (sz_lt_p_left (p q_y q_y) q_y)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit h1 =>
      have hcB := code_bounds hc
      have h0B := code_bounds h0
      have h1B := code_bounds h1
      have p0 := congrArg (fun q => q) ha
      change H0 = q_y at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => (L q)) hb
      change (p y y) = q_H0 at p1
      have z1 := congrArg sz p1
      have p2 := congrArg (fun q => (R q)) hb
      change y = (p (p q_y q_y) q_y) at p2
      have z2 := congrArg sz p2
      have badlt : sz q_y < sz q_H0 := by
        rw [Eq.trans (p1.symm) (Eq.trans (congrArg (fun z => p z y) (Eq.trans (p2) (rfl))) (congrArg (fun z => p (p (p q_y q_y) q_y) z) (Eq.trans (p2) (rfl))))]
        exact Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_y q_y) (sz_lt_p_left (p q_y q_y) q_y)) (sz_lt_p_left (p (p q_y q_y) q_y) (p (p q_y q_y) q_y))
      exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) h1B.2).elim
theorem source_holds (x y : CM) :
    x = (eval y (eval (eval x y) (eval (eval y y) y))) := by
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
  change x = (eval y (eval H0 (eval (eval y y) y)))
  have rawEq : (eval y (eval H0 (eval (eval y y) y))) = (eval y (p H0 (p (p y y) y))) := by
    calc
      (eval y (eval H0 (eval (eval y y) y))) = (eval y (eval H0 (eval (p y y) y))) := congrArg (fun q => (eval y (eval H0 (eval q y)))) (eval_raw (nr0 x y))
      _ = (eval y (eval H0 (p (p y y) y))) := congrArg (fun q => (eval y (eval H0 q))) (eval_raw (nr1 x y))
      _ = (eval y (p H0 (p (p y y) y))) := congrArg (fun q => (eval y q)) (eval_raw (nr2 x y H0 s0))
  exact (eval_hit (Code.law x y H0 s0)).symm.trans rawEq.symm
noncomputable instance instMagma2 : Magma CM where op := eval
theorem nt0 : ¬ ∃ o, Code CM.e CM.e o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_y, q_H0, s0, ha, hb, ho⟩
  have bad := congrArg (fun q => (L (R q))) hb
  change CM.e = (p q_y q_y) at bad
  cases bad
theorem nt1 : ¬ ∃ o, Code (CM.p CM.e CM.e) CM.e o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_y, q_H0, s0, ha, hb, ho⟩
  have bad := congrArg (fun q => (L (R q))) hb
  change CM.e = (p q_y q_y) at bad
  cases bad
theorem nt2 : ¬ ∃ o, Code (CM.p (CM.p CM.e CM.e) CM.e) (CM.p CM.e CM.e) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_y, q_H0, s0, ha, hb, ho⟩
  have bad := congrArg (fun q => (L (R q))) hb
  change CM.e = (p q_y q_y) at bad
  cases bad
theorem nt3 : ¬ ∃ o, Code (CM.p (CM.p (CM.p CM.e CM.e) CM.e) (CM.p CM.e CM.e)) CM.e o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_y, q_H0, s0, ha, hb, ho⟩
  have bad := congrArg (fun q => (L (R q))) hb
  change CM.e = (p q_y q_y) at bad
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
    have bad := target CM.e CM.e
    have hl : CM.e = CM.e := rfl
    have hr : (eval (eval (eval (eval CM.e CM.e) CM.e) (eval CM.e CM.e)) CM.e) = (CM.p (CM.p (CM.p (CM.p CM.e CM.e) CM.e) (CM.p CM.e CM.e)) CM.e) := by
      calc
        (eval (eval (eval (eval CM.e CM.e) CM.e) (eval CM.e CM.e)) CM.e) = (eval (eval (eval (CM.p CM.e CM.e) CM.e) (eval CM.e CM.e)) CM.e) := congrArg (fun q => (eval (eval (eval q CM.e) (eval CM.e CM.e)) CM.e)) (eval_raw nt0)
        _ = (eval (eval (eval (CM.p CM.e CM.e) CM.e) (CM.p CM.e CM.e)) CM.e) := congrArg (fun q => (eval (eval (eval (CM.p CM.e CM.e) CM.e) q) CM.e)) (eval_raw nt0)
        _ = (eval (eval (CM.p (CM.p CM.e CM.e) CM.e) (CM.p CM.e CM.e)) CM.e) := congrArg (fun q => (eval (eval q (CM.p CM.e CM.e)) CM.e)) (eval_raw nt1)
        _ = (eval (CM.p (CM.p (CM.p CM.e CM.e) CM.e) (CM.p CM.e CM.e)) CM.e) := congrArg (fun q => (eval q CM.e)) (eval_raw nt2)
        _ = (CM.p (CM.p (CM.p (CM.p CM.e CM.e) CM.e) (CM.p CM.e CM.e)) CM.e) := (eval_raw nt3)
    have bad2 := hl.symm.trans (bad.trans hr)
    exact Bool.noConfusion (congrArg (fun q => match q with | e => false | k _ => false | p _ _ => true) bad2)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_10211_to_36662 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_10211_to_36662
