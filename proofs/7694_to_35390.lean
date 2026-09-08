-- Equation7694 → Equation35390
-- Recorded verdict: false
-- Premise: x = y ◇ (y ◇ ((x ◇ (y ◇ y)) ◇ y))
-- Conclusion: x = ((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ x
-- Original submission SHA-256: ba64bdb80378e31936607570f84134498d00ef98196cb855c211ac3f2a966026
-- Generator: equational-challenges standalone v1
-- All project definitions are embedded in this file.

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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = y ◇ (y ◇ ((x ◇ (y ◇ y)) ◇ y))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G), x = ((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ x
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Original submission body
                   
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace submission
inductive CM where | e : CM | k : CM → CM | p : CM → CM → CM
namespace CM
def L : CM → CM | .p a _ => a | _ => .e
def R : CM → CM | .p _ b => b | _ => .e
def U : CM → CM | .k a => a | _ => .e
def sz : CM → Nat | .e => 0 | .k a => sz a + 1 | .p a b => sz a + sz b + 2
inductive Code : CM → CM → CM → Prop
  | r0 (q1 q0 : CM) : Code q1 (p q1 (p (p q0 (p q1 q1)) q1)) q0
def CodeCases (a b o : CM) : Prop := (∃ q1 q0 : CM, a = q1 ∧ b = (p q1 (p (p q0 (p q1 q1)) q1)) ∧ o = q0 ∧ sz a = sz q1 ∧ sz b = sz (p q1 (p (p q0 (p q1 q1)) q1)) ∧ sz o = sz q0) ∨ False
theorem code_cases {a b o : CM} (h : Code a b o) : CodeCases a b o := by
  cases h with
  | r0 => exact Or.inl ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl⟩
def NF : CM → Prop
  | .e => True
  | .k a => NF a
  | .p a b => NF a ∧ NF b ∧ ¬ ∃ o, Code a b o
@[grind →] theorem nf_p_left {a b : CM} (h : NF (p a b)) : NF a := h.1
@[grind →] theorem nf_p_right {a b : CM} (h : NF (p a b)) : NF b := h.2.1
@[grind →] theorem nf_p_no {a b : CM} (h : NF (p a b)) : ¬ ∃ o, Code a b o := h.2.2
theorem eq_sz {a b : CM} (h : a = b) : sz a = sz b := congrArg sz h
theorem ne_p_left (a b : CM) : a ≠ p a b := by
  intro h
  have q := congrArg sz h
  simp [sz] at q <;> omega
theorem ne_p_right (a b : CM) : b ≠ p a b := by
  intro h
  have q := congrArg sz h
  simp [sz] at q <;> omega
theorem code_nf {a b o : CM} (ha : NF a) (hb : NF b) (h : Code a b o) : NF o := by
  cases h with
  | r0 => exact hb.2.1.1.1
theorem redex0_not_nf (q1 q0 : CM) :
    ¬ NF (p q1 (p q1 (p (p q0 (p q1 q1)) q1))) := by
  intro h
  exact h.2.2 ⟨q0, Code.r0 q1 q0⟩
noncomputable def eval (a b : CM) : CM := by
  classical
  exact if h : ∃ o, Code a b o then Classical.choose h else p a b
theorem eval_raw {a b : CM} (h : ¬ ∃ o, Code a b o) : eval a b = p a b := by simp [eval, h]
theorem eval_nf {a b : CM} (ha : NF a) (hb : NF b) : NF (eval a b) := by
  by_cases h : ∃ o, Code a b o
  · rw [eval, dif_pos h]
    exact code_nf ha hb (Classical.choose_spec h)
  · rw [eval_raw h]
    exact ⟨ha, hb, h⟩
@[grind unfold] abbrev C0 (q1 q0 : CM) (a b o : CM) : Prop := a = q1 ∧ b = (p q1 (p (p q0 (p q1 q1)) q1)) ∧ o = q0 ∧ sz a = sz q1 ∧ sz b = sz (p q1 (p (p q0 (p q1 q1)) q1)) ∧ sz o = sz q0
inductive EvalCases (a b o : CM) : Prop
  | r0 (q1 q0 : CM) (h : C0 q1 q0 a b o) : EvalCases a b o
  | raw (h : o = p a b ∧ sz o = sz a + sz b + 2) (n : ¬ ∃ q, Code a b q) : EvalCases a b o
theorem eval_cases (a b : CM) : EvalCases a b (eval a b) := by
  by_cases h : ∃ o, Code a b o
  · let o := Classical.choose h
    have hc : Code a b o := Classical.choose_spec h
    have cc := code_cases hc
    have hv : eval a b = o := by rw [eval, dif_pos h]
    rw [hv]
    unfold CodeCases at cc
    rcases cc with cc0 | impossible
    · rcases cc0 with ⟨q1, q0, hc0⟩
      exact .r0 q1 q0 hc0
    · contradiction
  · exact .raw ⟨eval_raw h, eq_sz (eval_raw h)⟩ h

theorem source_raw (q0 q1 : CM)
    (hq0 : NF q0) (hq1 : NF q1) :
    q0 = (eval q1 (eval q1 (eval (eval q0 (eval q1 q1)) q1))) := by
  classical
  generalize H0 : eval q1 q1 = T0
  generalize H1 : eval q0 T0 = T1
  generalize H2 : eval T1 q1 = T2
  generalize H3 : eval q1 T2 = T3
  generalize H4 : eval q1 T3 = T4
  change q0 = T4
  have B0 : EvalCases q1 q1 T0 := by
    rw [← H0]
    exact eval_cases q1 q1
  have B1 : EvalCases q0 T0 T1 := by
    rw [← H1]
    exact eval_cases q0 T0
  have B2 : EvalCases T1 q1 T2 := by
    rw [← H2]
    exact eval_cases T1 q1
  have B3 : EvalCases q1 T2 T3 := by
    rw [← H3]
    exact eval_cases q1 T2
  have B4 : EvalCases q1 T3 T4 := by
    rw [← H4]
    exact eval_cases q1 T3
  have N0 : NF T0 := by
    rw [← H0]
    exact eval_nf hq1 hq1
  have N1 : NF T1 := by
    rw [← H1]
    exact eval_nf hq0 N0
  have N2 : NF T2 := by
    rw [← H2]
    exact eval_nf N1 hq1
  have N3 : NF T3 := by
    rw [← H3]
    exact eval_nf hq1 N2
  have N4 : NF T4 := by
    rw [← H4]
    exact eval_nf hq1 N3
  all_goals rcases B0 with ⟨v0_0_0, v0_0_1, hc0_0⟩ | ⟨hr0, n0⟩
  all_goals try (first | omega | contradiction | grind (config := { splits := 1, gen := 6 }) [nf_p_left, nf_p_right, nf_p_no, sz] | grind (config := { splits := 1, gen := 6 }) [Code.r0, sz] | grind (config := { splits := 1, gen := 6 }) [nf_p_left, nf_p_right, nf_p_no, redex0_not_nf, sz])
  all_goals rcases B1 with ⟨v1_0_0, v1_0_1, hc1_0⟩ | ⟨hr1, n1⟩
  all_goals try (first | omega | contradiction | grind (config := { splits := 1, gen := 6 }) [nf_p_left, nf_p_right, nf_p_no, sz] | grind (config := { splits := 1, gen := 6 }) [Code.r0, sz] | grind (config := { splits := 1, gen := 6 }) [nf_p_left, nf_p_right, nf_p_no, redex0_not_nf, sz])
  all_goals rcases B2 with ⟨v2_0_0, v2_0_1, hc2_0⟩ | ⟨hr2, n2⟩
  all_goals try (first | omega | contradiction | grind (config := { splits := 1, gen := 6 }) [nf_p_left, nf_p_right, nf_p_no, sz] | grind (config := { splits := 1, gen := 6 }) [Code.r0, sz] | grind (config := { splits := 1, gen := 6 }) [nf_p_left, nf_p_right, nf_p_no, redex0_not_nf, sz])
  all_goals rcases B3 with ⟨v3_0_0, v3_0_1, hc3_0⟩ | ⟨hr3, n3⟩
  all_goals try (first | omega | contradiction | grind (config := { splits := 1, gen := 6 }) [nf_p_left, nf_p_right, nf_p_no, sz] | grind (config := { splits := 1, gen := 6 }) [Code.r0, sz] | grind (config := { splits := 1, gen := 6 }) [nf_p_left, nf_p_right, nf_p_no, redex0_not_nf, sz])
  all_goals rcases B4 with ⟨v4_0_0, v4_0_1, hc4_0⟩ | ⟨hr4, n4⟩
  all_goals try (first | omega | contradiction | grind (config := { splits := 1, gen := 6 }) [nf_p_left, nf_p_right, nf_p_no, sz] | grind (config := { splits := 1, gen := 6 }) [Code.r0, sz] | grind (config := { splits := 1, gen := 6 }) [nf_p_left, nf_p_right, nf_p_no, redex0_not_nf, sz])
  all_goals first | omega | contradiction | grind (config := { splits := 1, gen := 6 }) [nf_p_left, nf_p_right, nf_p_no, sz] | grind (config := { splits := 1, gen := 6 }) [Code.r0, sz] | grind (config := { splits := 1, gen := 6 }) [nf_p_left, nf_p_right, nf_p_no, redex0_not_nf, sz]
def Carrier := {t : CM // NF t}
noncomputable def op (a b : Carrier) : Carrier := ⟨eval a.1 b.1, eval_nf a.2 b.2⟩
noncomputable instance instMagma : Magma Carrier where op := op
theorem source_holds (q0 q1 : Carrier) :
    q0 = (op q1 (op q1 (op (op q0 (op q1 q1)) q1))) := by
  apply Subtype.ext
  exact source_raw q0.1 q1.1 q0.2 q1.2
def ce : Carrier := ⟨e, by trivial⟩
def ck (a : Carrier) : Carrier := ⟨k a.1, a.2⟩
def tower : Nat → Carrier | 0 => ce | n+1 => ck (tower n)
theorem tower_sz (n : Nat) : sz (tower n).1 = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [tower, ck, sz, ih]
theorem tower_injective : Function.Injective tower := by
  intro a b h
  have q := congrArg (fun x : Carrier => sz x.1) h
  simpa only [tower_sz] using q
theorem t0 : ¬ ∃ o, Code e e o := by
  rintro ⟨o, h⟩
  have c := code_cases h
  unfold CodeCases at c
  grind (config := { splits := 12, gen := 12 }) [sz]
theorem e0 : eval e e = (p e e) := eval_raw t0
theorem t1 : ¬ ∃ o, Code e (p e e) o := by
  rintro ⟨o, h⟩
  have c := code_cases h
  unfold CodeCases at c
  grind (config := { splits := 12, gen := 12 }) [sz]
theorem e1 : eval e (p e e) = (p e (p e e)) := eval_raw t1
theorem t2 : ¬ ∃ o, Code (p e (p e e)) (p e e) o := by
  rintro ⟨o, h⟩
  have c := code_cases h
  unfold CodeCases at c
  grind (config := { splits := 12, gen := 12 }) [sz]
theorem e2 : eval (p e (p e e)) (p e e) = (p (p e (p e e)) (p e e)) := eval_raw t2
theorem t3 : ¬ ∃ o, Code (p (p e (p e e)) (p e e)) e o := by
  rintro ⟨o, h⟩
  have c := code_cases h
  unfold CodeCases at c
  grind (config := { splits := 12, gen := 12 }) [sz]
theorem e3 : eval (p (p e (p e e)) (p e e)) e = (p (p (p e (p e e)) (p e e)) e) := eval_raw t3
end CM
end submission
open submission
open submission.CM
noncomputable def submission : Goal := by
  refine ⟨CM.Carrier, CM.instMagma, CM.source_holds, ?_⟩
  intro target
  have bad := congrArg Subtype.val (target ce)
  change e = (eval (eval (eval e (eval e e)) (eval e e)) e) at bad
  have hl : e = e := rfl
  have hr : (eval (eval (eval e (eval e e)) (eval e e)) e) = (p (p (p e (p e e)) (p e e)) e) := ((((congrArg (fun q => (eval (eval (eval e q) (eval e e)) e)) e0).trans (congrArg (fun q => (eval (eval q (eval e e)) e)) e1)).trans (congrArg (fun q => (eval (eval (p e (p e e)) q) e)) e0)).trans (congrArg (fun q => (eval q e)) e2)).trans (e3)
  have bad := hl.symm.trans (bad.trans hr)
  exact Bool.noConfusion (congrArg (fun q => match q with | e => false | k _ => false | p _ _ => true) bad)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_7694_to_35390 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_7694_to_35390
