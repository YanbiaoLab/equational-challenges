-- Equation3917 → Equation3456
-- Recorded verdict: false
-- Premise: x ◇ y = (x ◇ (x ◇ y)) ◇ x
-- Conclusion: x ◇ x = x ◇ ((x ◇ x) ◇ x)
-- Original submission SHA-256: 3da023a28cb37a74060a6a252313683ac11fb80a121eb1fcd5d3564d3177e234
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ y = (x ◇ (x ◇ y)) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G), x ◇ x = x ◇ ((x ◇ x) ◇ x)
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
  | r0 (v0 v1 v2 : CM) : Code (p v0 (p v1 v2)) v0 (p v1 v2)
  | r1 (v0 v1 v2 v3 : CM) : Code (p v0 v1) (p (p v2 v3) (p v0 v1)) (p v2 v3)
def CodeCases (a b o : CM) : Prop := (∃ v0 v1 v2 : CM, a = (p v0 (p v1 v2)) ∧ b = v0 ∧ o = (p v1 v2) ∧ sz a = sz (p v0 (p v1 v2)) ∧ sz b = sz v0 ∧ sz o = sz (p v1 v2)) ∨ (∃ v0 v1 v2 v3 : CM, a = (p v0 v1) ∧ b = (p (p v2 v3) (p v0 v1)) ∧ o = (p v2 v3) ∧ sz a = sz (p v0 v1) ∧ sz b = sz (p (p v2 v3) (p v0 v1)) ∧ sz o = sz (p v2 v3)) ∨ False
theorem code_cases {a b o : CM} (h : Code a b o) : CodeCases a b o := by
  cases h with
  | r0 => exact Or.inl ⟨_, _, _, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | r1 => exact Or.inr (Or.inl ⟨_, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl⟩)
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
  | r0 => exact ha.2.1
  | r1 => exact hb.1
theorem redex0_not_nf (v0 v1 v2 : CM) :
    ¬ NF (p (p v0 (p v1 v2)) v0) := by
  intro h
  exact h.2.2 ⟨(p v1 v2), Code.r0 v0 v1 v2⟩
theorem redex1_not_nf (v0 v1 v2 v3 : CM) :
    ¬ NF (p (p v0 v1) (p (p v2 v3) (p v0 v1))) := by
  intro h
  exact h.2.2 ⟨(p v2 v3), Code.r1 v0 v1 v2 v3⟩
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
@[grind unfold] abbrev C0 (v0 v1 v2 : CM) (a b o : CM) : Prop := a = (p v0 (p v1 v2)) ∧ b = v0 ∧ o = (p v1 v2) ∧ sz a = sz (p v0 (p v1 v2)) ∧ sz b = sz v0 ∧ sz o = sz (p v1 v2)
@[grind unfold] abbrev C1 (v0 v1 v2 v3 : CM) (a b o : CM) : Prop := a = (p v0 v1) ∧ b = (p (p v2 v3) (p v0 v1)) ∧ o = (p v2 v3) ∧ sz a = sz (p v0 v1) ∧ sz b = sz (p (p v2 v3) (p v0 v1)) ∧ sz o = sz (p v2 v3)
inductive EvalCases (a b o : CM) : Prop
  | r0 (v0 v1 v2 : CM) (h : C0 v0 v1 v2 a b o) : EvalCases a b o
  | r1 (v0 v1 v2 v3 : CM) (h : C1 v0 v1 v2 v3 a b o) : EvalCases a b o
  | raw (h : o = p a b ∧ sz o = sz a + sz b + 2) (n : ¬ ∃ q, Code a b q) : EvalCases a b o
theorem eval_cases (a b : CM) : EvalCases a b (eval a b) := by
  by_cases h : ∃ o, Code a b o
  · let o := Classical.choose h
    have hc : Code a b o := Classical.choose_spec h
    have cc := code_cases hc
    have hv : eval a b = o := by rw [eval, dif_pos h]
    rw [hv]
    unfold CodeCases at cc
    rcases cc with cc0 | cc1 | impossible
    · rcases cc0 with ⟨v0, v1, v2, hc0⟩
      exact .r0 v0 v1 v2 hc0
    · rcases cc1 with ⟨v0, v1, v2, v3, hc1⟩
      exact .r1 v0 v1 v2 v3 hc1
    · contradiction
  · exact .raw ⟨eval_raw h, eq_sz (eval_raw h)⟩ h

theorem source_raw (q0 q1 : CM)
    (hq0 : NF q0) (hq1 : NF q1) :
    (eval q0 q1) = (eval (eval q0 (eval q0 q1)) q0) := by
  classical
  generalize H0 : eval q0 q1 = T0
  generalize H1 : eval q0 T0 = T1
  generalize H2 : eval T1 q0 = T2
  change T0 = T2
  have B0 : EvalCases q0 q1 T0 := by
    rw [← H0]
    exact eval_cases q0 q1
  have B1 : EvalCases q0 T0 T1 := by
    rw [← H1]
    exact eval_cases q0 T0
  have B2 : EvalCases T1 q0 T2 := by
    rw [← H2]
    exact eval_cases T1 q0
  have N0 : NF T0 := by
    rw [← H0]
    exact eval_nf hq0 hq1
  have N1 : NF T1 := by
    rw [← H1]
    exact eval_nf hq0 N0
  have N2 : NF T2 := by
    rw [← H2]
    exact eval_nf N1 hq0
  all_goals rcases B2 with ⟨v2_0_0, v2_0_1, v2_0_2, hc2_0⟩ | ⟨v2_1_0, v2_1_1, v2_1_2, v2_1_3, hc2_1⟩ | ⟨hr2, n2⟩
  all_goals try (first | omega | contradiction | grind (config := { splits := 1, gen := 6 }) [nf_p_left, nf_p_right, nf_p_no, sz] | grind (config := { splits := 1, gen := 6 }) [Code.r0, Code.r1, sz] | grind (config := { splits := 1, gen := 6 }) [nf_p_left, nf_p_right, nf_p_no, redex0_not_nf, redex1_not_nf, sz])
  all_goals rcases B1 with ⟨v1_0_0, v1_0_1, v1_0_2, hc1_0⟩ | ⟨v1_1_0, v1_1_1, v1_1_2, v1_1_3, hc1_1⟩ | ⟨hr1, n1⟩
  all_goals try (first | omega | contradiction | grind (config := { splits := 1, gen := 6 }) [nf_p_left, nf_p_right, nf_p_no, sz] | grind (config := { splits := 1, gen := 6 }) [Code.r0, Code.r1, sz] | grind (config := { splits := 1, gen := 6 }) [nf_p_left, nf_p_right, nf_p_no, redex0_not_nf, redex1_not_nf, sz])
  all_goals rcases B0 with ⟨v0_0_0, v0_0_1, v0_0_2, hc0_0⟩ | ⟨v0_1_0, v0_1_1, v0_1_2, v0_1_3, hc0_1⟩ | ⟨hr0, n0⟩
  all_goals try (first | omega | contradiction | grind (config := { splits := 1, gen := 6 }) [nf_p_left, nf_p_right, nf_p_no, sz] | grind (config := { splits := 1, gen := 6 }) [Code.r0, Code.r1, sz] | grind (config := { splits := 1, gen := 6 }) [nf_p_left, nf_p_right, nf_p_no, redex0_not_nf, redex1_not_nf, sz])
  all_goals first | omega | contradiction | grind (config := { splits := 1, gen := 6 }) [nf_p_left, nf_p_right, nf_p_no, sz] | grind (config := { splits := 1, gen := 6 }) [Code.r0, Code.r1, sz] | grind (config := { splits := 1, gen := 6 }) [nf_p_left, nf_p_right, nf_p_no, redex0_not_nf, redex1_not_nf, sz]
def Carrier := {t : CM // NF t}
noncomputable def op (a b : Carrier) : Carrier := ⟨eval a.1 b.1, eval_nf a.2 b.2⟩
noncomputable instance instMagma : Magma Carrier where op := op
theorem source_holds (q0 q1 : Carrier) :
    (op q0 q1) = (op (op q0 (op q0 q1)) q0) := by
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
theorem t1 : ¬ ∃ o, Code (p e e) e o := by
  rintro ⟨o, h⟩
  have c := code_cases h
  unfold CodeCases at c
  grind (config := { splits := 12, gen := 12 }) [sz]
theorem e1 : eval (p e e) e = (p (p e e) e) := eval_raw t1
theorem t2 : ¬ ∃ o, Code e (p (p e e) e) o := by
  rintro ⟨o, h⟩
  have c := code_cases h
  unfold CodeCases at c
  grind (config := { splits := 12, gen := 12 }) [sz]
theorem e2 : eval e (p (p e e) e) = (p e (p (p e e) e)) := eval_raw t2
end CM
end submission
open submission
open submission.CM
noncomputable def submission : Goal := by
  refine ⟨CM.Carrier, CM.instMagma, CM.source_holds, ?_⟩
  intro target
  have bad := congrArg Subtype.val (target ce)
  change (eval e e) = (eval e (eval (eval e e) e)) at bad
  have hl : (eval e e) = (p e e) := e0
  have hr : (eval e (eval (eval e e) e)) = (p e (p (p e e) e)) := ((congrArg (fun q => (eval e (eval q e))) e0).trans (congrArg (fun q => (eval e q)) e1)).trans (e2)
  have bad := hl.symm.trans (bad.trans hr)
  exact Bool.noConfusion (congrArg (fun q => match (R q) with | e => false | k _ => false | p _ _ => true) bad)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_3917_to_3456 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_3917_to_3456
