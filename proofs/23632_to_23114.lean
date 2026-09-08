-- Equation23632 → Equation23114
-- Recorded verdict: false
-- Premise: x = ((y ◇ z) ◇ x) ◇ (x ◇ (w ◇ w))
-- Conclusion: x = ((x ◇ x) ◇ x) ◇ (x ◇ (y ◇ x))
-- Original submission SHA-256: b912661f46a5ebe1a5cb4f5a968584d55869c23e32fc5560610b8e0ff8b8ed2a
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ z) ◇ x) ◇ (x ◇ (w ◇ w))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = ((x ◇ x) ◇ x) ◇ (x ◇ (y ◇ x))
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Original submission body
                   
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
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
inductive Code : CM → CM → CM → Prop
  | r0 (v00 v01 v02 : CM) : Code (p (p v00 v00) v01) (p v01 v02) v01
  | r1 (v10 v11 v12 : CM) : Code (p v10 v10) (p (p (p v10 v10) v11) v12) (p (p v10 v10) v11)
  | r2 (v20 v21 v22 v23 : CM) : Code (p (p v20 v20) v21) (p (p (p (p v20 v20) v21) v22) v23) (p (p (p v20 v20) v21) v22)
  | r3 (v30 v31 v32 : CM) : Code (p (p v30 v30) (p (p v31 v31) v32)) v32 (p (p v31 v31) v32)
def CodeCases (a b o : CM) : Prop := (∃ v00 v01 v02, a = (p (p v00 v00) v01) ∧ b = (p v01 v02) ∧ o = v01 ∧ sz a = ((((sz v00 + 1) + (sz v00 + 1)) + 1) + (sz v01 + 1)) ∧ sz b = ((sz v01 + 1) + (sz v02 + 1)) ∧ sz o = sz v01) ∨ (∃ v10 v11 v12, a = (p v10 v10) ∧ b = (p (p (p v10 v10) v11) v12) ∧ o = (p (p v10 v10) v11) ∧ sz a = ((sz v10 + 1) + (sz v10 + 1)) ∧ sz b = ((((((sz v10 + 1) + (sz v10 + 1)) + 1) + (sz v11 + 1)) + 1) + (sz v12 + 1)) ∧ sz o = ((((sz v10 + 1) + (sz v10 + 1)) + 1) + (sz v11 + 1))) ∨ (∃ v20 v21 v22 v23, a = (p (p v20 v20) v21) ∧ b = (p (p (p (p v20 v20) v21) v22) v23) ∧ o = (p (p (p v20 v20) v21) v22) ∧ sz a = ((((sz v20 + 1) + (sz v20 + 1)) + 1) + (sz v21 + 1)) ∧ sz b = ((((((((sz v20 + 1) + (sz v20 + 1)) + 1) + (sz v21 + 1)) + 1) + (sz v22 + 1)) + 1) + (sz v23 + 1)) ∧ sz o = ((((((sz v20 + 1) + (sz v20 + 1)) + 1) + (sz v21 + 1)) + 1) + (sz v22 + 1))) ∨ (∃ v30 v31 v32, a = (p (p v30 v30) (p (p v31 v31) v32)) ∧ b = v32 ∧ o = (p (p v31 v31) v32) ∧ sz a = ((((sz v30 + 1) + (sz v30 + 1)) + 1) + (((((sz v31 + 1) + (sz v31 + 1)) + 1) + (sz v32 + 1)) + 1)) ∧ sz b = sz v32 ∧ sz o = ((((sz v31 + 1) + (sz v31 + 1)) + 1) + (sz v32 + 1)))
theorem code_cases {a b o : CM} (h : Code a b o) : CodeCases a b o := by
  unfold CodeCases
  cases h with
  | r0 => exact Or.inl ⟨_, _, _, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | r1 => exact Or.inr (Or.inl ⟨_, _, _, rfl, rfl, rfl, rfl, rfl, rfl⟩)
  | r2 => exact Or.inr (Or.inr (Or.inl ⟨_, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl⟩))
  | r3 => exact Or.inr (Or.inr (Or.inr (⟨_, _, _, rfl, rfl, rfl, rfl, rfl, rfl⟩)))
def NF : CM → Prop
  | e => True
  | k a => NF a
  | p a b => NF a ∧ NF b ∧ ¬ ∃ o, Code a b o
theorem nf_p_no {a b : CM} (h : NF (p a b)) : ¬ ∃ o, Code a b o := h.2.2
theorem nf_p_left {a b : CM} (h : NF (p a b)) : NF a := h.1
theorem nf_p_right {a b : CM} (h : NF (p a b)) : NF b := h.2.1
theorem eq_sz {a b : CM} (h : a = b) : sz a = sz b := congrArg sz h
theorem ne_p_left (a b : CM) : a ≠ p a b := by
  intro h
  have q := congrArg sz h
  simp [sz] at q
  omega
theorem ne_p_right (a b : CM) : b ≠ p a b := by
  intro h
  have q := congrArg sz h
  simp [sz] at q
  omega
theorem redex0_not_nf (v00 v01 v02 : CM) :
    ¬ NF (p (p (p v00 v00) v01) (p v01 v02)) := by
  intro h
  exact h.2.2 ⟨v01, Code.r0 v00 v01 v02⟩

theorem redex1_not_nf (v10 v11 v12 : CM) :
    ¬ NF (p (p v10 v10) (p (p (p v10 v10) v11) v12)) := by
  intro h
  exact h.2.2 ⟨(p (p v10 v10) v11), Code.r1 v10 v11 v12⟩

theorem redex2_not_nf (v20 v21 v22 v23 : CM) :
    ¬ NF (p (p (p v20 v20) v21) (p (p (p (p v20 v20) v21) v22) v23)) := by
  intro h
  exact h.2.2 ⟨(p (p (p v20 v20) v21) v22), Code.r2 v20 v21 v22 v23⟩

theorem redex3_not_nf (v30 v31 v32 : CM) :
    ¬ NF (p (p (p v30 v30) (p (p v31 v31) v32)) v32) := by
  intro h
  exact h.2.2 ⟨(p (p v31 v31) v32), Code.r3 v30 v31 v32⟩


theorem code_nf {a b o : CM} (ha : NF a) (hb : NF b) (h : Code a b o) : NF o := by
  cases h with
  | r0 => exact ha.2.1
  | r1 => exact hb.1
  | r2 => exact hb.1
  | r3 => exact ha.2.1
noncomputable def eval (a b : CM) : CM := by
  classical
  exact if h : ∃ o, Code a b o then Classical.choose h else p a b
theorem eval_raw {a b : CM} (h : ¬ ∃ o, Code a b o) : eval a b = p a b := by
  rw [eval, dif_neg h]
theorem eval_nf {a b : CM} (ha : NF a) (hb : NF b) : NF (eval a b) := by
  by_cases h : ∃ o, Code a b o
  · rw [eval, dif_pos h]
    exact code_nf ha hb (Classical.choose_spec h)
  · rw [eval_raw h]
    exact ⟨ha, hb, h⟩
def EvalCases (a b o : CM) : Prop := (∃ v00 v01 v02, a = (p (p v00 v00) v01) ∧ b = (p v01 v02) ∧ o = v01 ∧ sz a = ((((sz v00 + 1) + (sz v00 + 1)) + 1) + (sz v01 + 1)) ∧ sz b = ((sz v01 + 1) + (sz v02 + 1)) ∧ sz o = sz v01) ∨ (∃ v10 v11 v12, a = (p v10 v10) ∧ b = (p (p (p v10 v10) v11) v12) ∧ o = (p (p v10 v10) v11) ∧ sz a = ((sz v10 + 1) + (sz v10 + 1)) ∧ sz b = ((((((sz v10 + 1) + (sz v10 + 1)) + 1) + (sz v11 + 1)) + 1) + (sz v12 + 1)) ∧ sz o = ((((sz v10 + 1) + (sz v10 + 1)) + 1) + (sz v11 + 1))) ∨ (∃ v20 v21 v22 v23, a = (p (p v20 v20) v21) ∧ b = (p (p (p (p v20 v20) v21) v22) v23) ∧ o = (p (p (p v20 v20) v21) v22) ∧ sz a = ((((sz v20 + 1) + (sz v20 + 1)) + 1) + (sz v21 + 1)) ∧ sz b = ((((((((sz v20 + 1) + (sz v20 + 1)) + 1) + (sz v21 + 1)) + 1) + (sz v22 + 1)) + 1) + (sz v23 + 1)) ∧ sz o = ((((((sz v20 + 1) + (sz v20 + 1)) + 1) + (sz v21 + 1)) + 1) + (sz v22 + 1))) ∨ (∃ v30 v31 v32, a = (p (p v30 v30) (p (p v31 v31) v32)) ∧ b = v32 ∧ o = (p (p v31 v31) v32) ∧ sz a = ((((sz v30 + 1) + (sz v30 + 1)) + 1) + (((((sz v31 + 1) + (sz v31 + 1)) + 1) + (sz v32 + 1)) + 1)) ∧ sz b = sz v32 ∧ sz o = ((((sz v31 + 1) + (sz v31 + 1)) + 1) + (sz v32 + 1))) ∨ (o = p a b ∧ sz o = ((sz a + 1) + (sz b + 1)) ∧ ¬ ∃ q, Code a b q)
theorem eval_cases (a b : CM) : EvalCases a b (eval a b) := by
  by_cases h : ∃ o, Code a b o
  · let o := Classical.choose h
    have hc : Code a b o := Classical.choose_spec h
    have cc := code_cases hc
    have hv : eval a b = o := by rw [eval, dif_pos h]
    rw [hv]
    unfold CodeCases at cc
    rcases cc with c0 | c1 | c2 | c3
    · exact Or.inl c0
    · exact Or.inr (Or.inl c1)
    · exact Or.inr (Or.inr (Or.inl c2))
    · exact Or.inr (Or.inr (Or.inr (Or.inl c3)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (⟨eval_raw h, eq_sz (eval_raw h), h⟩))))

theorem source_raw (q0 q3 z : CM) (hq0 : NF q0) (hq3 : NF q3) (hz : NF z) :
    q0 = (eval (eval (eval q3 q3) q0) (eval q0 z)) := by
  classical
  have B0 := eval_cases q3 q3
  have B1 := eval_cases (eval q3 q3) q0
  have B2 := eval_cases q0 z
  have B3 := eval_cases (eval (eval q3 q3) q0) (eval q0 z)
  have Hsrc : Code (p (p q3 q3) q0) (p q0 z) q0 := .r0 q3 q0 z
  have N0 : NF (eval q3 q3) := eval_nf (hq3) (hq3)
  have N1 : NF (eval (eval q3 q3) q0) := eval_nf (eval_nf (hq3) (hq3)) (hq0)
  have N2 : NF (eval q0 z) := eval_nf (hq0) (hz)
  have N3 : NF (eval (eval (eval q3 q3) q0) (eval q0 z)) := eval_nf (eval_nf (eval_nf (hq3) (hq3)) (hq0)) (eval_nf (hq0) (hz))
  all_goals rcases B3 with ⟨b3_0_v00, b3_0_v01, b3_0_v02, b3_0_a, b3_0_b, b3_0_o, b3_0_sa, b3_0_sb, b3_0_so⟩ | ⟨b3_1_v10, b3_1_v11, b3_1_v12, b3_1_a, b3_1_b, b3_1_o, b3_1_sa, b3_1_sb, b3_1_so⟩ | ⟨b3_2_v20, b3_2_v21, b3_2_v22, b3_2_v23, b3_2_a, b3_2_b, b3_2_o, b3_2_sa, b3_2_sb, b3_2_so⟩ | ⟨b3_3_v30, b3_3_v31, b3_3_v32, b3_3_a, b3_3_b, b3_3_o, b3_3_sa, b3_3_sb, b3_3_so⟩ | ⟨b3_raw_o, b3_raw_so, b3_raw_no⟩
  all_goals try omega
  all_goals try grind (config := { splits := 1, gen := 6 }) [NF, nf_p_no, nf_p_left, nf_p_right, ne_p_left, ne_p_right, eq_sz, redex0_not_nf, redex1_not_nf, redex2_not_nf, redex3_not_nf, Code.r0, Code.r1, Code.r2, Code.r3, L, R, U, sz]
  all_goals rcases B2 with ⟨b2_0_v00, b2_0_v01, b2_0_v02, b2_0_a, b2_0_b, b2_0_o, b2_0_sa, b2_0_sb, b2_0_so⟩ | ⟨b2_1_v10, b2_1_v11, b2_1_v12, b2_1_a, b2_1_b, b2_1_o, b2_1_sa, b2_1_sb, b2_1_so⟩ | ⟨b2_2_v20, b2_2_v21, b2_2_v22, b2_2_v23, b2_2_a, b2_2_b, b2_2_o, b2_2_sa, b2_2_sb, b2_2_so⟩ | ⟨b2_3_v30, b2_3_v31, b2_3_v32, b2_3_a, b2_3_b, b2_3_o, b2_3_sa, b2_3_sb, b2_3_so⟩ | ⟨b2_raw_o, b2_raw_so, b2_raw_no⟩
  all_goals try omega
  all_goals try grind (config := { splits := 1, gen := 6 }) [NF, nf_p_no, nf_p_left, nf_p_right, ne_p_left, ne_p_right, eq_sz, redex0_not_nf, redex1_not_nf, redex2_not_nf, redex3_not_nf, Code.r0, Code.r1, Code.r2, Code.r3, L, R, U, sz]
  all_goals rcases B1 with ⟨b1_0_v00, b1_0_v01, b1_0_v02, b1_0_a, b1_0_b, b1_0_o, b1_0_sa, b1_0_sb, b1_0_so⟩ | ⟨b1_1_v10, b1_1_v11, b1_1_v12, b1_1_a, b1_1_b, b1_1_o, b1_1_sa, b1_1_sb, b1_1_so⟩ | ⟨b1_2_v20, b1_2_v21, b1_2_v22, b1_2_v23, b1_2_a, b1_2_b, b1_2_o, b1_2_sa, b1_2_sb, b1_2_so⟩ | ⟨b1_3_v30, b1_3_v31, b1_3_v32, b1_3_a, b1_3_b, b1_3_o, b1_3_sa, b1_3_sb, b1_3_so⟩ | ⟨b1_raw_o, b1_raw_so, b1_raw_no⟩
  all_goals try omega
  all_goals try grind (config := { splits := 1, gen := 6 }) [NF, nf_p_no, nf_p_left, nf_p_right, ne_p_left, ne_p_right, eq_sz, redex0_not_nf, redex1_not_nf, redex2_not_nf, redex3_not_nf, Code.r0, Code.r1, Code.r2, Code.r3, L, R, U, sz]
  all_goals rcases B0 with ⟨b0_0_v00, b0_0_v01, b0_0_v02, b0_0_a, b0_0_b, b0_0_o, b0_0_sa, b0_0_sb, b0_0_so⟩ | ⟨b0_1_v10, b0_1_v11, b0_1_v12, b0_1_a, b0_1_b, b0_1_o, b0_1_sa, b0_1_sb, b0_1_so⟩ | ⟨b0_2_v20, b0_2_v21, b0_2_v22, b0_2_v23, b0_2_a, b0_2_b, b0_2_o, b0_2_sa, b0_2_sb, b0_2_so⟩ | ⟨b0_3_v30, b0_3_v31, b0_3_v32, b0_3_a, b0_3_b, b0_3_o, b0_3_sa, b0_3_sb, b0_3_so⟩ | ⟨b0_raw_o, b0_raw_so, b0_raw_no⟩
  all_goals try omega
  all_goals try grind (config := { splits := 1, gen := 6 }) [NF, nf_p_no, nf_p_left, nf_p_right, ne_p_left, ne_p_right, eq_sz, redex0_not_nf, redex1_not_nf, redex2_not_nf, redex3_not_nf, Code.r0, Code.r1, Code.r2, Code.r3, L, R, U, sz]
  all_goals grind (config := { splits := 10, gen := 10 }) [NF, nf_p_no, nf_p_left, nf_p_right, ne_p_left, ne_p_right, eq_sz, redex0_not_nf, redex1_not_nf, redex2_not_nf, redex3_not_nf, Code.r0, Code.r1, Code.r2, Code.r3, L, R, U, sz]
def Carrier := {t : CM // NF t}
noncomputable def op (a b : Carrier) : Carrier := ⟨eval a.1 b.1, eval_nf a.2 b.2⟩
noncomputable instance instMagmaNF : Magma Carrier where op a b := op b a
theorem source_holds (q0 q3 z : Carrier) : q0 = (op (op (op q3 q3) q0) (op q0 z)) := by
  apply Subtype.ext
  exact source_raw q0.1 q3.1 z.1 q0.2 q3.2 z.2
def ce : Carrier := ⟨e, by simp [NF]⟩
def ck (a : Carrier) : Carrier := ⟨k a.1, by simpa [NF] using a.2⟩
theorem nt0 : ¬ ∃ o, Code (CM.k CM.e) CM.e o := by
  rintro ⟨o, h⟩
  cases h
theorem nt1 : ¬ ∃ o, Code (CM.p (CM.k CM.e) CM.e) (CM.k CM.e) o := by
  rintro ⟨o, h⟩
  cases h
theorem nt2 : ¬ ∃ o, Code (CM.k CM.e) (CM.k CM.e) o := by
  rintro ⟨o, h⟩
  cases h
theorem nt3 : ¬ ∃ o, Code (CM.k CM.e) (CM.p (CM.k CM.e) (CM.k CM.e)) o := by
  rintro ⟨o, h⟩
  cases h
theorem nt4 : ¬ ∃ o, Code (CM.p (CM.p (CM.k CM.e) CM.e) (CM.k CM.e)) (CM.p (CM.k CM.e) (CM.p (CM.k CM.e) (CM.k CM.e))) o := by
  rintro ⟨o, h⟩
  cases h
end CM
end submission
open submission
open submission.CM
noncomputable def submission : Goal := by
  refine ⟨CM.Carrier, CM.instMagmaNF, (fun q0 q1 q2 q3 => ((fun q0 q3 q2 q1 => CM.source_holds q0 q3 (op q2 q1))) q0 q3 q2 q1), ?_⟩
  intro target
  have bad := congrArg Subtype.val (target (ck ce) ce)
  change (CM.k CM.e) = (eval (eval (eval (CM.k CM.e) CM.e) (CM.k CM.e)) (eval (CM.k CM.e) (eval (CM.k CM.e) (CM.k CM.e)))) at bad
  have hl : (CM.k CM.e) = (CM.k CM.e) := rfl
  have hr : (eval (eval (eval (CM.k CM.e) CM.e) (CM.k CM.e)) (eval (CM.k CM.e) (eval (CM.k CM.e) (CM.k CM.e)))) = (CM.p (CM.p (CM.p (CM.k CM.e) CM.e) (CM.k CM.e)) (CM.p (CM.k CM.e) (CM.p (CM.k CM.e) (CM.k CM.e)))) := ((((congrArg (fun q => (eval (eval q (CM.k CM.e)) (eval (CM.k CM.e) (eval (CM.k CM.e) (CM.k CM.e))))) (eval_raw nt0)).trans (congrArg (fun q => (eval q (eval (CM.k CM.e) (eval (CM.k CM.e) (CM.k CM.e))))) (eval_raw nt1))).trans (congrArg (fun q => (eval (CM.p (CM.p (CM.k CM.e) CM.e) (CM.k CM.e)) (eval (CM.k CM.e) q))) (eval_raw nt2))).trans (congrArg (fun q => (eval (CM.p (CM.p (CM.k CM.e) CM.e) (CM.k CM.e)) q)) (eval_raw nt3))).trans ((eval_raw nt4))
  have nb := hl.symm.trans (bad.trans hr)
  exact Bool.noConfusion (congrArg (fun q => match q with | e => false | k _ => false | p _ _ => true) nb)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_23632_to_23114 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_23632_to_23114
