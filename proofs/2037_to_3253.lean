-- Equation2037 → Equation3253
-- Recorded verdict: false
-- Premise: x = ((x ◇ x) ◇ x) ◇ (y ◇ x)
-- Conclusion: x ◇ x = x ◇ (x ◇ (x ◇ x))
-- Original submission SHA-256: 985fb907c334aee23cbb5f3034c093abe340698fb787dc373e934f310b68508c
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = ((x ◇ x) ◇ x) ◇ (y ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G), x ◇ x = x ◇ (x ◇ (x ◇ x))
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Original submission body
                   
set_option maxRecDepth 100000
set_option maxHeartbeats 2500000
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
  | r0 (v00 v01 : CM) : Code (p (p v00 v00) v00) (p v01 v00) v00
  | r1 (v10 v11 v12 : CM) : Code (p v10 (p v11 v10)) (p v12 (p v11 v10)) (p v11 v10)
  | r2 (v20 v21 : CM) : Code (p (p (p v20 v21) (p v20 v21)) (p v20 v21)) v21 (p v20 v21)
  | r3 (v30 v31 v32 : CM) : Code (p (p v30 v31) v31) (p v32 v31) v31
  | r4 (v40 v41 : CM) : Code (p v40 (p v41 v40)) v40 (p v41 v40)
  | r5 (v50 v51 v52 : CM) : Code (p (p v50 (p v51 v52)) (p v51 v52)) v52 (p v51 v52)
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
theorem redex0_not_nf (v00 v01 : CM) :
    ¬ NF (p (p (p v00 v00) v00) (p v01 v00)) := by
  intro h
  exact h.2.2 ⟨v00, Code.r0 v00 v01⟩

theorem redex1_not_nf (v10 v11 v12 : CM) :
    ¬ NF (p (p v10 (p v11 v10)) (p v12 (p v11 v10))) := by
  intro h
  exact h.2.2 ⟨(p v11 v10), Code.r1 v10 v11 v12⟩

theorem redex2_not_nf (v20 v21 : CM) :
    ¬ NF (p (p (p (p v20 v21) (p v20 v21)) (p v20 v21)) v21) := by
  intro h
  exact h.2.2 ⟨(p v20 v21), Code.r2 v20 v21⟩

theorem redex3_not_nf (v30 v31 v32 : CM) :
    ¬ NF (p (p (p v30 v31) v31) (p v32 v31)) := by
  intro h
  exact h.2.2 ⟨v31, Code.r3 v30 v31 v32⟩

theorem redex4_not_nf (v40 v41 : CM) :
    ¬ NF (p (p v40 (p v41 v40)) v40) := by
  intro h
  exact h.2.2 ⟨(p v41 v40), Code.r4 v40 v41⟩

theorem redex5_not_nf (v50 v51 v52 : CM) :
    ¬ NF (p (p (p v50 (p v51 v52)) (p v51 v52)) v52) := by
  intro h
  exact h.2.2 ⟨(p v51 v52), Code.r5 v50 v51 v52⟩


theorem code_nf {a b o : CM} (ha : NF a) (hb : NF b) (h : Code a b o) : NF o := by
  cases h with
  | r0 => exact ha.2.1
  | r1 => exact ha.2.1
  | r2 => exact ha.2.1
  | r3 => exact ha.2.1
  | r4 => exact ha.2.1
  | r5 => exact ha.2.1
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
inductive EvalCases : CM → CM → CM → Prop
  | r0 (v00 v01 : CM) : EvalCases (p (p v00 v00) v00) (p v01 v00) v00
  | r1 (v10 v11 v12 : CM) : EvalCases (p v10 (p v11 v10)) (p v12 (p v11 v10)) (p v11 v10)
  | r2 (v20 v21 : CM) : EvalCases (p (p (p v20 v21) (p v20 v21)) (p v20 v21)) v21 (p v20 v21)
  | r3 (v30 v31 v32 : CM) : EvalCases (p (p v30 v31) v31) (p v32 v31) v31
  | r4 (v40 v41 : CM) : EvalCases (p v40 (p v41 v40)) v40 (p v41 v40)
  | r5 (v50 v51 v52 : CM) : EvalCases (p (p v50 (p v51 v52)) (p v51 v52)) v52 (p v51 v52)
  | raw {a b : CM} (n : ¬ ∃ q, Code a b q) : EvalCases a b (p a b)
theorem no_code_r0 {v00 v01 : CM} (n : ¬ ∃ q, Code (p (p v00 v00) v00) (p v01 v00) q) : False := n ⟨_, Code.r0 v00 v01⟩
theorem no_code_r1 {v10 v11 v12 : CM} (n : ¬ ∃ q, Code (p v10 (p v11 v10)) (p v12 (p v11 v10)) q) : False := n ⟨_, Code.r1 v10 v11 v12⟩
theorem no_code_r2 {v20 v21 : CM} (n : ¬ ∃ q, Code (p (p (p v20 v21) (p v20 v21)) (p v20 v21)) v21 q) : False := n ⟨_, Code.r2 v20 v21⟩
theorem no_code_r3 {v30 v31 v32 : CM} (n : ¬ ∃ q, Code (p (p v30 v31) v31) (p v32 v31) q) : False := n ⟨_, Code.r3 v30 v31 v32⟩
theorem no_code_r4 {v40 v41 : CM} (n : ¬ ∃ q, Code (p v40 (p v41 v40)) v40 q) : False := n ⟨_, Code.r4 v40 v41⟩
theorem no_code_r5 {v50 v51 v52 : CM} (n : ¬ ∃ q, Code (p (p v50 (p v51 v52)) (p v51 v52)) v52 q) : False := n ⟨_, Code.r5 v50 v51 v52⟩
theorem nf_code_r0 {v00 v01 : CM} (h : NF (p (p (p v00 v00) v00) (p v01 v00))) : False := redex0_not_nf v00 v01 h
theorem nf_code_r1 {v10 v11 v12 : CM} (h : NF (p (p v10 (p v11 v10)) (p v12 (p v11 v10)))) : False := redex1_not_nf v10 v11 v12 h
theorem nf_code_r2 {v20 v21 : CM} (h : NF (p (p (p (p v20 v21) (p v20 v21)) (p v20 v21)) v21)) : False := redex2_not_nf v20 v21 h
theorem nf_code_r3 {v30 v31 v32 : CM} (h : NF (p (p (p v30 v31) v31) (p v32 v31))) : False := redex3_not_nf v30 v31 v32 h
theorem nf_code_r4 {v40 v41 : CM} (h : NF (p (p v40 (p v41 v40)) v40)) : False := redex4_not_nf v40 v41 h
theorem nf_code_r5 {v50 v51 v52 : CM} (h : NF (p (p (p v50 (p v51 v52)) (p v51 v52)) v52)) : False := redex5_not_nf v50 v51 v52 h
theorem eval_cases_of_code {a b o : CM} (h : Code a b o) : EvalCases a b o := by
  cases h with
  | r0 => exact .r0 _ _
  | r1 => exact .r1 _ _ _
  | r2 => exact .r2 _ _
  | r3 => exact .r3 _ _ _
  | r4 => exact .r4 _ _
  | r5 => exact .r5 _ _ _
theorem eval_cases (a b : CM) : EvalCases a b (eval a b) := by
  by_cases h : ∃ o, Code a b o
  · rw [eval, dif_pos h]
    exact eval_cases_of_code (Classical.choose_spec h)
  · rw [eval_raw h]
    exact .raw h

theorem source_raw (q0 q1 : CM) (hq0 : NF q0) (hq1 : NF q1) :
    q0 = (eval (eval (eval q0 q0) q0) (eval q1 q0)) := by
  classical
  generalize hE0 : (eval q0 q0) = E0
  generalize hE1 : (eval E0 q0) = E1
  generalize hE2 : (eval q1 q0) = E2
  generalize hE3 : (eval E1 E2) = E3
  have B0 : EvalCases q0 q0 E0 := by rw [← hE0]; exact eval_cases q0 q0
  have B1 : EvalCases E0 q0 E1 := by rw [← hE1]; exact eval_cases E0 q0
  have B2 : EvalCases q1 q0 E2 := by rw [← hE2]; exact eval_cases q1 q0
  have B3 : EvalCases E1 E2 E3 := by rw [← hE3]; exact eval_cases E1 E2
  have Hsrc : Code (p (p q0 q0) q0) (p q1 q0) q0 := .r0 q0 q1
  have N0 : NF E0 := by rw [← hE0]; exact eval_nf (hq0) (hq0)
  have N1 : NF E1 := by rw [← hE1]; exact eval_nf (N0) (hq0)
  have N2 : NF E2 := by rw [← hE2]; exact eval_nf (hq1) (hq0)
  have N3 : NF E3 := by rw [← hE3]; exact eval_nf (N1) (N2)
  all_goals cases B3
  all_goals first
  | exfalso; apply no_code_r0 <;> assumption
  | exfalso; apply no_code_r1 <;> assumption
  | exfalso; apply no_code_r2 <;> assumption
  | exfalso; apply no_code_r3 <;> assumption
  | exfalso; apply no_code_r4 <;> assumption
  | exfalso; apply no_code_r5 <;> assumption
  | exfalso; apply nf_code_r0 <;> assumption
  | exfalso; apply nf_code_r1 <;> assumption
  | exfalso; apply nf_code_r2 <;> assumption
  | exfalso; apply nf_code_r3 <;> assumption
  | exfalso; apply nf_code_r4 <;> assumption
  | exfalso; apply nf_code_r5 <;> assumption
  | rfl
  | omega
  | skip
  all_goals cases B2
  all_goals first
  | exfalso; apply no_code_r0 <;> assumption
  | exfalso; apply no_code_r1 <;> assumption
  | exfalso; apply no_code_r2 <;> assumption
  | exfalso; apply no_code_r3 <;> assumption
  | exfalso; apply no_code_r4 <;> assumption
  | exfalso; apply no_code_r5 <;> assumption
  | exfalso; apply nf_code_r0 <;> assumption
  | exfalso; apply nf_code_r1 <;> assumption
  | exfalso; apply nf_code_r2 <;> assumption
  | exfalso; apply nf_code_r3 <;> assumption
  | exfalso; apply nf_code_r4 <;> assumption
  | exfalso; apply nf_code_r5 <;> assumption
  | rfl
  | omega
  | skip
  all_goals cases B1
  all_goals first
  | exfalso; apply no_code_r0 <;> assumption
  | exfalso; apply no_code_r1 <;> assumption
  | exfalso; apply no_code_r2 <;> assumption
  | exfalso; apply no_code_r3 <;> assumption
  | exfalso; apply no_code_r4 <;> assumption
  | exfalso; apply no_code_r5 <;> assumption
  | exfalso; apply nf_code_r0 <;> assumption
  | exfalso; apply nf_code_r1 <;> assumption
  | exfalso; apply nf_code_r2 <;> assumption
  | exfalso; apply nf_code_r3 <;> assumption
  | exfalso; apply nf_code_r4 <;> assumption
  | exfalso; apply nf_code_r5 <;> assumption
  | rfl
  | omega
  | skip
  all_goals cases B0
  all_goals first
  | exfalso; apply no_code_r0 <;> assumption
  | exfalso; apply no_code_r1 <;> assumption
  | exfalso; apply no_code_r2 <;> assumption
  | exfalso; apply no_code_r3 <;> assumption
  | exfalso; apply no_code_r4 <;> assumption
  | exfalso; apply no_code_r5 <;> assumption
  | exfalso; apply nf_code_r0 <;> assumption
  | exfalso; apply nf_code_r1 <;> assumption
  | exfalso; apply nf_code_r2 <;> assumption
  | exfalso; apply nf_code_r3 <;> assumption
  | exfalso; apply nf_code_r4 <;> assumption
  | exfalso; apply nf_code_r5 <;> assumption
  | rfl
  | omega
  | skip
  all_goals first | rfl | omega | grind
  all_goals done
def Carrier := {t : CM // NF t}
noncomputable def op (a b : Carrier) : Carrier := ⟨eval a.1 b.1, eval_nf a.2 b.2⟩
noncomputable instance instMagmaNF : Magma Carrier where op := op
theorem source_holds (q0 q1 : Carrier) : q0 = (op (op (op q0 q0) q0) (op q1 q0)) := by
  apply Subtype.ext
  exact source_raw q0.1 q1.1 q0.2 q1.2
def ce : Carrier := ⟨e, by simp [NF]⟩
def ck (a : Carrier) : Carrier := ⟨k a.1, by simpa [NF] using a.2⟩
theorem nt0 : ¬ ∃ o, Code CM.e CM.e o := by
  rintro ⟨o, h⟩
  cases h
theorem nt2 : ¬ ∃ o, Code CM.e (CM.p CM.e CM.e) o := by
  rintro ⟨o, h⟩
  cases h
theorem nt3 : ¬ ∃ o, Code CM.e (CM.p CM.e (CM.p CM.e CM.e)) o := by
  rintro ⟨o, h⟩
  cases h
end CM
end submission
open submission
open submission.CM
noncomputable def submission : Goal := by
  refine ⟨CM.Carrier, CM.instMagmaNF, CM.source_holds, ?_⟩
  intro target
  have bad := congrArg Subtype.val (target ce)
  change (eval CM.e CM.e) = (eval CM.e (eval CM.e (eval CM.e CM.e))) at bad
  have hl : (eval CM.e CM.e) = (CM.p CM.e CM.e) := (eval_raw nt0)
  have hr : (eval CM.e (eval CM.e (eval CM.e CM.e))) = (CM.p CM.e (CM.p CM.e (CM.p CM.e CM.e))) := ((congrArg (fun q => (eval CM.e (eval CM.e q))) (eval_raw nt0)).trans (congrArg (fun q => (eval CM.e q)) (eval_raw nt2))).trans ((eval_raw nt3))
  have nb := hl.symm.trans (bad.trans hr)
  exact Bool.noConfusion (congrArg (fun q => match (R q) with | e => false | k _ => false | p _ _ => true) nb)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_2037_to_3253 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_2037_to_3253
