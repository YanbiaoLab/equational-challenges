-- Equation49389 → Equation46648
-- Recorded verdict: true
-- Premise: x * y = ((z * w) * u) * (x * u)
-- Conclusion: x * y = (z * z) * (w * (u * u))
-- Original submission SHA-256: c00f3de9d632608b112ce179b1199ee3cdc7383a8e96848e23fd33b3b857aafd
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = ((z ◇ w) ◇ u) ◇ (x ◇ u)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = (z ◇ z) ◇ (w ◇ (u ◇ u))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (q0 q1 q2 q3 q4 : G), ((q0 ◇ q1) ◇ (q3 ◇ (q0 ◇ q2))) = (q3 ◇ q4) := by
    intro q0 q1 q2 q3 q4
    exact ((rfl).symm).trans ((((congrArg (fun t => t ◇ (q3 ◇ (q0 ◇ q2))) ((h q0 q1 q0 q0 q2).symm)).symm).trans ((h q3 q4 (q0 ◇ q0) q2 (q0 ◇ q2)).symm)).trans (rfl))
  have apc1 : forall (q5 q6 q7 q8 q9 q10 q11 : G), ((q9 ◇ q10) ◇ ((q5 ◇ q6) ◇ (q9 ◇ q11))) = (q7 ◇ q8) := by
    intro q5 q6 q7 q8 q9 q10 q11
    exact (((rfl).symm).trans ((((apc0 q5 q6 q5 q7 q8).symm).trans ((apc0 q9 q10 q11 (q5 ◇ q6) (q7 ◇ (q5 ◇ q5))).symm)).trans (rfl))).symm
  have apc2 : forall (q12 q13 q14 q15 q16 : G), ((q15 ◇ q16) ◇ (q15 ◇ q12)) = (q13 ◇ q14) := by
    intro q12 q13 q14 q15 q16
    exact ((rfl).symm).trans ((((congrArg (fun t => (q15 ◇ q16) ◇ t) (apc0 q12 q12 q12 q15 q12)).symm).trans (apc1 q12 q12 q13 q14 q15 q16 (q12 ◇ q12))).trans (rfl))
  have apc4 : forall (q17 q18 q19 q20 q21 q22 : G), ((q21 ◇ q22) ◇ (q17 ◇ q18)) = (q19 ◇ q20) := by
    intro q17 q18 q19 q20 q21 q22
    exact ((rfl).symm).trans ((((congrArg (fun t => (q21 ◇ q22) ◇ t) (apc2 q17 q17 q18 q21 q17)).symm).trans (apc1 q21 q17 q19 q20 q21 q22 q17)).trans (rfl))
  have apc5 : forall (x y z w u : G), (((z ◇ w) ◇ u) ◇ (x ◇ u)) = (((x ◇ x) ◇ x) ◇ (x ◇ x)) := by
    intro x y z w u
    exact ((rfl).symm).trans (((h x y z w u).symm.trans (h x y x x x)).trans (rfl))
  have apc11 : forall (x y z w u : G), (x ◇ y) = (x ◇ x) := by
    intro x y z w u
    exact ((rfl).symm).trans (((h x y z w u).trans ((h x x z w u).symm)).trans (rfl))
  have apc12 : forall (x y z w u q0 q1 q2 q3 q4 : G), ((q0 ◇ q0) ◇ (q0 ◇ q0)) = (q3 ◇ q3) := by
    intro x y z w u q0 q1 q2 q3 q4
    exact ((rfl).symm).trans (((((((congrArg (fun t => (q0 ◇ q1) ◇ t) (congrArg (fun t => q3 ◇ t) (apc11 q0 q2 (q0 ◇ q2) (q0 ◇ q2) (q0 ◇ q2)))).trans (congrArg (fun t => t ◇ (q3 ◇ (q0 ◇ q0))) (apc11 q0 q1 (q0 ◇ q1) (q0 ◇ q1) (q0 ◇ q1)))).trans (congrArg (fun t => (q0 ◇ q0) ◇ t) (apc11 q3 (q0 ◇ q0) (q3 ◇ (q0 ◇ q0)) (q3 ◇ (q0 ◇ q0)) (q3 ◇ (q0 ◇ q0))))).trans (apc11 (q0 ◇ q0) (q3 ◇ q3) ((q0 ◇ q0) ◇ (q3 ◇ q3)) ((q0 ◇ q0) ◇ (q3 ◇ q3)) ((q0 ◇ q0) ◇ (q3 ◇ q3)))).symm).trans ((apc0 q0 q1 q2 q3 q4).trans (apc11 q3 q4 (q3 ◇ q4) (q3 ◇ q4) (q3 ◇ q4)))).trans (rfl))
  have apc13 : forall (x y z w u q17 q18 q19 q20 q21 q22 : G), ((q21 ◇ q21) ◇ (q17 ◇ q17)) = (q19 ◇ q19) := by
    intro x y z w u q17 q18 q19 q20 q21 q22
    exact ((rfl).symm).trans (((((congrArg (fun t => (q21 ◇ q22) ◇ t) (apc11 q17 q18 (q17 ◇ q18) (q17 ◇ q18) (q17 ◇ q18))).trans (congrArg (fun t => t ◇ (q17 ◇ q17)) (apc11 q21 q22 (q21 ◇ q22) (q21 ◇ q22) (q21 ◇ q22)))).symm).trans ((apc4 q17 q18 q19 q20 q21 q22).trans (apc11 q19 q20 (q19 ◇ q20) (q19 ◇ q20) (q19 ◇ q20)))).trans (rfl))
  have apc17 : forall (q23 q24 q25 q26 : G), ((q26 ◇ q24) ◇ q25) = (q23 ◇ q23) := by
    intro q23 q24 q25 q26
    exact (((rfl).symm).trans ((((apc12 q23 q23 q23 q23 q23 (q26 ◇ q24) q23 q23 q23 q23).symm).trans ((h (q26 ◇ q24) q25 q26 q24 (q26 ◇ q24)).symm)).trans (rfl))).symm
  have apc20 : forall (q27 q28 q29 q30 q2 q3 q4 q31 : G), ((((q29 ◇ q28) ◇ q27) ◇ ((q29 ◇ q28) ◇ q27)) ◇ (q3 ◇ q30)) = (q3 ◇ q3) := by
    intro q27 q28 q29 q30 q2 q3 q4 q31
    exact ((congrArg (fun t => t ◇ (q3 ◇ q30)) (apc11 ((q29 ◇ q28) ◇ q27) ((q31 ◇ q2) ◇ q27) (((q29 ◇ q28) ◇ q27) ◇ ((q31 ◇ q2) ◇ q27)) (((q29 ◇ q28) ◇ q27) ◇ ((q31 ◇ q2) ◇ q27)) (((q29 ◇ q28) ◇ q27) ◇ ((q31 ◇ q2) ◇ q27)))).symm).trans ((((congrArg (fun t => t ◇ (q3 ◇ q30)) (h (q31 ◇ q2) q30 q29 q28 q27)).symm).trans ((h q3 q4 q31 q2 q30).symm)).trans (apc11 q3 q4 (q3 ◇ q4) (q3 ◇ q4) (q3 ◇ q4)))
  have apc21 : forall (q27 q28 q29 q30 q3 q4 q31 : G), (((q3 ◇ q3) ◇ q3) ◇ (q3 ◇ q3)) = (q3 ◇ q3) := by
    intro q27 q28 q29 q30 q3 q4 q31
    exact ((apc5 q3 (((((q29 ◇ q28) ◇ q27) ◇ (q31 ◇ q27)) ◇ q30) ◇ (q3 ◇ q30)) ((q29 ◇ q28) ◇ q27) (q31 ◇ q27) q30).symm).trans ((((congrArg (fun t => t ◇ (q3 ◇ q30)) (congrArg (fun t => t ◇ q30) (h q31 q27 q29 q28 q27))).symm).trans ((h q3 q4 q31 q27 q30).symm)).trans (apc11 q3 q4 (q3 ◇ q4) (q3 ◇ q4) (q3 ◇ q4)))
  have apc41 : forall (q32 q33 q34 q35 q36 q37 : G), ((q35 ◇ q35) ◇ (q32 ◇ q32)) = ((q35 ◇ q34) ◇ q37) := by
    intro q32 q33 q34 q35 q36 q37
    exact (((congrArg (fun t => (q35 ◇ q36) ◇ t) (apc11 q32 q33 (q32 ◇ q33) (q32 ◇ q33) (q32 ◇ q33))).trans (congrArg (fun t => t ◇ (q32 ◇ q32)) (apc11 q35 q36 (q35 ◇ q36) (q35 ◇ q36) (q35 ◇ q36)))).symm).trans ((((congrArg (fun t => (q35 ◇ q36) ◇ t) (apc2 q32 q32 q33 q35 q34)).symm).trans (apc0 q35 q36 q32 (q35 ◇ q34) q37)).trans (rfl))
  have apc44 : forall (q38 q39 q40 : G), ((q39 ◇ q39) ◇ (q39 ◇ q39)) = ((q39 ◇ q38) ◇ q40) := by
    intro q38 q39 q40
    exact (((rfl).symm).trans ((((apc41 q38 q38 q38 q39 q38 q40).symm).trans (apc11 (q39 ◇ q39) (q38 ◇ q38) q38 q38 q38)).trans (rfl))).symm
  have apc46 : forall (q41 q42 q43 q44 q45 : G), (((q43 ◇ q41) ◇ q42) ◇ (q45 ◇ q44)) = (q45 ◇ q45) := by
    intro q41 q42 q43 q44 q45
    exact ((rfl).symm).trans ((((congrArg (fun t => t ◇ (q45 ◇ q44)) ((apc17 ((q41 ◇ q41) ◇ q41) q41 q42 q43).symm)).symm).trans (apc20 q41 q41 q41 q44 q41 q45 q41 q41)).trans (rfl))
  have apc56 : forall (q46 q47 q48 : G), ((q48 ◇ q48) ◇ (q48 ◇ q48)) = (q48 ◇ q48) := by
    intro q46 q47 q48
    exact (((apc11 ((q48 ◇ q48) ◇ q48) ((q47 ◇ q47) ◇ (q46 ◇ q46)) (((q48 ◇ q48) ◇ q48) ◇ ((q47 ◇ q47) ◇ (q46 ◇ q46))) (((q48 ◇ q48) ◇ q48) ◇ ((q47 ◇ q47) ◇ (q46 ◇ q46))) (((q48 ◇ q48) ◇ q48) ◇ ((q47 ◇ q47) ◇ (q46 ◇ q46)))).trans (apc46 q48 q48 q48 q48 (q48 ◇ q48))).symm).trans ((((congrArg (fun t => ((q48 ◇ q48) ◇ q48) ◇ t) ((apc13 q46 q46 q46 q46 q46 q46 q46 q48 q46 q47 q46).symm)).symm).trans (apc21 q46 q46 q46 q46 q48 q46 q46)).trans (rfl))
  have apc59 : forall (q46 q47 q48 q38 q39 q40 : G), ((q39 ◇ q38) ◇ q40) = (q39 ◇ q39) := by
    intro q46 q47 q48 q38 q39 q40
    exact (((rfl).symm).trans ((((apc56 ((q39 ◇ q39) ◇ (q39 ◇ q39)) ((q39 ◇ q39) ◇ (q39 ◇ q39)) q39).symm).trans ((apc44 q38 q39 q40).trans (rfl))).trans (rfl))).symm
  exact (calc
    (x ◇ y) = (((z ◇ z) ◇ z) ◇ (x ◇ z)) := h x y z z z
    _ = ((z ◇ z) ◇ (z ◇ z)) := apc59 u u u z (z ◇ z) (x ◇ z)
    _ = ((z ◇ z) ◇ (w ◇ (u ◇ u))) := (apc11 (z ◇ z) (w ◇ (u ◇ u)) u u u).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_49389_to_46648 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_49389_to_46648
