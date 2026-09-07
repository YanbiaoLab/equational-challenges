-- Equation23576 → Equation59187
-- Recorded verdict: true
-- Premise: x = ((y ◇ y) ◇ z) ◇ (z ◇ (x ◇ z))
-- Conclusion: (x ◇ x) ◇ y = y ◇ ((z ◇ z) ◇ y)
-- Original submission SHA-256: 4abf1f662fd18c52f7ad8cbd50d5b042f0f9c6fec251a0d7faa0eca1ca3ea3d3
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ y) ◇ z) ◇ (z ◇ (x ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ x) ◇ y = y ◇ ((z ◇ z) ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3 : G), (((q3 ◇ q3) ◇ (q2 ◇ (q0 ◇ q2))) ◇ ((q2 ◇ (q0 ◇ q2)) ◇ q0)) = ((q1 ◇ q1) ◇ q2) := by
    intro q0 q1 q2 q3
    exact ((rfl).symm).trans ((((congrArg (fun t => ((q3 ◇ q3) ◇ (q2 ◇ (q0 ◇ q2))) ◇ t) (congrArg (fun t => (q2 ◇ (q0 ◇ q2)) ◇ t) ((h q0 q1 q2).symm))).symm).trans ((h ((q1 ◇ q1) ◇ q2) q3 (q2 ◇ (q0 ◇ q2))).symm)).trans (rfl))
  have apc1 : forall (q0 q1 q2 q3 : G), ((q1 ◇ q1) ◇ q2) = ((q0 ◇ q0) ◇ q2) := by
    intro q0 q1 q2 q3
    exact ((rfl).symm).trans (((apc0 q0 q1 q2 q3).symm.trans (apc0 q0 q0 q2 q3)).trans (rfl))
  have apc2 : forall (q4 q5 q6 q7 : G), (((q4 ◇ q4) ◇ (q5 ◇ q5)) ◇ q7) = ((q6 ◇ q6) ◇ q7) := by
    intro q4 q5 q6 q7
    exact ((rfl).symm).trans ((((congrArg (fun t => t ◇ q7) (apc1 q4 q5 (q5 ◇ q5) q4)).symm).trans (apc1 q6 (q5 ◇ q5) q7 q4)).trans (rfl))
  have apc3 : forall (q8 q9 q10 : G), (q9 ◇ (((q8 ◇ q8) ◇ (q9 ◇ (q8 ◇ q8))) ◇ q9)) = ((q10 ◇ q10) ◇ (q8 ◇ q8)) := by
    intro q8 q9 q10
    exact ((rfl).symm).trans ((((congrArg (fun t => t ◇ (((q8 ◇ q8) ◇ (q9 ◇ (q8 ◇ q8))) ◇ q9)) ((h q9 q8 (q8 ◇ q8)).symm)).symm).trans (apc0 q9 q10 (q8 ◇ q8) (q8 ◇ q8))).trans (rfl))
  have apc4 : forall (q8 q9 q10 : G), ((q10 ◇ q10) ◇ (q8 ◇ q8)) = ((q8 ◇ q8) ◇ (q8 ◇ q8)) := by
    intro q8 q9 q10
    exact ((rfl).symm).trans (((apc3 q8 q9 q10).symm.trans (apc3 q8 q9 q8)).trans (rfl))
  have apc5 : forall (x y z : G), (((y ◇ y) ◇ z) ◇ (z ◇ (x ◇ z))) = (((x ◇ x) ◇ x) ◇ (x ◇ (x ◇ x))) := by
    intro x y z
    exact ((rfl).symm).trans (((h x y z).symm.trans (h x x x)).trans (rfl))
  have apc6 : forall (q11 q12 q13 : G), ((q12 ◇ q12) ◇ ((q11 ◇ q11) ◇ (q12 ◇ q12))) = ((q12 ◇ q12) ◇ (q12 ◇ q12)) := by
    intro q11 q12 q13
    exact ((rfl).symm).trans ((((congrArg (fun t => (q12 ◇ q12) ◇ t) (apc2 q12 (q12 ◇ q12) q11 (q12 ◇ q12))).symm).trans (apc3 q12 (q12 ◇ q12) q13)).trans (apc4 q12 ((q13 ◇ q13) ◇ (q12 ◇ q12)) q13))
  have apc7 : forall (q14 q15 q16 : G), ((q15 ◇ q15) ◇ ((q14 ◇ q14) ◇ (q16 ◇ q16))) = ((q16 ◇ q16) ◇ (q16 ◇ q16)) := by
    intro q14 q15 q16
    exact (((rfl).symm).trans ((((apc6 q14 q16 q14).symm).trans (apc1 q15 q16 ((q14 ◇ q14) ◇ (q16 ◇ q16)) q14)).trans (rfl))).symm
  have apc11 : forall (q17 q18 q19 : G), ((q17 ◇ q17) ◇ ((q19 ◇ q19) ◇ (q18 ◇ (q19 ◇ q19)))) = q18 := by
    intro q17 q18 q19
    exact ((rfl).symm).trans ((((apc1 q17 (q19 ◇ q19) ((q19 ◇ q19) ◇ (q18 ◇ (q19 ◇ q19))) q17).symm).trans ((h q18 q19 (q19 ◇ q19)).symm)).trans (rfl))
  have apc13 : forall (q20 q21 : G), ((q20 ◇ q20) ◇ (q20 ◇ q20)) = (q20 ◇ q20) := by
    intro q20 q21
    exact ((apc4 q20 ((q21 ◇ q21) ◇ (q20 ◇ q20)) q21).symm).trans ((((congrArg (fun t => (q21 ◇ q21) ◇ t) (apc11 (q20 ◇ q20) (q20 ◇ q20) q20)).symm).trans (apc11 q21 (q20 ◇ q20) (q20 ◇ q20))).trans (rfl))
  have apc14 : forall (q8 q9 q10 q20 q21 : G), ((q10 ◇ q10) ◇ (q8 ◇ q8)) = (q8 ◇ q8) := by
    intro q8 q9 q10 q20 q21
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc4 q8 q9 q10).trans (apc13 q8 ((q8 ◇ q8) ◇ (q8 ◇ q8))))).trans (rfl))
  have apc28 : forall (q22 q23 q24 : G), (q24 ◇ q24) = (q22 ◇ q22) := by
    intro q22 q23 q24
    exact (((congrArg (fun t => (q23 ◇ q23) ◇ t) (apc14 q24 ((q24 ◇ q24) ◇ (q24 ◇ q24)) q24 ((q24 ◇ q24) ◇ (q24 ◇ q24)) ((q24 ◇ q24) ◇ (q24 ◇ q24)))).trans (apc14 q24 ((q23 ◇ q23) ◇ (q24 ◇ q24)) q23 ((q23 ◇ q23) ◇ (q24 ◇ q24)) ((q23 ◇ q23) ◇ (q24 ◇ q24)))).symm).trans ((((congrArg (fun t => (q23 ◇ q23) ◇ t) (apc7 q22 q24 q24)).symm).trans (apc11 q23 (q22 ◇ q22) q24)).trans (rfl))
  have apc49 : forall (q25 q26 q27 q28 q29 : G), (((q29 ◇ q29) ◇ (q28 ◇ ((q25 ◇ q25) ◇ q28))) ◇ ((q28 ◇ ((q26 ◇ q26) ◇ q28)) ◇ (q26 ◇ q26))) = ((q27 ◇ q27) ◇ q28) := by
    intro q25 q26 q27 q28 q29
    exact ((rfl).symm).trans ((((congrArg (fun t => t ◇ ((q28 ◇ ((q26 ◇ q26) ◇ q28)) ◇ (q26 ◇ q26))) (congrArg (fun t => (q29 ◇ q29) ◇ t) (congrArg (fun t => q28 ◇ t) (apc1 q25 q26 q28 q25)))).symm).trans (apc0 (q26 ◇ q26) q27 q28 q29)).trans (rfl))
  have apc53 : forall (q30 : G), (((q30 ◇ q30) ◇ q30) ◇ (q30 ◇ (q30 ◇ q30))) = q30 := by
    intro q30
    exact ((rfl).symm).trans ((((apc5 q30 q30 q30).symm).trans ((h q30 q30 q30).symm)).trans (rfl))
  have apc90 : forall (q31 q32 : G), (((q32 ◇ q32) ◇ q32) ◇ (q32 ◇ (q31 ◇ q31))) = q32 := by
    intro q31 q32
    exact ((rfl).symm).trans ((((congrArg (fun t => ((q32 ◇ q32) ◇ q32) ◇ t) (congrArg (fun t => q32 ◇ t) (apc28 q31 q31 q32))).symm).trans (apc53 q32)).trans (rfl))
  have apc91 : forall (q33 q34 q35 : G), (q35 ◇ ((q33 ◇ q33) ◇ q35)) = ((q34 ◇ q34) ◇ q35) := by
    intro q33 q34 q35
    exact ((rfl).symm).trans ((((apc90 q33 (q35 ◇ ((q33 ◇ q33) ◇ q35))).symm).trans (apc49 q33 q33 q34 q35 (q35 ◇ ((q33 ◇ q33) ◇ q35)))).trans (rfl))
  exact (apc91 z x y).symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_23576_to_59187 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_23576_to_59187
