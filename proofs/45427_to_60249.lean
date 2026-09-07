-- Equation45427 → Equation60249
-- Recorded verdict: true
-- Premise: x * y = y * (((x * z) * w) * u)
-- Conclusion: (x * y) * x = (z * y) * (z * y)
-- Original submission SHA-256: 82e80695c037233c96877862e05c22c9b60c9f23c570fd56f174328de44e6957
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = y ◇ (((x ◇ z) ◇ w) ◇ u)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ x = (z ◇ y) ◇ (z ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3 q4:G), (q3 ◇ (q0 ◇ ((q2 ◇ q4) ◇ q1))) = (q2 ◇ q3):=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => q3 ◇ t) ((h q0 ((q2 ◇ q4) ◇ q1) q0 q0 q0).symm)).symm).trans ((h q2 q3 q4 q1 (((q0 ◇ q0) ◇ q0) ◇ q0)).symm)
  have apc1 : forall (q5 q6 q7 q8:G), (q8 ◇ (q5 ◇ q7)) = ((q5 ◇ q6) ◇ q8):=by
    intro q5 q6 q7 q8
    exact ((congrArg (fun t => q8 ◇ t) ((h q5 q7 q6 q5 q5).symm)).symm).trans (apc0 q7 q5 (q5 ◇ q6) q8 q5)
  have apc2 : forall (q9 q10 q11 q12:G), ((q10 ◇ q11) ◇ q12) = ((q10 ◇ q9) ◇ q12):=by
    intro q9 q10 q11 q12
    exact (((apc1 q10 q9 q9 q12).symm).trans (apc1 q10 q11 q9 q12)).symm
  have apc3 : forall (q13 q14 q15 q16:G), ((q15 ◇ q14) ◇ q16) = ((q13 ◇ q15) ◇ q16):=by
    intro q13 q14 q15 q16
    exact (((congrArg (fun t => t ◇ q16) ((h q13 q15 q13 q13 q13).symm)).symm).trans (apc2 q14 q15 (((q13 ◇ q13) ◇ q13) ◇ q13) q16)).symm
  have apc4 : forall (q5 q6 q7 q8:G), ((q5 ◇ q6) ◇ q8) = ((q5 ◇ q5) ◇ q8):=by
    intro q5 q6 q7 q8
    exact ((apc1 q5 q6 q7 q8).symm).trans (apc1 q5 q5 q7 q8)
  have apc6 : forall (q17 q18 q19 q20 q21:G), ((q20 ◇ q17) ◇ q21) = ((q19 ◇ q18) ◇ q21):=by
    intro q17 q18 q19 q20 q21
    exact (apc3 q19 q17 q20 q21).trans (apc2 q18 q19 q20 q21)
  have apc9 : forall (q22 q23 q24 q25:G), (q24 ◇ (q22 ◇ q23)) = ((q23 ◇ q23) ◇ q24):=by
    intro q22 q23 q24 q25
    exact (((congrArg (fun t => q24 ◇ t) ((h q22 q23 q22 q22 q22).symm)).symm).trans (apc1 q23 q25 (((q22 ◇ q22) ◇ q22) ◇ q22) q24)).trans (apc4 q23 q25 ((q23 ◇ q25) ◇ q24) q24)
  have apc10 : forall (q26 q2 q3 q4 q0:G), ((q26 ◇ q26) ◇ q3) = (q2 ◇ q3):=by
    intro q26 q2 q3 q4 q0
    exact (((congrArg (fun t => q3 ◇ t) (congrArg (fun t => t ◇ q26) (apc9 q2 q4 q0 (q0 ◇ (q2 ◇ q4))))).trans (apc9 ((q4 ◇ q4) ◇ q0) q26 q3 (q3 ◇ (((q4 ◇ q4) ◇ q0) ◇ q26)))).symm).trans (((congrArg (fun t => q3 ◇ t) (congrArg (fun t => t ◇ q26) ((h q0 (q2 ◇ q4) q0 q0 q0).symm))).symm).trans ((h q2 q3 q4 (((q0 ◇ q0) ◇ q0) ◇ q0) q26).symm))
  have apc11 : forall (q27 q28 q29 q30:G), ((q27 ◇ q27) ◇ (q29 ◇ q29)) = ((q29 ◇ q29) ◇ q28):=by
    intro q27 q28 q29 q30
    exact (((apc9 q30 q29 q28 (q28 ◇ (q30 ◇ q29))).symm).trans ((((apc10 q27 q28 (q30 ◇ q29) q27 q27).symm).trans (apc9 q30 q29 (q27 ◇ q27) q27)).trans (apc9 q27 q27 (q29 ◇ q29) ((q29 ◇ q29) ◇ (q27 ◇ q27))))).symm
  have apc13 : forall (q31 q32 q33 q34 q35:G), ((q31 ◇ q31) ◇ (q32 ◇ q32)) = ((q34 ◇ q33) ◇ q35):=by
    intro q31 q32 q33 q34 q35
    exact (apc11 q31 q35 q32 q31).trans (apc6 q32 q33 q34 q32 q35)
  exact ((apc13 ((x ◇ y) ◇ x) ((z ◇ y) ◇ (z ◇ y)) y x x).symm).trans (apc13 ((x ◇ y) ◇ x) ((z ◇ y) ◇ (z ◇ y)) y z (z ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_45427_to_60249 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_45427_to_60249
