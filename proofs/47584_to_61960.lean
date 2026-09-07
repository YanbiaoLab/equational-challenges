-- Equation47584 → Equation61960
-- Recorded verdict: true
-- Premise: x * y = (z * w) * ((z * y) * x)
-- Conclusion: (x * y) * x = ((y * z) * x) * x
-- Original submission SHA-256: 128c9e35501f947ea82a56e987c3414cda56173fbb39ec9ef4b029a360fdd007
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ w) ◇ ((z ◇ y) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ x = ((y ◇ z) ◇ x) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3 q4:G), (((q4 ◇ q1) ◇ q0) ◇ q3) = ((q4 ◇ q2) ◇ (q0 ◇ q1)):=by
    intro q0 q1 q2 q3 q4
    exact (((congrArg (fun t => (q4 ◇ q2) ◇ t) ((h q0 q1 q4 q3).symm)).symm).trans ((h ((q4 ◇ q1) ◇ q0) q3 q4 q2).symm)).symm
  have apc1 : forall (q0 q1 q2 q3 q4:G), (((q4 ◇ q1) ◇ q0) ◇ q3) = (((q4 ◇ q1) ◇ q0) ◇ q0):=by
    intro q0 q1 q2 q3 q4
    exact (apc0 q0 q1 q2 q3 q4).trans ((apc0 q0 q1 q2 q0 q4).symm)
  have apc2 : forall (q5 q6 q7 q8 q9:G), (((q6 ◇ q5) ◇ q7) ◇ q7) = (q8 ◇ q9):=by
    intro q5 q6 q7 q8 q9
    exact ((apc1 q7 q5 q5 (((q6 ◇ q5) ◇ q9) ◇ q8) q6).symm).trans ((h q8 q9 (q6 ◇ q5) q7).symm)
  have apc3 : forall (q10 q11 q12 q13 q14 q15:G), (((q11 ◇ q10) ◇ q12) ◇ q12) = (q13 ◇ q13):=by
    intro q10 q11 q12 q13 q14 q15
    exact ((apc1 q12 q10 (((q11 ◇ q10) ◇ q12) ◇ (q14 ◇ q15)) (q14 ◇ q15) q11).symm).trans (((congrArg (fun t => ((q11 ◇ q10) ◇ q12) ◇ t) (apc2 q10 q11 q13 q14 q15)).symm).trans ((h q13 q13 (q11 ◇ q10) q12).symm))
  have apc4 : forall (q0 q1 q2 q3 q4:G), (((q4 ◇ q1) ◇ q0) ◇ q0) = ((q4 ◇ q2) ◇ (q0 ◇ q1)):=by
    intro q0 q1 q2 q3 q4
    exact ((apc1 q0 q1 (((q4 ◇ q1) ◇ q0) ◇ q3) q3 q4).symm).trans (apc0 q0 q1 q2 q3 q4)
  have apc6 : forall (q16 q17 q18 q19 q20 q21:G), (((q17 ◇ q16) ◇ q21) ◇ q21) = ((q18 ◇ q19) ◇ q20):=by
    intro q16 q17 q18 q19 q20 q21
    exact ((((congrArg (fun t => t ◇ q20) (apc2 q16 q17 q20 q18 q19)).symm).trans (apc4 q20 q20 q21 q16 (q17 ◇ q16))).trans (apc1 q21 q16 (((q17 ◇ q16) ◇ q21) ◇ (q20 ◇ q20)) (q20 ◇ q20) q17)).symm
  have apc8 : forall (q22 q23 q24 q25 q26:G), (((q22 ◇ q22) ◇ q26) ◇ q26) = ((q23 ◇ q24) ◇ q25):=by
    intro q22 q23 q24 q25 q26
    exact ((congrArg (fun t => t ◇ q26) (congrArg (fun t => t ◇ q26) (apc3 q22 q22 q22 q22 q22 q22))).symm).trans (apc6 q22 ((q22 ◇ q22) ◇ q22) q23 q24 q25 q26)
  exact ((apc8 ((x ◇ y) ◇ x) x y x (((y ◇ z) ◇ x) ◇ x)).symm).trans (apc8 ((x ◇ y) ◇ x) (y ◇ z) x x (((y ◇ z) ◇ x) ◇ x))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_47584_to_61960 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_47584_to_61960
