-- Equation50050 → Equation52988
-- Recorded verdict: true
-- Premise: x * y = (z * (y * (z * w))) * x
-- Conclusion: x * x = (((y * x) * x) * z) * x
-- Original submission SHA-256: f47c18cc0abfab45a846cc856960d9ddde87353059732e0e3c6fe59dece1f875
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ (y ◇ (z ◇ w))) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = (((y ◇ x) ◇ x) ◇ z) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3 q4 q5:G), (((q5 ◇ ((q2 ◇ (q1 ◇ (q2 ◇ q0))) ◇ q3)) ◇ q1) ◇ q4) = (q4 ◇ q5):=by
    intro q0 q1 q2 q3 q4 q5
    exact ((congrArg (fun t => t ◇ q4) ((h (q5 ◇ ((q2 ◇ (q1 ◇ (q2 ◇ q0))) ◇ q3)) q1 q2 q0).symm)).symm).trans ((h q4 q5 (q2 ◇ (q1 ◇ (q2 ◇ q0))) q3).symm)
  have apc1 : forall (q6 q7 q8 q9 q10 q11 q12 q13:G), (((q9 ◇ (q7 ◇ q6)) ◇ q6) ◇ q8) = (q8 ◇ q9):=by
    intro q6 q7 q8 q9 q10 q11 q12 q13
    exact ((congrArg (fun t => t ◇ q8) (congrArg (fun t => t ◇ q6) (congrArg (fun t => q9 ◇ t) (apc0 q10 q11 q12 q13 q7 q6)))).symm).trans (((congrArg (fun t => t ◇ q8) (apc0 q10 q11 q12 q13 (q9 ◇ (((q6 ◇ ((q12 ◇ (q11 ◇ (q12 ◇ q10))) ◇ q13)) ◇ q11) ◇ q7)) q6)).symm).trans ((h q8 q9 ((q6 ◇ ((q12 ◇ (q11 ◇ (q12 ◇ q10))) ◇ q13)) ◇ q11) q7).symm))
  have apc2 : forall (q14 q15 q16 q17:G), (((q17 ◇ q14) ◇ q15) ◇ q16) = (q16 ◇ q17):=by
    intro q14 q15 q16 q17
    exact ((congrArg (fun t => t ◇ q16) ((h (q17 ◇ q14) q15 q17 q14).symm)).symm).trans (apc1 (q17 ◇ q14) q15 q16 q17 q14 q14 q14 q14)
  have apc3 : forall (q18 q19 q20 q21:G), ((q19 ◇ q18) ◇ q20) = (q20 ◇ q21):=by
    intro q18 q19 q20 q21
    exact ((congrArg (fun t => t ◇ q20) ((h q19 q18 q21 q18).symm)).symm).trans (apc2 (q18 ◇ (q21 ◇ q18)) q19 q20 q21)
  have apc4 : forall (q22 q23 q24:G), (q23 ◇ q24) = (q23 ◇ q22):=by
    intro q22 q23 q24
    exact (((apc2 q22 (q24 ◇ ((q22 ◇ q22) ◇ q22)) q23 q22).symm).trans ((h q23 q24 (q22 ◇ q22) q22).symm)).symm
  have apc7 : forall (q22 q23 q24:G), (q23 ◇ q23) = (q23 ◇ q22):=by
    intro q22 q23 q24
    exact (((apc4 q22 q23 q24).symm).trans (apc4 q23 q23 q24)).symm
  have apc10 : forall (q25 q26 q27:G), ((q26 ◇ q25) ◇ q27) = (q27 ◇ q27):=by
    intro q25 q26 q27
    exact ((apc7 q25 q27 q25).trans ((apc3 q25 q26 q27 q25).symm)).symm
  exact (calc
    (x ◇ x) = (x ◇ x):=rfl
    _ = ((((y ◇ x) ◇ x) ◇ z) ◇ x):=(((congrArg (fun t => t ◇ x) (congrArg (fun t => t ◇ z) (apc10 x y x))).trans (congrArg (fun t => t ◇ x) (apc10 x x z))).trans (apc10 z z x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_50050_to_52988 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_50050_to_52988
