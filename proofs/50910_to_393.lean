-- Equation50910 → Equation393
-- Recorded verdict: true
-- Premise: x * y = (z * ((y * y) * w)) * x
-- Conclusion: x * y = (y * z) * w
-- Original submission SHA-256: 4dfd78c43c5a392a9915577e9253aedb8a56fa58c8eade23c53e666cbc6176eb
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ ((y ◇ y) ◇ w)) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (y ◇ z) ◇ w
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3:G), ((((q3 ◇ q3) ◇ q1) ◇ q0) ◇ q2) = (q2 ◇ q3):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => t ◇ q2) ((h ((q3 ◇ q3) ◇ q1) q0 q0 q0).symm)).symm).trans ((h q2 q3 (q0 ◇ ((q0 ◇ q0) ◇ q0)) q1).symm)
  have apc1 : forall (q4 q5 q6 q7:G), ((q5 ◇ q4) ◇ q6) = (q6 ◇ q7):=by
    intro q4 q5 q6 q7
    exact ((congrArg (fun t => t ◇ q6) ((h q5 q4 (q7 ◇ q7) q4).symm)).symm).trans (apc0 q5 ((q4 ◇ q4) ◇ q4) q6 q7)
  have apc2 : forall (q8 q9 q10:G), (q9 ◇ q10) = (q9 ◇ q8):=by
    intro q8 q9 q10
    exact (((apc0 ((q10 ◇ q10) ◇ q8) q8 q9 q8).symm).trans ((h q9 q10 ((q8 ◇ q8) ◇ q8) q8).symm)).symm
  have apc4 : forall (q8 q9 q10:G), (q9 ◇ q9) = (q9 ◇ q8):=by
    intro q8 q9 q10
    exact (((apc2 q8 q9 q10).symm).trans (apc2 q9 q9 q10)).symm
  have apc6 : forall (q11 q12 q13:G), ((q12 ◇ q11) ◇ q13) = (q13 ◇ q13):=by
    intro q11 q12 q13
    exact ((apc4 q11 q13 q11).trans ((apc1 q11 q12 q13 q11).symm)).symm
  have apc7 : forall (q14 q15 q16 q17 q18:G), (q15 ◇ q16) = (q14 ◇ q14):=by
    intro q14 q15 q16 q17 q18
    exact (((((congrArg (fun t => t ◇ q14) (congrArg (fun t => t ◇ q17) (apc6 q16 q16 q18))).trans (congrArg (fun t => t ◇ q14) (apc6 q18 q18 q17))).trans (apc6 q17 q17 q14)).symm).trans (((apc2 q14 (((q16 ◇ q16) ◇ q18) ◇ q17) q15).symm).trans (apc0 q17 q18 q15 q16))).symm
  exact (apc7 (x ◇ y) x y (x ◇ y) (x ◇ y)).trans ((apc7 (x ◇ y) (y ◇ z) w (x ◇ y) (x ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_50910_to_393 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_50910_to_393
