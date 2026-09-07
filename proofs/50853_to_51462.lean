-- Equation50853 → Equation51462
-- Recorded verdict: true
-- Premise: x * y = (z * ((x * z) * w)) * w
-- Conclusion: x * y = ((x * z) * (x * z)) * y
-- Original submission SHA-256: 2a5234e5d3528b4921a9ec2636b21d202ba4af0e8b7224faca9e83061399ac31
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ ((x ◇ z) ◇ w)) ◇ w
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = ((x ◇ z) ◇ (x ◇ z)) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2:G), (q1 ◇ q2) = (q1 ◇ q0):=by
    intro q0 q1 q2
    exact ((h q1 q0 q0 q0).trans ((h q1 q2 q0 q0).symm)).symm
  have apc1 : forall (x y z w:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w
    exact (h x y z w).trans ((h x x z w).symm)
  have apc2 : forall (q3 q4 q5 q6 q7:G), ((q6 ◇ q3) ◇ q4) = (q5 ◇ q5):=by
    intro q3 q4 q5 q6 q7
    exact (((congrArg (fun t => t ◇ q4) (apc0 q3 q6 ((q5 ◇ q6) ◇ q4))).symm).trans ((h q5 q7 q6 q4).symm)).trans (apc1 q5 q7 (q5 ◇ q7) (q5 ◇ q7))
  have apc6 : forall (q8 q9 q10 q11 q12 q13:G), ((q10 ◇ q10) ◇ q8) = (q10 ◇ q9):=by
    intro q8 q9 q10 q11 q12 q13
    exact ((congrArg (fun t => t ◇ q8) (apc1 q10 (((q11 ◇ q12) ◇ q13) ◇ q8) (q10 ◇ (((q11 ◇ q12) ◇ q13) ◇ q8)) (q10 ◇ (((q11 ◇ q12) ◇ q13) ◇ q8)))).symm).trans (((congrArg (fun t => t ◇ q8) (congrArg (fun t => q10 ◇ t) (congrArg (fun t => t ◇ q8) ((apc2 q12 q13 q10 q11 q12).symm)))).symm).trans ((h q10 q9 q10 q8).symm))
  have apc7 : forall (q14 q15 q16:G), (q16 ◇ q16) = (q15 ◇ q14):=by
    intro q14 q15 q16
    exact (((apc6 q14 q14 q15 q14 q14 q14).symm).trans (apc2 q15 q14 q16 q15 q14)).symm
  exact ((apc7 y x (x ◇ y)).symm).trans (apc7 y ((x ◇ z) ◇ (x ◇ z)) (x ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_50853_to_51462 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_50853_to_51462
