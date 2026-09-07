-- Equation43735 → Equation55735
-- Recorded verdict: true
-- Premise: x * y = y * ((z * y) * (y * w))
-- Conclusion: x * (x * y) = (z * z) * (w * z)
-- Original submission SHA-256: 764f22b2d8c2f8abb211191d7c560930c437048c46ab74a349f163d6ce7cef54
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = y ◇ ((z ◇ y) ◇ (y ◇ w))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (x ◇ y) = (z ◇ z) ◇ (w ◇ z)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2:G), (q1 ◇ q2) = (q0 ◇ q2):=by
    intro q0 q1 q2
    exact ((h q0 q2 q0 q0).trans ((h q1 q2 q0 q0).symm)).symm
  have apc2 : forall (q3 q4 q5 q6:G), (q6 ◇ (q3 ◇ (q6 ◇ q4))) = (q5 ◇ q6):=by
    intro q3 q4 q5 q6
    exact ((congrArg (fun t => q6 ◇ t) (apc0 q3 (q3 ◇ q6) (q6 ◇ q4))).symm).trans ((h q5 q6 q3 q4).symm)
  have apc3 : forall (q7 q8 q9 q10:G), (q10 ◇ (q7 ◇ q8)) = (q9 ◇ q10):=by
    intro q7 q8 q9 q10
    exact ((congrArg (fun t => q10 ◇ t) (apc2 q10 q7 q7 q8)).symm).trans (apc2 q8 (q8 ◇ q7) q9 q10)
  have apc4 : forall (q11 q12 q13 q14 q15:G), (q14 ◇ (q11 ◇ q12)) = (q13 ◇ q15):=by
    intro q11 q12 q13 q14 q15
    exact (((apc3 q11 q12 q13 q15).symm).trans (apc0 q14 q15 (q11 ◇ q12))).symm
  exact (apc4 x y (x ◇ (x ◇ y)) x ((z ◇ z) ◇ (w ◇ z))).trans ((apc4 w z (x ◇ (x ◇ y)) (z ◇ z) ((z ◇ z) ◇ (w ◇ z))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_43735_to_55735 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_43735_to_55735
