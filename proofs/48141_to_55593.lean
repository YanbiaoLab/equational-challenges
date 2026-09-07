-- Equation48141 → Equation55593
-- Recorded verdict: true
-- Premise: x * y = (y * (z * z)) * (z * w)
-- Conclusion: x * (x * x) = (y * y) * (z * y)
-- Original submission SHA-256: af3a1b89b81064f8e87cbafe8a9f6e061b223128709d4a465f3cfcca8a9a0a34
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (y ◇ (z ◇ z)) ◇ (z ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (x ◇ x) = (y ◇ y) ◇ (z ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3 q4:G), (q3 ◇ (q1 ◇ (q4 ◇ q4))) = ((q0 ◇ q1) ◇ (q4 ◇ q2)):=by
    intro q0 q1 q2 q3 q4
    exact (((congrArg (fun t => t ◇ (q4 ◇ q2)) ((h q0 q1 q4 q4).symm)).symm).trans ((h q3 (q1 ◇ (q4 ◇ q4)) q4 q2).symm)).symm
  have apc1 : forall (q5 q6 q7 q8 q9 q10:G), ((q5 ◇ q10) ◇ (q7 ◇ q6)) = (q8 ◇ q9):=by
    intro q5 q6 q7 q8 q9 q10
    exact ((apc0 q5 q10 q6 (q9 ◇ (q10 ◇ q10)) q7).symm).trans ((h q8 q9 q10 (q7 ◇ q7)).symm)
  have apc2 : forall (q11 q12 q13 q14 q15 q16 q17:G), ((q12 ◇ q13) ◇ (q17 ◇ q15)) = (q16 ◇ (q11 ◇ q14)):=by
    intro q11 q12 q13 q14 q15 q16 q17
    exact ((congrArg (fun t => t ◇ (q17 ◇ q15)) (apc1 q11 q17 q17 q12 q13 q14)).symm).trans ((h q16 (q11 ◇ q14) q17 q15).symm)
  have apc3 : forall (q11 q12 q13 q14 q15 q16 q17:G), (q16 ◇ (q11 ◇ q14)) = (q12 ◇ (q12 ◇ q12)):=by
    intro q11 q12 q13 q14 q15 q16 q17
    exact ((apc2 q11 q12 q13 q14 q15 q16 q17).symm).trans (apc2 q12 q12 q13 q12 q15 q12 q17)
  exact (apc3 x (x ◇ (x ◇ x)) (x ◇ (x ◇ x)) x (x ◇ (x ◇ x)) x (x ◇ (x ◇ x))).trans ((apc3 z (x ◇ (x ◇ x)) (x ◇ (x ◇ x)) y (x ◇ (x ◇ x)) (y ◇ y) (x ◇ (x ◇ x))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_48141_to_55593 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_48141_to_55593
