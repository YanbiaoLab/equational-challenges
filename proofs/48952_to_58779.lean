-- Equation48952 → Equation58779
-- Recorded verdict: true
-- Premise: x * y = ((y * y) * y) * (z * x)
-- Conclusion: (x * y) * z = y * (x * (y * y))
-- Original submission SHA-256: a0ade76b03982936df9ceb6a879f744ceda042517530972115f65556e3af737b
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = ((y ◇ y) ◇ y) ◇ (z ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ z = y ◇ (x ◇ (y ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3:G), (((q3 ◇ q3) ◇ q3) ◇ (q0 ◇ q1)) = ((q2 ◇ q0) ◇ q3):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => ((q3 ◇ q3) ◇ q3) ◇ t) ((h q0 q1 q2).symm)).symm).trans ((h (q2 ◇ q0) q3 ((q1 ◇ q1) ◇ q1)).symm)
  have apc1 : forall (q4 q5 q6 q7:G), ((q4 ◇ q7) ◇ q6) = (q5 ◇ q6):=by
    intro q4 q5 q6 q7
    exact ((apc0 q7 q5 q4 q6).symm).trans ((h q5 q6 q7).symm)
  have apc3 : forall (q8 q9 q10 q11:G), (q8 ◇ (q11 ◇ q9)) = (q9 ◇ q10):=by
    intro q8 q9 q10 q11
    exact ((apc1 (q10 ◇ q10) q8 (q11 ◇ q9) q10).symm).trans ((h q9 q10 q11).symm)
  have apc4 : forall (q8 q9 q10 q11:G), (q9 ◇ q10) = (q9 ◇ q8):=by
    intro q8 q9 q10 q11
    exact ((apc3 q8 q9 q10 q11).symm).trans (apc3 q8 q9 q8 q11)
  have apc6 : forall (q12 q13 q14 q15:G), (q14 ◇ q15) = (q13 ◇ q12):=by
    intro q12 q13 q14 q15
    exact (((apc4 q12 q13 (q12 ◇ q14) q12).symm).trans (apc3 q13 q14 q15 q12)).symm
  exact (apc6 ((x ◇ y) ◇ z) (y ◇ (x ◇ (y ◇ y))) (x ◇ y) z).trans ((apc6 ((x ◇ y) ◇ z) (y ◇ (x ◇ (y ◇ y))) y (x ◇ (y ◇ y))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_48952_to_58779 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_48952_to_58779
