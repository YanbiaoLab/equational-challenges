-- Equation51864 → Equation41722
-- Recorded verdict: true
-- Premise: x * y = ((z * z) * (y * w)) * x
-- Conclusion: x * x = y * (z * (w * (w * y)))
-- Original submission SHA-256: aecb679e9ab49626f91bc788d146a52d85f9eecd88992b6ad0ad7c5eea5a8d2b
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((z ◇ z) ◇ (y ◇ w)) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ x = y ◇ (z ◇ (w ◇ (w ◇ y)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3:G), (((q3 ◇ q1) ◇ q0) ◇ q2) = (q2 ◇ q3):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => t ◇ q2) ((h (q3 ◇ q1) q0 q0 q0).symm)).symm).trans ((h q2 q3 (q0 ◇ q0) q1).symm)
  have apc1 : forall (q4 q5 q6:G), (q4 ◇ q6) = (q4 ◇ q5):=by
    intro q4 q5 q6
    exact ((apc0 (q5 ◇ q4) q6 q4 q6).symm).trans ((h q4 q5 q6 q4).symm)
  have apc2 : forall (q4 q5 q6:G), (q4 ◇ q5) = (q4 ◇ q4):=by
    intro q4 q5 q6
    exact ((apc1 q4 q5 q6).symm).trans (apc1 q4 q4 q6)
  have apc3 : forall (q7 q8 q9 q10 q11:G), (((q11 ◇ q9) ◇ q8) ◇ q7) = (q10 ◇ q10):=by
    intro q7 q8 q9 q10 q11
    exact (((apc1 ((q11 ◇ q9) ◇ q8) q7 q10).symm).trans (apc0 q8 q9 q10 q11)).trans (apc2 q10 q11 (q10 ◇ q11))
  have apc6 : forall (q12 q13 q14:G), (q14 ◇ q14) = (q13 ◇ q12):=by
    intro q12 q13 q14
    exact ((h q13 q12 q12 q12).trans (apc3 q13 (q12 ◇ q12) q12 q14 q12)).symm
  exact (apc6 (x ◇ x) (x ◇ x) x).trans (apc6 (z ◇ (w ◇ (w ◇ y))) y (x ◇ x))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_51864_to_41722 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_51864_to_41722
