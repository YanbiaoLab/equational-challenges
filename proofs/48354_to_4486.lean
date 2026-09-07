-- Equation48354 → Equation4486
-- Recorded verdict: true
-- Premise: x * y = (z * (z * y)) * (z * z)
-- Conclusion: x * (y * y) = (y * z) * y
-- Original submission SHA-256: 2b9cac3be22b7a631ea1c4e8e490ce06d2a1c9864ed0b5bf13def85b412ca041
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (z ◇ (z ◇ y)) ◇ (z ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ y) = (y ◇ z) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc1 : forall (q0 q1 q2:G), (q1 ◇ q2) = (q0 ◇ q2):=by
    intro q0 q1 q2
    exact ((h q0 q2 q0).trans ((h q1 q2 q0).symm)).symm
  have apc2 : forall (q3 q4 q5 q6:G), (q3 ◇ (q6 ◇ q6)) = (q4 ◇ q5):=by
    intro q3 q4 q5 q6
    exact ((apc1 q3 (q6 ◇ (q6 ◇ q5)) (q6 ◇ q6)).symm).trans ((h q4 q5 q6).symm)
  have apc7 : forall (q3 q4 q5 q6:G), (q4 ◇ q5) = (q3 ◇ q3):=by
    intro q3 q4 q5 q6
    exact ((apc2 q3 q4 q5 q6).symm).trans (apc2 q3 q3 q3 q6)
  exact (apc7 (x ◇ (y ◇ y)) x (y ◇ y) (x ◇ (y ◇ y))).trans ((apc7 (x ◇ (y ◇ y)) (y ◇ z) y (x ◇ (y ◇ y))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_48354_to_4486 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_48354_to_4486
