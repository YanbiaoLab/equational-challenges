-- Equation51659 → Equation62058
-- Recorded verdict: true
-- Premise: x * y = ((y * z) * (w * x)) * u
-- Conclusion: (x * y) * y = ((x * x) * y) * y
-- Original submission SHA-256: 70181ea49d0eb89cb772a0b6545df322ccbf6e8e1b85f1740c6f73baa1acb766
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = ((y ◇ z) ◇ (w ◇ x)) ◇ u
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), (x ◇ y) ◇ y = ((x ◇ x) ◇ y) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (q0 q1 q2 q3 q4 q5:G), (((q4 ◇ q5) ◇ (q0 ◇ q1)) ◇ q2) = (q3 ◇ q4):=by
    intro q0 q1 q2 q3 q4 q5
    exact ((congrArg (fun t => t ◇ q2) (congrArg (fun t => (q4 ◇ q5) ◇ t) ((h q0 q1 q0 q0 q3).symm))).symm).trans ((h q3 q4 q5 ((q1 ◇ q0) ◇ (q0 ◇ q0)) q2).symm)
  have apc1 : forall (q0 q1 q2 q3 q4 q5:G), (q3 ◇ q4) = (q0 ◇ q4):=by
    intro q0 q1 q2 q3 q4 q5
    exact ((apc0 q0 q1 q2 q3 q4 q5).symm).trans (apc0 q0 q1 q2 q0 q4 q5)
  exact (apc1 ((x ◇ y) ◇ y) ((x ◇ y) ◇ y) ((x ◇ y) ◇ y) (x ◇ y) y ((x ◇ y) ◇ y)).trans ((apc1 ((x ◇ y) ◇ y) ((x ◇ y) ◇ y) ((x ◇ y) ◇ y) ((x ◇ x) ◇ y) y ((x ◇ y) ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_51659_to_62058 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_51659_to_62058
