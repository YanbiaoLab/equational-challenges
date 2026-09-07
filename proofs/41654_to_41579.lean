-- Equation41654 → Equation41579
-- Recorded verdict: true
-- Premise: x ◇ x = y ◇ (y ◇ (z ◇ (w ◇ u)))
-- Conclusion: x ◇ x = x ◇ (y ◇ (z ◇ (w ◇ w)))
-- Original submission SHA-256: 83f218f778e800a857703c5f397ef72c908c052b93107f15369f6ca0c16ba038
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ x = y ◇ (y ◇ (z ◇ (w ◇ u)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ x = x ◇ (y ◇ (z ◇ (w ◇ w)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   

set_option linter.unusedVariables false
set_option maxHeartbeats 400000
set_option maxRecDepth 100000

def submission : Goal := by
  intro G _ h
  intro x y z w
  have f7 : ∀ (X2 X3 X0 X1 X4 : G), (X2 ◇ X2) = (X3 ◇ (X3 ◇ (X4 ◇ (X1 ◇ X0)))) := by
    intro X2 X3 X0 X1 X4
    exact h X2 X3 X4 X1 X0
  have f25 : ∀ (X2 X0 X1 : G), (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X2 X0 X1
    calc (X1 ◇ X1)
      _ = (X2 ◇ (X2 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2))))) := ((f7 X1 X2 ((X2 ◇ X2)) X2 X2).symm).symm
      _ = (X2 ◇ (X0 ◇ X0)) := congrArg (X2 ◇ ·) ((f7 X0 X2 X2 X2 X2).symm)
  calc (x ◇ x)
    _ = (x ◇ (x ◇ x)) := f25 x x x
    _ = (x ◇ (y ◇ (x ◇ x))) := congrArg (x ◇ ·) (f25 y x x)
    _ = (x ◇ (y ◇ (z ◇ (w ◇ w)))) := congrArg (x ◇ ·) (congrArg (y ◇ ·) (((f25 z w x).symm).symm))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_41654_to_41579 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_41654_to_41579
