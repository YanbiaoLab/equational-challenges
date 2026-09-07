-- Equation3298 → Equation60941
-- Recorded verdict: true
-- Premise: x ◇ x = y ◇ (z ◇ (z ◇ z))
-- Conclusion: (x ◇ x) ◇ y = (y ◇ (z ◇ z)) ◇ y
-- Original submission SHA-256: 71e0a28d82443871d84006381eec53b173cddcedcddfc8b1fbe17f03558a64a0
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = y ◇ (z ◇ (z ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ x) ◇ y = (y ◇ (z ◇ z)) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   

set_option linter.unusedVariables false
set_option maxHeartbeats 400000
set_option maxRecDepth 100000

def submission : Goal := by
  intro G _ h
  intro x y z
  have e0 : ∀ (X1 X2 X3 : G), (X1 ◇ X1) = (X2 ◇ (X3 ◇ (X3 ◇ X3))) := by
      intro X1 X2 X3
      calc (X1 ◇ X1)
        _ = (X2 ◇ (X3 ◇ (X3 ◇ X3))) := h X1 X2 X3
  have e1 : ∀ (X1 X4 : G), (X1 ◇ X1) = (X4 ◇ X4) := by
      intro X1 X4
      calc (X1 ◇ X1)
        _ = (X1 ◇ (X1 ◇ (X1 ◇ X1))) := h X1 X1 X1
        _ = (X4 ◇ X4) := (h X4 X1 X1).symm
  have e2 : ∀ (X1 X2 X3 X4 : G), (X1 ◇ X1) = (X2 ◇ (X3 ◇ (X4 ◇ X4))) := by
      intro X1 X2 X3 X4
      calc (X1 ◇ X1)
        _ = (X2 ◇ (X3 ◇ (X3 ◇ X3))) := h X1 X2 X3
        _ = (X2 ◇ (X3 ◇ (X4 ◇ X4))) := congrArg (X2 ◇ ·) (congrArg (X3 ◇ ·) ((e1 X4 X3).symm))
  have gx : ∀ (X0 X1 X2 X3 : G), (X0 ◇ (X1 ◇ X1)) = (X2 ◇ X2) := by
      intro X0 X1 X2 X3
      calc (X0 ◇ (X1 ◇ X1))
        _ = (X0 ◇ ((X3 ◇ X3) ◇ ((X3 ◇ X3) ◇ (X3 ◇ X3)))) := congrArg (X0 ◇ ·) (((e2 X1 ((X3 ◇ X3)) ((X3 ◇ X3)) X3).symm).symm)
        _ = (X2 ◇ X2) := (h X2 X0 ((X3 ◇ X3))).symm
  calc ((x ◇ x) ◇ y)
    _ = ((y ◇ (z ◇ z)) ◇ y) := congrArg (· ◇ y) ((gx y z x x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_3298_to_60941 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_3298_to_60941
