-- Equation3289 → Equation41728
-- Recorded verdict: true
-- Premise: x ◇ x = y ◇ (z ◇ (x ◇ y))
-- Conclusion: x ◇ x = y ◇ (z ◇ (w ◇ (u ◇ z)))
-- Original submission SHA-256: 4262f1b72258e8a691af262984b9a0bf314a2c11b0ff0d849db817ce42cdb67b
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = y ◇ (z ◇ (x ◇ y))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ x = y ◇ (z ◇ (w ◇ (u ◇ z)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   

set_option linter.unusedVariables false
set_option maxHeartbeats 400000
set_option maxRecDepth 100000

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have e0 : ∀ (X1 X2 X3 : G), (X1 ◇ X1) = (X2 ◇ (X3 ◇ (X1 ◇ X2))) := by
      intro X1 X2 X3
      calc (X1 ◇ X1)
        _ = (X2 ◇ (X3 ◇ (X1 ◇ X2))) := h X1 X2 X3
  have e1 : ∀ (X1 X2 X3 : G), (X1 ◇ X1) = ((X2 ◇ X3) ◇ (X2 ◇ X2)) := by
      intro X1 X2 X3
      calc (X1 ◇ X1)
        _ = ((X2 ◇ X3) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X3)))) := ((h X1 ((X2 ◇ X3)) X3).symm).symm
        _ = ((X2 ◇ X3) ◇ (X2 ◇ X2)) := congrArg ((X2 ◇ X3) ◇ ·) ((h X2 X3 X1).symm)
  have e2 : ∀ (X1 X4 : G), (X1 ◇ X1) = (X4 ◇ X4) := by
      intro X1 X4
      calc (X1 ◇ X1)
        _ = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := e1 X1 X1 X1
        _ = (X4 ◇ X4) := (e1 X4 X1 X1).symm
  have gx : ∀ (X0 X1 X2 X3 X4 : G), ((X0 ◇ X1) ◇ (X0 ◇ X0)) = (X2 ◇ (X3 ◇ (X4 ◇ X2))) := by
      intro X0 X1 X2 X3 X4
      calc ((X0 ◇ X1) ◇ (X0 ◇ X0))
        _ = (X4 ◇ X4) := (e1 X4 X0 X1).symm
        _ = (X2 ◇ (X3 ◇ (X4 ◇ X2))) := h X4 X2 X3
  calc (x ◇ x)
    _ = (y ◇ y) := e2 x y
    _ = (y ◇ ((y ◇ x) ◇ (y ◇ y))) := ((h y y ((y ◇ x))).symm).symm
    _ = (y ◇ (z ◇ (w ◇ (u ◇ z)))) := congrArg (y ◇ ·) (((gx y x z w u).symm).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_3289_to_41728 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_3289_to_41728
