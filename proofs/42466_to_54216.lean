-- Equation42466 → Equation54216
-- Recorded verdict: true
-- Premise: x ◇ x = y ◇ (x ◇ ((x ◇ z) ◇ z))
-- Conclusion: x ◇ (y ◇ y) = y ◇ (y ◇ (z ◇ z))
-- Original submission SHA-256: 7c74d7c214686ead937bca467e36a55becc2e9bdc9169cfaa2a1b26d5bbcfe0b
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = y ◇ (x ◇ ((x ◇ z) ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ y) = y ◇ (y ◇ (z ◇ z))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   

set_option linter.unusedVariables false
set_option maxHeartbeats 400000
set_option maxRecDepth 100000

def submission : Goal := by
  intro G _ h
  intro x y z
  have e0 : ∀ (X2 X1 X3 : G), (X2 ◇ (X1 ◇ ((X1 ◇ X3) ◇ X3))) = (X1 ◇ X1) := by
      intro X2 X1 X3
      calc (X2 ◇ (X1 ◇ ((X1 ◇ X3) ◇ X3)))
        _ = (X1 ◇ X1) := (h X1 X2 X3).symm
  have e1 : ∀ (X1 X2 X3 : G), (X1 ◇ (X2 ◇ (X3 ◇ X3))) = (X2 ◇ X2) := by
      intro X1 X2 X3
      calc (X1 ◇ (X2 ◇ (X3 ◇ X3)))
        _ = (X1 ◇ (X2 ◇ ((X2 ◇ (X3 ◇ ((X3 ◇ X1) ◇ X1))) ◇ (X3 ◇ ((X3 ◇ X1) ◇ X1))))) := congrArg (X1 ◇ ·) (congrArg (X2 ◇ ·) (((h X3 ((X2 ◇ (X3 ◇ ((X3 ◇ X1) ◇ X1)))) X1).symm).symm))
        _ = (X2 ◇ X2) := (h X2 X1 ((X3 ◇ ((X3 ◇ X1) ◇ X1)))).symm
  have e2 : ∀ (X3 X2 : G), ((X3 ◇ X3) ◇ (X3 ◇ X3)) = (X2 ◇ X2) := by
      intro X3 X2
      calc ((X3 ◇ X3) ◇ (X3 ◇ X3))
        _ = (X3 ◇ ((X3 ◇ X3) ◇ (X3 ◇ X3))) := (e1 X3 ((X3 ◇ X3)) X3).symm
        _ = (X3 ◇ (X2 ◇ ((X3 ◇ X3) ◇ (X3 ◇ X3)))) := congrArg (X3 ◇ ·) ((e1 X2 ((X3 ◇ X3)) X3).symm)
        _ = (X2 ◇ X2) := e1 X3 X2 ((X3 ◇ X3))
  have e3 : ∀ (X3 X2 : G), (X3 ◇ X3) = (X2 ◇ X2) := by
      intro X3 X2
      calc (X3 ◇ X3)
        _ = ((X3 ◇ X3) ◇ (X3 ◇ X3)) := (e2 X3 X3).symm
        _ = (X2 ◇ X2) := ((e2 X3 X2).symm).symm
  calc (x ◇ (y ◇ y))
    _ = (x ◇ ((x ◇ x) ◇ (x ◇ x))) := congrArg (x ◇ ·) ((e2 x y).symm)
    _ = ((x ◇ x) ◇ (x ◇ x)) := e1 x ((x ◇ x)) x
    _ = (y ◇ y) := ((e2 x y).symm).symm
    _ = (y ◇ (y ◇ (z ◇ z))) := (e1 y y z).symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_42466_to_54216 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_42466_to_54216
