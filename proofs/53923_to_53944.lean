-- Equation53923 → Equation53944
-- Recorded verdict: true
-- Premise: x ◇ (x ◇ y) = y ◇ (z ◇ (y ◇ w))
-- Conclusion: x ◇ (x ◇ y) = z ◇ (x ◇ (z ◇ w))
-- Original submission SHA-256: 1cbeb5cfff0628b7aabd048e0b662eab170908213af93e5046b420c5e2b7189a
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (x ◇ y) = y ◇ (z ◇ (y ◇ w))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (x ◇ y) = z ◇ (x ◇ (z ◇ w))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   

set_option linter.unusedVariables false
set_option maxHeartbeats 400000
set_option maxRecDepth 100000

def submission : Goal := by
  intro G _ h
  intro x y z w
  have e0 : ∀ (X1 X2 X3 X4 : G), (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (X3 ◇ (X2 ◇ X4))) := by
      intro X1 X2 X3 X4
      calc (X1 ◇ (X1 ◇ X2))
        _ = (X2 ◇ (X3 ◇ (X2 ◇ X4))) := h X1 X2 X3 X4
  have e1 : ∀ (X1 X2 X5 : G), (X1 ◇ (X1 ◇ X2)) = (X5 ◇ (X5 ◇ X2)) := by
      intro X1 X2 X5
      calc (X1 ◇ (X1 ◇ X2))
        _ = (X2 ◇ (X1 ◇ (X2 ◇ X1))) := h X1 X2 X1 X1
        _ = (X5 ◇ (X5 ◇ X2)) := (h X5 X2 X1 X1).symm
  have e2 : ∀ (X1 X2 X5 X3 : G), (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (X5 ◇ (X5 ◇ X3))) := by
      intro X1 X2 X5 X3
      calc (X1 ◇ (X1 ◇ X2))
        _ = (X2 ◇ (X2 ◇ (X2 ◇ X3))) := h X1 X2 X2 X3
        _ = (X2 ◇ (X5 ◇ (X5 ◇ X3))) := congrArg (X2 ◇ ·) ((e1 X5 X3 X2).symm)
  have e3 : ∀ (X1 X2 X4 X3 : G), (X1 ◇ (X1 ◇ X2)) = (X4 ◇ (X4 ◇ (X2 ◇ X3))) := by
      intro X1 X2 X4 X3
      calc (X1 ◇ (X1 ◇ X2))
        _ = (X2 ◇ (X2 ◇ (X2 ◇ X3))) := h X1 X2 X2 X3
        _ = (X4 ◇ (X4 ◇ (X2 ◇ X3))) := (e1 X4 ((X2 ◇ X3)) X2).symm
  have e4 : ∀ (X1 X2 X3 X5 : G), (X1 ◇ (X1 ◇ X2)) = (X3 ◇ (X5 ◇ (X5 ◇ X3))) := by
      intro X1 X2 X3 X5
      calc (X1 ◇ (X1 ◇ X2))
        _ = (X2 ◇ (X2 ◇ (X2 ◇ X3))) := h X1 X2 X2 X3
        _ = (X2 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X1)))) := congrArg (X2 ◇ ·) (e3 X2 X3 X2 X1)
        _ = (X3 ◇ (X3 ◇ (X2 ◇ (X3 ◇ X1)))) := (e1 X3 ((X2 ◇ (X3 ◇ X1))) X2).symm
        _ = (X3 ◇ (X5 ◇ (X5 ◇ X3))) := congrArg (X3 ◇ ·) ((h X5 X3 X2 X1).symm)
  calc (x ◇ (x ◇ y))
    _ = (y ◇ (y ◇ (y ◇ y))) := h x y y y
    _ = (x ◇ (x ◇ z)) := (e4 x z y y).symm
    _ = (z ◇ (x ◇ (z ◇ w))) := ((h x z x w).symm).symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_53923_to_53944 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_53923_to_53944
