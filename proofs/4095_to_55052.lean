-- Equation4095 → Equation55052
-- Recorded verdict: true
-- Premise: x ◇ x = ((y ◇ y) ◇ y) ◇ z
-- Conclusion: x ◇ (y ◇ y) = x ◇ ((y ◇ y) ◇ y)
-- Original submission SHA-256: baee2e3b8fb71fb5d2ba0a25ab42fad7c33aa6605e843229589eee382dc10a5b
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = ((y ◇ y) ◇ y) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ (y ◇ y) = x ◇ ((y ◇ y) ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   

set_option linter.unusedVariables false
set_option maxHeartbeats 400000
set_option maxRecDepth 100000

def submission : Goal := by
  intro G _ h
  intro x y
  have e0 : ∀ (X1 X2 X3 : G), (X1 ◇ X1) = (((X2 ◇ X2) ◇ X2) ◇ X3) := by
      intro X1 X2 X3
      calc (X1 ◇ X1)
        _ = (((X2 ◇ X2) ◇ X2) ◇ X3) := h X1 X2 X3
  have e1 : ∀ (X1 X4 : G), (X1 ◇ X1) = (X4 ◇ X4) := by
      intro X1 X4
      calc (X1 ◇ X1)
        _ = (((X1 ◇ X1) ◇ X1) ◇ X1) := h X1 X1 X1
        _ = (X4 ◇ X4) := (h X4 X1 X1).symm
  have e2 : ∀ (X1 X4 X2 X3 : G), (X1 ◇ X1) = (((X4 ◇ X4) ◇ X2) ◇ X3) := by
      intro X1 X4 X2 X3
      calc (X1 ◇ X1)
        _ = (((X2 ◇ X2) ◇ X2) ◇ X3) := h X1 X2 X3
        _ = (((X4 ◇ X4) ◇ X2) ◇ X3) := congrArg (· ◇ X3) (congrArg (· ◇ X2) ((e1 X4 X2).symm))
  have gx : ∀ (X0 X1 X2 X3 : G), ((X0 ◇ X0) ◇ X1) = (X2 ◇ X2) := by
      intro X0 X1 X2 X3
      calc ((X0 ◇ X0) ◇ X1)
        _ = ((((X3 ◇ X3) ◇ (X3 ◇ X3)) ◇ (X3 ◇ X3)) ◇ X1) := congrArg (· ◇ X1) (((e2 X0 X3 ((X3 ◇ X3)) ((X3 ◇ X3))).symm).symm)
        _ = (X2 ◇ X2) := (h X2 ((X3 ◇ X3)) X1).symm
  calc (x ◇ (y ◇ y))
    _ = (x ◇ (x ◇ x)) := congrArg (x ◇ ·) (e1 y x)
    _ = (x ◇ ((y ◇ y) ◇ y)) := congrArg (x ◇ ·) ((gx y y x x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_4095_to_55052 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_4095_to_55052
