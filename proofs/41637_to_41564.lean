-- Equation41637 → Equation41564
-- Recorded verdict: true
-- Premise: x ◇ x = y ◇ (y ◇ (y ◇ (z ◇ w)))
-- Conclusion: x ◇ x = x ◇ (y ◇ (z ◇ (x ◇ x)))
-- Original submission SHA-256: c0a4711034fe053c724714c763196334e41a888170a1bab2dd222b326ad24c25
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ x = y ◇ (y ◇ (y ◇ (z ◇ w)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = x ◇ (y ◇ (z ◇ (x ◇ x)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   

set_option linter.unusedVariables false
set_option maxHeartbeats 400000
set_option maxRecDepth 100000

def submission : Goal := by
  intro G _ h
  intro x y z
  have e0 : ∀ (X1 X2 X3 X4 : G), (X1 ◇ X1) = (X2 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4)))) := by
      intro X1 X2 X3 X4
      calc (X1 ◇ X1)
        _ = (X2 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4)))) := ((h X1 X2 X3 X4).symm).symm
  have e1 : ∀ (X1 X5 : G), (X1 ◇ X1) = (X5 ◇ X5) := by
      intro X1 X5
      calc (X1 ◇ X1)
        _ = (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) := ((h X1 X1 X1 X1).symm).symm
        _ = (X5 ◇ X5) := (h X5 X1 X1 X1).symm
  have e2 : ∀ (X1 X2 X5 : G), (X1 ◇ X1) = (X2 ◇ (X5 ◇ X5)) := by
      intro X1 X2 X5
      calc (X1 ◇ X1)
        _ = (X2 ◇ (X2 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X1))))) := ((h X1 X2 X2 ((X1 ◇ X1))).symm).symm
        _ = (X2 ◇ (X5 ◇ X5)) := congrArg (X2 ◇ ·) ((h X5 X2 X1 X1).symm)
  calc (x ◇ x)
    _ = (x ◇ (x ◇ x)) := e2 x x x
    _ = (x ◇ (y ◇ (x ◇ x))) := congrArg (x ◇ ·) (e2 x y x)
    _ = (x ◇ (y ◇ (z ◇ (x ◇ x)))) := congrArg (x ◇ ·) (congrArg (y ◇ ·) (((e2 x z x).symm).symm))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_41637_to_41564 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_41637_to_41564
