-- Equation317 → Equation41572
-- Recorded verdict: true
-- Premise: x ◇ x = y ◇ (y ◇ z)
-- Conclusion: x ◇ x = x ◇ (y ◇ (z ◇ (z ◇ x)))
-- Original submission SHA-256: 15b764e2aad297e2af8b072eb214f464270c296f0ff5a93f2482c6d843b7e136
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = y ◇ (y ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = x ◇ (y ◇ (z ◇ (z ◇ x)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   

set_option linter.unusedVariables false
set_option maxHeartbeats 400000
set_option maxRecDepth 100000

def submission : Goal := by
  intro G _ h
  intro x y z
  have f7 : ∀ (X2 X0 X1 : G), (X0 ◇ X0) = (X1 ◇ (X1 ◇ X2)) := by
    intro X2 X0 X1
    exact h X0 X1 X2
  calc (x ◇ x)
    _ = (x ◇ (x ◇ x)) := h x x x
    _ = (x ◇ (y ◇ (y ◇ y))) := congrArg (x ◇ ·) (h x y y)
    _ = (x ◇ (y ◇ (z ◇ (z ◇ x)))) := congrArg (x ◇ ·) (congrArg (y ◇ ·) (((h y z x).symm).symm))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_317_to_41572 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_317_to_41572
