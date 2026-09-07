-- Equation3479 → Equation55073
-- Recorded verdict: true
-- Premise: x ◇ x = y ◇ ((x ◇ z) ◇ z)
-- Conclusion: x ◇ (y ◇ y) = x ◇ ((z ◇ w) ◇ w)
-- Original submission SHA-256: 6c7542aebe0e43fbb856014fa7de4646551433b623d9624114aae35b18abf275
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = y ◇ ((x ◇ z) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ y) = x ◇ ((z ◇ w) ◇ w)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   

set_option linter.unusedVariables false
set_option maxHeartbeats 400000
set_option maxRecDepth 100000

def submission : Goal := by
  intro G _ h
  intro x y z w
  have e0 : ∀ (X1 X2 X3 : G), (X1 ◇ X1) = (X2 ◇ ((X1 ◇ X3) ◇ X3)) := by
      intro X1 X2 X3
      calc (X1 ◇ X1)
        _ = (X2 ◇ ((X1 ◇ X3) ◇ X3)) := h X1 X2 X3
  have e1 : ∀ (X1 X2 X3 : G), (X1 ◇ X1) = (X2 ◇ (X3 ◇ X3)) := by
      intro X1 X2 X3
      calc (X1 ◇ X1)
        _ = (X2 ◇ ((X1 ◇ ((X3 ◇ X1) ◇ X1)) ◇ ((X3 ◇ X1) ◇ X1))) := ((h X1 X2 (((X3 ◇ X1) ◇ X1))).symm).symm
        _ = (X2 ◇ (X3 ◇ X3)) := congrArg (X2 ◇ ·) ((h X3 ((X1 ◇ ((X3 ◇ X1) ◇ X1))) X1).symm)
  calc (x ◇ (y ◇ y))
    _ = (z ◇ z) := (e1 z x y).symm
    _ = (x ◇ ((z ◇ w) ◇ w)) := ((h z x w).symm).symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_3479_to_55073 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_3479_to_55073
