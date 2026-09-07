-- Equation3501 → Equation43455
-- Recorded verdict: true
-- Premise: x ◇ x = y ◇ ((z ◇ z) ◇ z)
-- Conclusion: x ◇ x = y ◇ ((z ◇ z) ◇ (w ◇ x))
-- Original submission SHA-256: b1a3aaf4c03a091b8b7e1616d1149235aa5199af1f8c5956ebef0c0d08d81045
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = y ◇ ((z ◇ z) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ x = y ◇ ((z ◇ z) ◇ (w ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   

set_option linter.unusedVariables false
set_option maxHeartbeats 400000
set_option maxRecDepth 100000

def submission : Goal := by
  intro G _ h
  intro x y z w
  have f7 : ∀ (X2 X0 X1 : G), (X0 ◇ X0) = (X1 ◇ ((X2 ◇ X2) ◇ X2)) := by
    intro X2 X0 X1
    exact h X0 X1 X2
  have f22 : ∀ (X0 X1 : G), (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    calc (X0 ◇ X0)
      _ = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := ((f7 X0 X0 X0).symm).symm
      _ = (X1 ◇ X1) := (f7 X0 X1 X0).symm
  have f41 : ∀ (X2 X3 X0 X1 : G), (X1 ◇ X1) = (X2 ◇ ((X0 ◇ X0) ◇ X3)) := by
    intro X2 X3 X0 X1
    calc (X1 ◇ X1)
      _ = (X2 ◇ ((X3 ◇ X3) ◇ X3)) := ((f7 X3 X1 X2).symm).symm
      _ = (X2 ◇ ((X0 ◇ X0) ◇ X3)) := congrArg (X2 ◇ ·) (congrArg (· ◇ X3) (f22 X3 X0))
  calc (x ◇ x)
    _ = (y ◇ ((z ◇ z) ◇ (w ◇ x))) := ((f41 y ((w ◇ x)) z x).symm).symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_3501_to_43455 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_3501_to_43455
