-- Equation5775 → Equation4183
-- Recorded verdict: true
-- Premise: x = y ◇ (x ◇ (x ◇ ((x ◇ x) ◇ x)))
-- Conclusion: x ◇ y = ((y ◇ z) ◇ z) ◇ y
-- Original submission SHA-256: 41881ffc23465c32a392ead2e312ef880a27748ea72d5dc09778144f75ca21f2
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = y ◇ (x ◇ (x ◇ ((x ◇ x) ◇ x)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = ((y ◇ z) ◇ z) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   

set_option linter.unusedVariables false
set_option maxHeartbeats 400000
set_option maxRecDepth 100000

def submission : Goal := by
  intro G _ h
  intro x y z
  have f7 : ∀ (X0 X1 : G), (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = X0 := by
    intro X0 X1
    exact (h X0 X1).symm
  have f15 : ∀ (X0 X1 : G), (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = (X1 ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0))) := by
    intro X0 X1
    calc (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))
      _ = (X1 ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))))) := (f7 ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) X1).symm
      _ = (X1 ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0))) := congrArg (X1 ◇ ·) (congrArg ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ·) (congrArg ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ·) (f7 X0 (((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))))))
  have f22 : ∀ (X0 X1 : G), (((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0))))) = (X1 ◇ ((((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0))))) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) := by
    intro X0 X1
    calc (((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)))))
      _ = (X1 ◇ ((((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0))))) ◇ ((((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0))))) := ((f15 (((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0))) X1).symm).symm
      _ = (X1 ◇ ((((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0))))) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) := congrArg (X1 ◇ ·) (congrArg ((((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0))))) ◇ ·) ((f15 X0 ((((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0))))))).symm))
  have f27 : ∀ (X0 X1 : G), (((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0))))) = (X1 ◇ X0) := by
    intro X0 X1
    calc (((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)))))
      _ = (X1 ◇ ((((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0))))) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) := ((f22 X0 X1).symm).symm
      _ = (X1 ◇ X0) := congrArg (X1 ◇ ·) (f7 X0 ((((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)))))))
  have f34 : ∀ (X0 X1 : G), (((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) = (X1 ◇ X0) := by
    intro X0 X1
    calc (((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))))
      _ = (((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0))))) := congrArg (((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ ·) (congrArg (((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ ·) (((f15 X0 ((((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0))))).symm).symm))
      _ = (X1 ◇ X0) := f27 X0 X1
  have f38 : ∀ (X0 X1 : G), (((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    calc (((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ X0)
      _ = (((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) := congrArg (((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ ·) ((f7 X0 (((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)))).symm)
      _ = (X1 ◇ X0) := f34 X0 X1
  have f48 : ∀ (X2 X0 X1 : G), (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X2 X0 X1
    calc (X0 ◇ X1)
      _ = (((X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1))) ◇ ((X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1))) ◇ X1)) ◇ X1) := (f38 X1 X0).symm
      _ = (X2 ◇ X1) := f38 X1 X2
  calc (x ◇ y)
    _ = (((y ◇ z) ◇ z) ◇ y) := (f48 x (((y ◇ z) ◇ z)) y).symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_5775_to_4183 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_5775_to_4183
