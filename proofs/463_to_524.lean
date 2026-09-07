-- Equation463 → Equation524
-- Recorded verdict: true
-- Premise: x = y ◇ (x ◇ (x ◇ (x ◇ x)))
-- Conclusion: x = y ◇ (y ◇ (z ◇ (y ◇ x)))
-- Original submission SHA-256: cabc3ee334f970b8774e960db89d60ccd55fb85d456656a7faecfd19994fd08a
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = y ◇ (x ◇ (x ◇ (x ◇ x)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (y ◇ (z ◇ (y ◇ x)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   

set_option linter.unusedVariables false
set_option maxHeartbeats 400000
set_option maxRecDepth 100000

def submission : Goal := by
  intro G _ h
  intro x y z
  have f7 : ∀ (X0 X1 : G), (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := by
    intro X0 X1
    exact (h X0 X1).symm
  have f14 : ∀ (X0 X1 : G), (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))) := by
    intro X0 X1
    calc (X0 ◇ (X0 ◇ (X0 ◇ X0)))
      _ = (X1 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))))) := (f7 ((X0 ◇ (X0 ◇ (X0 ◇ X0)))) X1).symm
      _ = (X1 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))) := congrArg (X1 ◇ ·) (congrArg ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ·) (congrArg ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ·) (f7 X0 ((X0 ◇ (X0 ◇ (X0 ◇ X0)))))))
  have f18 : ∀ (X0 X1 : G), (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))))) = (X1 ◇ ((((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X0 X1
    calc (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)))))
      _ = (X1 ◇ ((((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))))) ◇ ((((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))))) := ((f14 (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))) X1).symm).symm
      _ = (X1 ◇ ((((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := congrArg (X1 ◇ ·) (congrArg ((((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))))) ◇ ·) ((f14 X0 ((((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))))))).symm))
  have f21 : ∀ (X0 X1 : G), (X1 ◇ X0) = (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))))) := by
    intro X0 X1
    calc (X1 ◇ X0)
      _ = (X1 ◇ ((((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := congrArg (X1 ◇ ·) ((f7 X0 ((((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))))))).symm)
      _ = (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))))) := (f18 X0 X1).symm
  have f25 : ∀ (X0 X1 : G), (X1 ◇ X0) = (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X0 X1
    calc (X1 ◇ X0)
      _ = (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))))) := ((f21 X0 X1).symm).symm
      _ = (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := congrArg (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ ·) (congrArg (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ ·) ((f14 X0 (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)))).symm))
  have f27 : ∀ (X0 X1 : G), (X1 ◇ X0) = (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ X0) := by
    intro X0 X1
    calc (X1 ◇ X0)
      _ = (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := ((f25 X0 X1).symm).symm
      _ = (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ X0) := congrArg (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ ·) (f7 X0 (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))))
  have f35 : ∀ (X2 X0 X1 : G), (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X2 X0 X1
    calc (X0 ◇ X1)
      _ = (((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1)) ◇ X1) := ((f27 X1 X0).symm).symm
      _ = (X2 ◇ X1) := (f27 X1 X2).symm
  calc x
    _ = (y ◇ (x ◇ (x ◇ (x ◇ x)))) := h x y
    _ = (y ◇ (x ◇ (x ◇ (y ◇ x)))) := congrArg (y ◇ ·) (congrArg (x ◇ ·) (congrArg (x ◇ ·) (f35 y x x)))
    _ = (y ◇ (x ◇ (z ◇ (y ◇ x)))) := congrArg (y ◇ ·) (congrArg (x ◇ ·) ((f35 x z ((y ◇ x))).symm))
    _ = (y ◇ (y ◇ (z ◇ (y ◇ x)))) := congrArg (y ◇ ·) ((f35 x y ((z ◇ (y ◇ x)))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_463_to_524 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_463_to_524
