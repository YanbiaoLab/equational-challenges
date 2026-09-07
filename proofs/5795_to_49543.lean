-- Equation5795 → Equation49543
-- Recorded verdict: true
-- Premise: x = y ◇ (x ◇ (x ◇ ((z ◇ x) ◇ x)))
-- Conclusion: x ◇ x = (y ◇ (y ◇ (z ◇ w))) ◇ x
-- Original submission SHA-256: 407cfdb1d722fbda9667c194d6986a78d2188a1957da75fb3aa89fea73574d2e
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (x ◇ (x ◇ ((z ◇ x) ◇ x)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ x = (y ◇ (y ◇ (z ◇ w))) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   

set_option linter.unusedVariables false
set_option maxHeartbeats 400000
set_option maxRecDepth 100000

def submission : Goal := by
  intro G _ h
  intro x y z w
  have f7 : ∀ (X2 X0 X1 : G), (X1 ◇ (X0 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0)))) = X0 := by
    intro X2 X0 X1
    exact (h X0 X1 X2).symm
  have f21 : ∀ (X2 X0 X1 : G), (X0 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0))) = (X1 ◇ ((X0 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0))) ◇ X0))) := by
    intro X2 X0 X1
    calc (X0 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0)))
      _ = (X1 ◇ ((X0 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0))) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0)))) ◇ (X0 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0))))))) := (f7 X2 ((X0 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0)))) X1).symm
      _ = (X1 ◇ ((X0 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0))) ◇ X0))) := congrArg (X1 ◇ ·) (congrArg ((X0 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0))) ◇ ·) (congrArg ((X0 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0))) ◇ ·) (f7 X2 X0 ((X2 ◇ (X0 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0))))))))
  have f92 : ∀ (X2 X3 X0 X1 : G), (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ ((X2 ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0))))) = (X3 ◇ ((((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ ((X2 ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0))))) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))))) := by
    intro X2 X3 X0 X1
    calc (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ ((X2 ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)))))
      _ = (X3 ◇ ((((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ ((X2 ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0))))) ◇ ((((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ ((X2 ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0))))) := ((f21 X2 (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0))) X3).symm).symm
      _ = (X3 ◇ ((((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ ((X2 ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0))))) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))))) := congrArg (X3 ◇ ·) (congrArg ((((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ ((X2 ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0))))) ◇ ·) ((f21 X1 X0 ((((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ ((X2 ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0))))))).symm))
  have f119 : ∀ (X2 X3 X0 X1 : G), (X3 ◇ X0) = (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ ((X2 ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0))))) := by
    intro X2 X3 X0 X1
    calc (X3 ◇ X0)
      _ = (X3 ◇ ((((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ ((X2 ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0))))) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))))) := congrArg (X3 ◇ ·) ((f7 X1 X0 ((((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ ((X2 ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0))))))).symm)
      _ = (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ ((X2 ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0))))) := (f92 X2 X3 X0 X1).symm
  have f150 : ∀ (X3 X0 X1 : G), (X3 ◇ X0) = (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))))) := by
    intro X3 X0 X1
    calc (X3 ◇ X0)
      _ = (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ ((X3 ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0))))) := ((f119 X3 X3 X0 X1).symm).symm
      _ = (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))))) := congrArg (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ ·) (congrArg (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ ·) ((f21 X1 X0 ((X3 ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0))))).symm))
  have f174 : ∀ (X3 X0 X1 : G), (X3 ◇ X0) = (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ X0) := by
    intro X3 X0 X1
    calc (X3 ◇ X0)
      _ = (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))))) := ((f150 X3 X0 X1).symm).symm
      _ = (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ X0) := congrArg (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ ·) (f7 X1 X0 (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0))))
  have f843 : ∀ (X2 X0 X1 : G), (X2 ◇ X1) = (X0 ◇ X1) := by
    intro X2 X0 X1
    calc (X2 ◇ X1)
      _ = (((X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) ◇ ((X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) ◇ X1)) ◇ X1) := ((f174 X2 X1 X2).symm).symm
      _ = (X0 ◇ X1) := (f174 X0 X1 X2).symm
  calc (x ◇ x)
    _ = ((y ◇ (y ◇ (z ◇ w))) ◇ x) := (f843 ((y ◇ (y ◇ (z ◇ w)))) x x).symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_5795_to_49543 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_5795_to_49543
