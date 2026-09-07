-- Equation5795 → Equation49712
-- Recorded verdict: true
-- Premise: x = y ◇ (x ◇ (x ◇ ((z ◇ x) ◇ x)))
-- Conclusion: x ◇ y = (x ◇ (z ◇ (x ◇ w))) ◇ y
-- Original submission SHA-256: 72accb7a3cef76892136bfeb514ea440dacc732c39f592a95f88a3432e1c1605
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
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (x ◇ (z ◇ (x ◇ w))) ◇ y
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
  have f119 : ∀ (X2 X3 X0 X1 : G), (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ ((X2 ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0))))) = (X3 ◇ X0) := by
    intro X2 X3 X0 X1
    calc (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ ((X2 ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)))))
      _ = (X3 ◇ ((((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ ((X2 ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0))))) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))))) := ((f92 X2 X3 X0 X1).symm).symm
      _ = (X3 ◇ X0) := congrArg (X3 ◇ ·) (f7 X1 X0 ((((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ ((X2 ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)))))))
  have f150 : ∀ (X3 X0 X1 : G), (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))))) = (X3 ◇ X0) := by
    intro X3 X0 X1
    calc (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))))
      _ = (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ ((X3 ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0))))) := congrArg (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ ·) (congrArg (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ ·) (((f21 X1 X0 ((X3 ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0))))).symm).symm))
      _ = (X3 ◇ X0) := f119 X3 X3 X0 X1
  have f174 : ∀ (X3 X0 X1 : G), (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ X0) = (X3 ◇ X0) := by
    intro X3 X0 X1
    calc (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ X0)
      _ = (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))))) := congrArg (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ ·) ((f7 X1 X0 (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)))).symm)
      _ = (X3 ◇ X0) := f150 X3 X0 X1
  have f812 : ∀ (X3 X0 X1 : G), (X0 ◇ X1) = (X3 ◇ X1) := by
    intro X3 X0 X1
    calc (X0 ◇ X1)
      _ = (((X1 ◇ (X1 ◇ ((X3 ◇ X1) ◇ X1))) ◇ ((X1 ◇ (X1 ◇ ((X3 ◇ X1) ◇ X1))) ◇ X1)) ◇ X1) := (f174 X0 X1 X3).symm
      _ = (X3 ◇ X1) := f174 X3 X1 X3
  calc (x ◇ y)
    _ = ((x ◇ (z ◇ (x ◇ w))) ◇ y) := (f812 x ((x ◇ (z ◇ (x ◇ w)))) y).symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_5795_to_49712 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_5795_to_49712
