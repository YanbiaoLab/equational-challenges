-- Equation41908 → Equation41802
-- Recorded verdict: true
-- Premise: x ◇ y = y ◇ (x ◇ (z ◇ (y ◇ y)))
-- Conclusion: x ◇ y = x ◇ (y ◇ (z ◇ (w ◇ y)))
-- Original submission SHA-256: 9976f3ec09277ffb768de16d72063ee20f3ef0050cb585195c2a6224858149fa
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = y ◇ (x ◇ (z ◇ (y ◇ y)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = x ◇ (y ◇ (z ◇ (w ◇ y)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   

set_option linter.unusedVariables false
set_option maxHeartbeats 400000
set_option maxRecDepth 100000

def submission : Goal := by
  intro G _ h
  intro x y z w
  have f7 : ∀ (X2 X0 X1 : G), (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X1)))) := by
    intro X2 X0 X1
    exact h X0 X1 X2
  have f15 : ∀ (X2 X0 X1 : G), (X2 ◇ (X0 ◇ (X1 ◇ X1))) = ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1))) := by
    intro X2 X0 X1
    calc (X2 ◇ (X0 ◇ (X1 ◇ X1)))
      _ = ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))))) := ((f7 X1 X2 ((X0 ◇ (X1 ◇ X1)))).symm).symm
      _ = ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1))) := congrArg ((X0 ◇ (X1 ◇ X1)) ◇ ·) (congrArg (X2 ◇ ·) ((f7 X0 ((X0 ◇ (X1 ◇ X1))) X1).symm))
  have f16 : ∀ (X0 X1 : G), (X1 ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    calc (X1 ◇ (X1 ◇ X1))
      _ = ((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))))) := ((f7 X0 X1 ((X1 ◇ X1))).symm).symm
      _ = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := congrArg ((X1 ◇ X1) ◇ ·) ((f7 ((X1 ◇ X1)) X0 X1).symm)
  have f27 : ∀ (X2 X0 X1 : G), (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X2 X0 X1
    calc (X1 ◇ (X0 ◇ X0))
      _ = ((X0 ◇ X0) ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) := ((f7 X2 X1 ((X0 ◇ X0))).symm).symm
      _ = ((X0 ◇ X0) ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))) := congrArg ((X0 ◇ X0) ◇ ·) (congrArg (X1 ◇ ·) (congrArg (X2 ◇ ·) ((f16 X0 X0).symm)))
  have f76 : ∀ (X0 X1 : G), (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) := by
    intro X0 X1
    calc (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))
      _ = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))))) := ((f27 X0 ((X0 ◇ X0)) X1).symm).symm
      _ = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) := congrArg (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ·) (congrArg (X1 ◇ ·) ((f7 ((X0 ◇ X0)) ((X0 ◇ X0)) X0).symm))
  have f99 : ∀ (X0 X1 : G), (X1 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) := by
    intro X0 X1
    calc (X1 ◇ (X0 ◇ (X0 ◇ X0)))
      _ = (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := congrArg (X1 ◇ ·) (f16 X0 X0)
      _ = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) := f76 X0 X1
      _ = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) := congrArg (· ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ((f16 X0 X0).symm)
  have f169 : ∀ (X2 X0 X1 : G), (X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) = (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ (X2 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))))) := by
    intro X2 X0 X1
    calc (X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1))
      _ = (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1))))) := ((f7 ((X0 ◇ (X1 ◇ X1))) X2 (((X0 ◇ (X1 ◇ X1)) ◇ X1))).symm).symm
      _ = (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ (X2 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))))) := congrArg (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ ·) (congrArg (X2 ◇ ·) ((f15 (((X0 ◇ (X1 ◇ X1)) ◇ X1)) X0 X1).symm))
  have f2558 : ∀ (X0 X1 : G), (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) = (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ X1)) := by
    intro X0 X1
    calc (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1))
      _ = (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ (X1 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))))) := ((f169 X1 X0 X1).symm).symm
      _ = (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ X1)) := congrArg (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ ·) ((f7 X0 (((X0 ◇ (X1 ◇ X1)) ◇ X1)) X1).symm)
  have f165 : ∀ (X0 X1 : G), ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    calc ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))
      _ = ((X1 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0))) := ((f15 ((X0 ◇ X0)) X1 X0).symm).symm
      _ = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := congrArg ((X1 ◇ (X0 ◇ X0)) ◇ ·) ((f16 ((X1 ◇ (X0 ◇ X0))) X0).symm)
  have f626 : ∀ (X0 X1 : G), ((X1 ◇ (X0 ◇ X0)) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    calc ((X1 ◇ (X0 ◇ X0)) ◇ X0)
      _ = (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := ((f7 X0 ((X1 ◇ (X0 ◇ X0))) X0).symm).symm
      _ = (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) := congrArg (X0 ◇ ·) ((f165 X0 X1).symm)
  have f641 : ∀ (X0 X1 : G), ((X0 ◇ X0) ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X0) := by
    intro X0 X1
    calc ((X0 ◇ X0) ◇ X0)
      _ = (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) := ((f7 X1 ((X0 ◇ X0)) X0).symm).symm
      _ = ((X1 ◇ (X0 ◇ X0)) ◇ X0) := (f626 X0 X1).symm
  have f2607 : ∀ (X1 : G), (X1 ◇ ((X1 ◇ X1) ◇ X1)) = (((X1 ◇ X1) ◇ X1) ◇ (((X1 ◇ X1) ◇ X1) ◇ X1)) := by
    intro X1
    calc (X1 ◇ ((X1 ◇ X1) ◇ X1))
      _ = (X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1)) := congrArg (X1 ◇ ·) (f641 X1 X1)
      _ = (((X1 ◇ (X1 ◇ X1)) ◇ X1) ◇ (((X1 ◇ (X1 ◇ X1)) ◇ X1) ◇ X1)) := f2558 X1 X1
      _ = (((X1 ◇ (X1 ◇ X1)) ◇ X1) ◇ (((X1 ◇ X1) ◇ X1) ◇ X1)) := congrArg (((X1 ◇ (X1 ◇ X1)) ◇ X1) ◇ ·) (congrArg (· ◇ X1) ((f641 X1 X1).symm))
      _ = (((X1 ◇ X1) ◇ X1) ◇ (((X1 ◇ X1) ◇ X1) ◇ X1)) := congrArg (· ◇ (((X1 ◇ X1) ◇ X1) ◇ X1)) ((f641 X1 X1).symm)
  have f677 : ∀ (X0 X1 : G), ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    calc ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))
      _ = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := congrArg (· ◇ (X0 ◇ X0)) (f16 X0 X0)
      _ = ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := f641 ((X0 ◇ X0)) X1
      _ = ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := congrArg (· ◇ (X0 ◇ X0)) (congrArg (X1 ◇ ·) ((f16 X0 X0).symm))
  have f1542 : ∀ (X0 X1 : G), (X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = ((X1 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ X0) := by
    intro X0 X1
    calc (X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))
      _ = (X0 ◇ ((X1 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := congrArg (X0 ◇ ·) (((f677 ((X0 ◇ X0)) X1).symm).symm)
      _ = ((X1 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ X0) := (f7 ((X0 ◇ X0)) ((X1 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) X0).symm
  have f1552 : ∀ (X0 X1 : G), (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) = ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X0) := by
    intro X0 X1
    calc (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))))
      _ = (X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) := congrArg (X0 ◇ ·) (congrArg (· ◇ (X0 ◇ (X0 ◇ X0))) (congrArg ((X0 ◇ X0) ◇ ·) (f16 X0 X0)))
      _ = (X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := congrArg (X0 ◇ ·) (congrArg (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ·) (f16 X0 X0))
      _ = ((X1 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ X0) := ((f1542 X0 X1).symm).symm
      _ = ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X0) := congrArg (· ◇ X0) (congrArg (X1 ◇ ·) (congrArg ((X0 ◇ X0) ◇ ·) ((f16 X0 X0).symm)))
  have f1582 : ∀ (X0 X1 : G), (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X0) := by
    intro X0 X1
    calc (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)
      _ = (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) := ((f7 X0 (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) X0).symm).symm
      _ = ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X0) := f1552 X0 X1
  have f627 : ∀ (X2 X0 X1 : G), (X2 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X2 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))))) := by
    intro X2 X0 X1
    calc (X2 ◇ (X0 ◇ X0))
      _ = ((X0 ◇ X0) ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))) := ((f27 ((X1 ◇ (X0 ◇ X0))) X0 X2).symm).symm
      _ = ((X0 ◇ X0) ◇ (X2 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))))) := congrArg ((X0 ◇ X0) ◇ ·) (congrArg (X2 ◇ ·) ((f165 X0 X1).symm))
  have f983 : ∀ (X0 X1 : G), ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) := by
    intro X0 X1
    calc ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))
      _ = ((X0 ◇ X0) ◇ ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))))) := ((f627 ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) X0 ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))).symm).symm
      _ = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) := congrArg ((X0 ◇ X0) ◇ ·) ((f15 ((X0 ◇ X0)) X1 ((X0 ◇ X0))).symm)
  have f1000 : ∀ (X0 X1 : G), ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    calc ((X0 ◇ X0) ◇ (X0 ◇ X0))
      _ = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) := ((f7 X1 ((X0 ◇ X0)) ((X0 ◇ X0))).symm).symm
      _ = ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := (f983 X0 X1).symm
  have f1018 : ∀ (X0 : G), ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    calc ((X0 ◇ X0) ◇ (X0 ◇ X0))
      _ = ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := ((f1000 X0 X0).symm).symm
      _ = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := (f641 ((X0 ◇ X0)) X0).symm
  have f1030 : ∀ (X0 : G), (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    calc (X0 ◇ (X0 ◇ X0))
      _ = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := f16 X0 X0
      _ = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := f1018 X0
      _ = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := congrArg (· ◇ (X0 ◇ X0)) ((f16 X0 X0).symm)
  have f1047 : ∀ (X0 : G), (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0) := by
    intro X0
    calc (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))
      _ = (X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := congrArg (X0 ◇ ·) (((f1030 ((X0 ◇ X0))).symm).symm)
      _ = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0) := (f7 ((X0 ◇ X0)) (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) X0).symm
  have f1061 : ∀ (X0 : G), (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := by
    intro X0
    calc (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))
      _ = (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := congrArg (X0 ◇ ·) (congrArg ((X0 ◇ X0) ◇ ·) (f16 X0 X0))
      _ = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0) := f1047 X0
      _ = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := congrArg (· ◇ X0) (congrArg ((X0 ◇ X0) ◇ ·) ((f16 X0 X0).symm))
  have f1063 : ∀ (X0 : G), ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := by
    intro X0
    calc ((X0 ◇ X0) ◇ X0)
      _ = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := ((f7 X0 ((X0 ◇ X0)) X0).symm).symm
      _ = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := f1061 X0
  have f1591 : ∀ (X0 X1 : G), ((X0 ◇ X0) ◇ X0) = ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X0) := by
    intro X0 X1
    calc ((X0 ◇ X0) ◇ X0)
      _ = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := ((f1063 X0).symm).symm
      _ = ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X0) := f1582 X0 X1
  have f1907 : ∀ (X0 : G), ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := by
    intro X0
    calc ((X0 ◇ X0) ◇ X0)
      _ = ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X0) := ((f1591 X0 X0).symm).symm
      _ = (((X0 ◇ X0) ◇ X0) ◇ X0) := congrArg (· ◇ X0) ((f7 X0 ((X0 ◇ X0)) X0).symm)
  have f2664 : ∀ (X1 : G), (((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) = (X1 ◇ ((X1 ◇ X1) ◇ X1)) := by
    intro X1
    calc (((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1))
      _ = (((X1 ◇ X1) ◇ X1) ◇ (((X1 ◇ X1) ◇ X1) ◇ X1)) := congrArg (((X1 ◇ X1) ◇ X1) ◇ ·) (((f1907 X1).symm).symm)
      _ = (X1 ◇ ((X1 ◇ X1) ◇ X1)) := (f2607 X1).symm
  have f2710 : ∀ (X0 : G), (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := by
    intro X0
    calc (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))
      _ = ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := ((f99 X0 (((X0 ◇ X0) ◇ X0))).symm).symm
      _ = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := congrArg ((X0 ◇ (X0 ◇ X0)) ◇ ·) (f2664 X0)
  have f717 : ∀ (X2 X0 X1 : G), (X1 ◇ (X2 ◇ (X0 ◇ X0))) = ((X2 ◇ (X0 ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) := by
    intro X2 X0 X1
    calc (X1 ◇ (X2 ◇ (X0 ◇ X0)))
      _ = ((X2 ◇ (X0 ◇ X0)) ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X0))) := ((f15 X1 X2 X0).symm).symm
      _ = ((X2 ◇ (X0 ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) := congrArg ((X2 ◇ (X0 ◇ X0)) ◇ ·) (congrArg (X1 ◇ ·) ((f641 X0 X2).symm))
  have f2740 : ∀ (X0 : G), (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    calc (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))
      _ = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := ((f2710 X0).symm).symm
      _ = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := (f717 X0 X0 X0).symm
  have f2750 : ∀ (X0 : G), (((X0 ◇ X0) ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0
    calc (((X0 ◇ X0) ◇ X0) ◇ X0)
      _ = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := ((f7 X0 (((X0 ◇ X0) ◇ X0)) X0).symm).symm
      _ = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := congrArg (X0 ◇ ·) (f2740 X0)
  have f2767 : ∀ (X0 : G), (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := by
    intro X0
    calc (X0 ◇ X0)
      _ = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := ((f7 X0 X0 X0).symm).symm
      _ = (((X0 ◇ X0) ◇ X0) ◇ X0) := (f2750 X0).symm
  have f2792 : ∀ (X0 X1 : G), (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) = ((((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) := by
    intro X0 X1
    calc (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))))
      _ = (X1 ◇ ((((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1)))) := congrArg (X1 ◇ ·) (((f2767 ((X0 ◇ (X1 ◇ X1)))).symm).symm)
      _ = ((((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) := (f7 X0 ((((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1)))) X1).symm
  have f700 : ∀ (X0 X1 : G), (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1))) = (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    calc (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1)))
      _ = ((X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ (X1 ◇ X1))) := ((f641 ((X0 ◇ (X1 ◇ X1))) X1).symm).symm
      _ = (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) := congrArg (· ◇ (X0 ◇ (X1 ◇ X1))) ((f7 X0 ((X0 ◇ (X1 ◇ X1))) X1).symm)
  have f767 : ∀ (X0 X1 : G), (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1))) = (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    calc (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1)))
      _ = (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) := ((f700 X0 X1).symm).symm
      _ = (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) := congrArg (· ◇ (X0 ◇ (X1 ◇ X1))) ((f641 X1 X0).symm)
  have f2841 : ∀ (X0 X1 : G), (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) = ((((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) := by
    intro X0 X1
    calc (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))))
      _ = ((((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) := ((f2792 X0 X1).symm).symm
      _ = ((((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) := congrArg (· ◇ X1) (f767 X0 X1)
  have f2057 : ∀ (X0 X1 : G), (X1 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1)))) = ((((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) := by
    intro X0 X1
    calc (X1 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1))))
      _ = (X1 ◇ ((((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1)))) := congrArg (X1 ◇ ·) (((f1907 ((X0 ◇ (X1 ◇ X1)))).symm).symm)
      _ = ((((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) := (f7 X0 ((((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1)))) X1).symm
  have f2104 : ∀ (X0 X1 : G), (X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ (X1 ◇ X1)))) = ((((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) := by
    intro X0 X1
    calc (X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))))
      _ = (X1 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1)))) := congrArg (X1 ◇ ·) ((f767 X0 X1).symm)
      _ = ((((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) := f2057 X0 X1
      _ = ((((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) := congrArg (· ◇ X1) (((f767 X0 X1).symm).symm)
  have f2127 : ∀ (X0 X1 : G), ((((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) = (((X1 ◇ X1) ◇ X1) ◇ X1) := by
    intro X0 X1
    calc ((((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1)
      _ = (X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ (X1 ◇ X1)))) := (f2104 X0 X1).symm
      _ = (((X1 ◇ X1) ◇ X1) ◇ X1) := (f7 X0 (((X1 ◇ X1) ◇ X1)) X1).symm
  have f2141 : ∀ (X0 X1 : G), ((X1 ◇ X1) ◇ X1) = ((((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) := by
    intro X0 X1
    calc ((X1 ◇ X1) ◇ X1)
      _ = (((X1 ◇ X1) ◇ X1) ◇ X1) := ((f1907 X1).symm).symm
      _ = ((((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) := (f2127 X0 X1).symm
  have f2866 : ∀ (X0 X1 : G), (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) = ((X1 ◇ X1) ◇ X1) := by
    intro X0 X1
    calc (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))))
      _ = ((((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) := ((f2841 X0 X1).symm).symm
      _ = ((X1 ◇ X1) ◇ X1) := (f2141 X0 X1).symm
  have f2780 : ∀ (X0 : G), (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    calc (X0 ◇ X0)
      _ = (((X0 ◇ X0) ◇ X0) ◇ X0) := ((f2767 X0).symm).symm
      _ = ((X0 ◇ X0) ◇ X0) := (f1907 X0).symm
  have f2888 : ∀ (X0 X1 : G), (X1 ◇ X1) = (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X0 X1
    calc (X1 ◇ X1)
      _ = ((X1 ◇ X1) ◇ X1) := ((f2780 X1).symm).symm
      _ = (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) := (f2866 X0 X1).symm
  have f2909 : ∀ (X0 X1 : G), (X1 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ X1) := by
    intro X0 X1
    calc (X1 ◇ X1)
      _ = (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) := ((f2888 X0 X1).symm).symm
      _ = ((X0 ◇ (X1 ◇ X1)) ◇ X1) := (f7 X0 ((X0 ◇ (X1 ◇ X1))) X1).symm
  have f3127 : ∀ (X2 X0 X1 : G), (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) = ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X1) := by
    intro X2 X0 X1
    calc (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))))
      _ = (X1 ◇ ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ (X1 ◇ X1)))) := congrArg (X1 ◇ ·) (((f2909 X2 ((X0 ◇ (X1 ◇ X1)))).symm).symm)
      _ = ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X1) := (f7 X0 ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))))) X1).symm
  have f3175 : ∀ (X2 X0 X1 : G), ((X0 ◇ (X1 ◇ X1)) ◇ X1) = ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X1) := by
    intro X2 X0 X1
    calc ((X0 ◇ (X1 ◇ X1)) ◇ X1)
      _ = (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) := ((f7 X0 ((X0 ◇ (X1 ◇ X1))) X1).symm).symm
      _ = ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X1) := f3127 X2 X0 X1
  have f3114 : ∀ (X2 X0 X1 : G), (X1 ◇ (X2 ◇ (X0 ◇ X0))) = ((X2 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X2 X0 X1
    calc (X1 ◇ (X2 ◇ (X0 ◇ X0)))
      _ = ((X2 ◇ (X0 ◇ X0)) ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X0))) := ((f15 X1 X2 X0).symm).symm
      _ = ((X2 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) := congrArg ((X2 ◇ (X0 ◇ X0)) ◇ ·) (congrArg (X1 ◇ ·) ((f2909 X2 X0).symm))
  have f3224 : ∀ (X2 X0 X1 : G), ((X0 ◇ (X1 ◇ X1)) ◇ X1) = ((X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X1) := by
    intro X2 X0 X1
    calc ((X0 ◇ (X1 ◇ X1)) ◇ X1)
      _ = ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X1) := ((f3175 X2 X0 X1).symm).symm
      _ = ((X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X1) := congrArg (· ◇ X1) (congrArg (X2 ◇ ·) ((f3114 X0 X1 X0).symm))
  have f3264 : ∀ (X2 X0 X1 : G), ((X1 ◇ X1) ◇ X1) = ((X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X1) := by
    intro X2 X0 X1
    calc ((X1 ◇ X1) ◇ X1)
      _ = ((X0 ◇ (X1 ◇ X1)) ◇ X1) := ((f641 X1 X0).symm).symm
      _ = ((X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X1) := f3224 X2 X0 X1
  have f3277 : ∀ (X2 X0 X1 : G), (X1 ◇ X1) = ((X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X1) := by
    intro X2 X0 X1
    calc (X1 ◇ X1)
      _ = ((X1 ◇ X1) ◇ X1) := ((f2780 X1).symm).symm
      _ = ((X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X1) := f3264 X2 X0 X1
  have f3617 : ∀ (X0 X1 : G), (X1 ◇ X1) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    calc (X1 ◇ X1)
      _ = ((X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X1) := ((f3277 X1 X0 X1).symm).symm
      _ = ((X0 ◇ X1) ◇ X1) := congrArg (· ◇ X1) ((f7 X0 X0 X1).symm)
  have f4105 : ∀ (X0 X1 : G), ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    calc ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))
      _ = ((X0 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) := congrArg ((X0 ◇ (X0 ◇ X0)) ◇ ·) (((f3617 X1 (((X0 ◇ X0) ◇ X0))).symm).symm)
      _ = ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := (f99 X0 ((X1 ◇ ((X0 ◇ X0) ◇ X0)))).symm
  have f4166 : ∀ (X0 X1 : G), ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    calc ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))
      _ = ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := congrArg (· ◇ (X0 ◇ (X0 ◇ X0))) (congrArg (X1 ◇ ·) (f2780 X0))
      _ = ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := (f4105 X0 X1).symm
      _ = ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := congrArg ((X0 ◇ (X0 ◇ X0)) ◇ ·) (congrArg (((X0 ◇ X0) ◇ X0) ◇ ·) ((f2780 X0).symm))
      _ = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := congrArg ((X0 ◇ (X0 ◇ X0)) ◇ ·) (congrArg (· ◇ (X0 ◇ X0)) ((f2780 X0).symm))
  have f4244 : ∀ (X0 X1 : G), ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    calc ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))
      _ = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := ((f3114 X0 X0 ((X0 ◇ X0))).symm).symm
      _ = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := (f4166 X0 X1).symm
  have f4274 : ∀ (X0 X1 : G), ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    calc ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))
      _ = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := ((f4244 X0 X1).symm).symm
      _ = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := (f3114 X1 X0 X0).symm
  have f3050 : ∀ (X0 X1 : G), ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) = (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    calc ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))
      _ = ((X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ (X1 ◇ X1))) := ((f2909 X1 ((X0 ◇ (X1 ◇ X1)))).symm).symm
      _ = (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) := congrArg (· ◇ (X0 ◇ (X1 ◇ X1))) ((f7 X0 ((X0 ◇ (X1 ◇ X1))) X1).symm)
  have f3181 : ∀ (X0 X1 : G), ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) = (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    calc ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))
      _ = (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) := ((f3050 X0 X1).symm).symm
      _ = (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) := congrArg (· ◇ (X0 ◇ (X1 ◇ X1))) ((f641 X1 X0).symm)
  have f3229 : ∀ (X0 X1 : G), ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) = ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    calc ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))
      _ = (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) := ((f3181 X0 X1).symm).symm
      _ = ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) := congrArg (· ◇ (X0 ◇ (X1 ◇ X1))) ((f2780 X1).symm)
  have f3268 : ∀ (X0 X1 : G), ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    calc ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1)))
      _ = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) := (f3229 X0 X1).symm
      _ = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := (f3114 X0 X1 X0).symm
  have f4280 : ∀ (X0 X1 : G), (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    calc (X0 ◇ (X0 ◇ (X0 ◇ X0)))
      _ = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := (f4274 X0 X0).symm
      _ = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := f4274 X0 X1
  have f5635 : ∀ (X0 X1 : G), (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    calc (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))
      _ = ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)))) := ((f15 X0 X1 ((X0 ◇ X0))).symm).symm
      _ = ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := congrArg ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ·) ((f4280 X0 ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))).symm)
  have f5638 : ∀ (X0 X1 : G), (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    calc (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))
      _ = (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := congrArg (X0 ◇ ·) (congrArg (X1 ◇ ·) (f16 X0 X0))
      _ = ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := f5635 X0 X1
      _ = ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := congrArg (· ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) (congrArg (X1 ◇ ·) ((f16 X0 X0).symm))
  have f4100 : ∀ (X2 X0 X1 : G), (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) = ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) := by
    intro X2 X0 X1
    calc (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))))
      _ = (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1)))) := congrArg (X1 ◇ ·) (((f3617 X2 ((X0 ◇ (X1 ◇ X1)))).symm).symm)
      _ = ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) := (f7 X0 ((X2 ◇ (X0 ◇ (X1 ◇ X1)))) X1).symm
  have f4168 : ∀ (X2 X0 X1 : G), ((X0 ◇ (X1 ◇ X1)) ◇ X1) = ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) := by
    intro X2 X0 X1
    calc ((X0 ◇ (X1 ◇ X1)) ◇ X1)
      _ = (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) := ((f7 X0 ((X0 ◇ (X1 ◇ X1))) X1).symm).symm
      _ = ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) := f4100 X2 X0 X1
  have f4246 : ∀ (X2 X0 X1 : G), ((X1 ◇ X1) ◇ X1) = ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) := by
    intro X2 X0 X1
    calc ((X1 ◇ X1) ◇ X1)
      _ = ((X0 ◇ (X1 ◇ X1)) ◇ X1) := ((f641 X1 X0).symm).symm
      _ = ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) := f4168 X2 X0 X1
  have f4276 : ∀ (X2 X0 X1 : G), (X1 ◇ X1) = ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) := by
    intro X2 X0 X1
    calc (X1 ◇ X1)
      _ = ((X1 ◇ X1) ◇ X1) := ((f2780 X1).symm).symm
      _ = ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) := f4246 X2 X0 X1
  have f4621 : ∀ (X0 X1 : G), ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    calc ((X1 ◇ X1) ◇ (X1 ◇ X1))
      _ = ((X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) ◇ (X1 ◇ X1)) := ((f4276 X1 X0 ((X1 ◇ X1))).symm).symm
      _ = ((X0 ◇ X1) ◇ (X1 ◇ X1)) := congrArg (· ◇ (X1 ◇ X1)) ((f7 ((X1 ◇ X1)) X0 X1).symm)
  have f4704 : ∀ (X0 X1 : G), (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    calc (X1 ◇ (X1 ◇ X1))
      _ = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := ((f16 X1 X1).symm).symm
      _ = ((X0 ◇ X1) ◇ (X1 ◇ X1)) := f4621 X0 X1
  have f4999 : ∀ (X0 X1 : G), ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    calc ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))
      _ = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := congrArg ((X0 ◇ (X0 ◇ X0)) ◇ ·) (f165 X0 X0)
      _ = ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := f4704 X1 ((X0 ◇ (X0 ◇ X0)))
      _ = ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := congrArg ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ·) ((f165 X0 X0).symm)
  have f5062 : ∀ (X0 X1 : G), ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    calc ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))
      _ = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := congrArg ((X0 ◇ (X0 ◇ X0)) ◇ ·) ((f3268 X0 X0).symm)
      _ = ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := f4999 X0 X1
      _ = ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := congrArg ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ·) (((f3268 X0 X0).symm).symm)
  have f2193 : ∀ (X0 X1 : G), (((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) = (((((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := by
    intro X0 X1
    calc (((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))
      _ = (((((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ ((X1 ◇ X1) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := ((f2141 ((X1 ◇ X1)) ((X0 ◇ (X1 ◇ (X1 ◇ X1))))).symm).symm
      _ = (((((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := congrArg (· ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) (congrArg ((((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ ·) ((f27 X0 X1 ((X0 ◇ (X1 ◇ (X1 ◇ X1))))).symm))
  have f2303 : ∀ (X0 X1 : G), (((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) = (((((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := by
    intro X0 X1
    calc (((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))
      _ = (((((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := ((f2193 X0 X1).symm).symm
      _ = (((((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := congrArg (· ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) (congrArg ((((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ ·) ((f677 X1 X0).symm))
  have f2350 : ∀ (X0 X1 : G), (((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) = (((((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := by
    intro X0 X1
    calc (((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))
      _ = (((((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := ((f2303 X0 X1).symm).symm
      _ = (((((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := congrArg (· ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) (congrArg ((((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ ·) ((f1030 X1).symm))
  have f702 : ∀ (X0 X1 : G), (((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) = (((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := by
    intro X0 X1
    calc (((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))
      _ = (((X1 ◇ X1) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := ((f641 ((X0 ◇ (X1 ◇ (X1 ◇ X1)))) ((X1 ◇ X1))).symm).symm
      _ = (((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := congrArg (· ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ((f27 X0 X1 ((X0 ◇ (X1 ◇ (X1 ◇ X1))))).symm)
  have f2387 : ∀ (X0 X1 : G), (((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) = (((((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := by
    intro X0 X1
    calc (((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))
      _ = (((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := (f702 X0 X1).symm
      _ = (((((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := f2350 X0 X1
      _ = (((((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := congrArg (· ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) (congrArg (· ◇ (X1 ◇ (X1 ◇ X1))) (((f702 X0 X1).symm).symm))
  have f2415 : ∀ (X0 X1 : G), (((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) = (((((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := by
    intro X0 X1
    calc (((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))
      _ = (((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := congrArg (· ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) (f677 X1 X0)
      _ = (((((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := f2387 X0 X1
      _ = (((((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := congrArg (· ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) (congrArg (· ◇ (X1 ◇ (X1 ◇ X1))) (congrArg (· ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ((f677 X1 X0).symm)))
  have f2423 : ∀ (X0 X1 : G), ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) = ((((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := by
    intro X0 X1
    calc ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))
      _ = (((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := congrArg (· ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) (f1030 X1)
      _ = (((((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := f2415 X0 X1
      _ = ((((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := congrArg (· ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) (congrArg (· ◇ (X1 ◇ (X1 ◇ X1))) (congrArg (· ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ((f1030 X1).symm)))
  have f1513 : ∀ (X0 X1 : G), ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    calc ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))
      _ = (((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := ((f677 X0 ((X1 ◇ (X0 ◇ X0)))).symm).symm
      _ = (((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := congrArg (· ◇ (X0 ◇ X0)) ((f165 X0 X1).symm)
  have f1571 : ∀ (X0 X1 : G), (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    calc (X0 ◇ (X0 ◇ X0))
      _ = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := ((f1030 X0).symm).symm
      _ = (((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := f1513 X0 X1
  have f1805 : ∀ (X0 X1 : G), ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    calc ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))
      _ = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := congrArg ((X0 ◇ X0) ◇ ·) (f16 X0 X0)
      _ = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := f1571 ((X0 ◇ X0)) X1
      _ = (((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := congrArg (· ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) (congrArg (· ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ((f16 X0 X0).symm))
      _ = (((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ (X0 ◇ (X0 ◇ X0))) := congrArg (((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ ·) ((f16 X0 X0).symm)
      _ = (((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ (X0 ◇ X0))) := congrArg (· ◇ (X0 ◇ (X0 ◇ X0))) (congrArg ((X0 ◇ (X0 ◇ X0)) ◇ ·) (congrArg (X1 ◇ ·) ((f16 X0 X0).symm)))
  have f2429 : ∀ (X0 X1 : G), ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) = (((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := by
    intro X0 X1
    calc ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))
      _ = ((((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := ((f2423 X0 X1).symm).symm
      _ = (((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := congrArg (· ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ((f1805 X1 X0).symm)
  have f1827 : ∀ (X0 X1 : G), (X1 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    calc (X1 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))
      _ = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X1 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)))) := ((f15 X1 ((X0 ◇ X0)) ((X0 ◇ X0))).symm).symm
      _ = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := congrArg (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ·) (congrArg (X1 ◇ ·) ((f1571 X0 ((X0 ◇ X0))).symm))
  have f1830 : ∀ (X0 X1 : G), (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    calc (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))
      _ = (X1 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := congrArg (X1 ◇ ·) (congrArg ((X0 ◇ X0) ◇ ·) (f16 X0 X0))
      _ = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := f1827 X0 X1
      _ = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := congrArg (· ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) (congrArg ((X0 ◇ X0) ◇ ·) ((f16 X0 X0).symm))
  have f2431 : ∀ (X0 X1 : G), (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1)))) = ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := by
    intro X0 X1
    calc (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))))
      _ = (((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := ((f1830 X1 X0).symm).symm
      _ = ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := (f2429 X0 X1).symm
  have f5077 : ∀ (X0 X1 : G), (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    calc (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))
      _ = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := ((f2431 X0 X0).symm).symm
      _ = ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := f5062 X0 X1
  have f5080 : ∀ (X0 X1 : G), ((X0 ◇ X0) ◇ X0) = ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    calc ((X0 ◇ X0) ◇ X0)
      _ = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := ((f7 X0 ((X0 ◇ X0)) X0).symm).symm
      _ = ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := f5077 X0 X1
  have f5083 : ∀ (X0 X1 : G), (X0 ◇ X0) = ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    calc (X0 ◇ X0)
      _ = ((X0 ◇ X0) ◇ X0) := ((f2780 X0).symm).symm
      _ = ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := f5080 X0 X1
  have f5662 : ∀ (X0 X1 : G), (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    calc (X0 ◇ X0)
      _ = ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := ((f5083 X0 X1).symm).symm
      _ = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := (f5638 X0 X1).symm
  have f5673 : ∀ (X0 X1 : G), (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    calc (X0 ◇ X0)
      _ = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := ((f5662 X0 X1).symm).symm
      _ = (X1 ◇ X0) := (f7 X0 X1 X0).symm
  calc (x ◇ y)
    _ = (y ◇ y) := (f5673 y x).symm
    _ = (y ◇ (y ◇ (z ◇ (y ◇ y)))) := h y y z
    _ = ((y ◇ (z ◇ (y ◇ y))) ◇ (y ◇ (z ◇ (y ◇ y)))) := (f5673 ((y ◇ (z ◇ (y ◇ y)))) y).symm
    _ = (x ◇ (y ◇ (z ◇ (y ◇ y)))) := ((f5673 ((y ◇ (z ◇ (y ◇ y)))) x).symm).symm
    _ = (x ◇ (y ◇ (z ◇ (w ◇ y)))) := congrArg (x ◇ ·) (congrArg (y ◇ ·) (congrArg (z ◇ ·) (((f5673 y w).symm).symm)))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_41908_to_41802 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_41908_to_41802
