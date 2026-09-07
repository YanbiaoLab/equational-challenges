-- Equation44575 → Equation54051
-- Recorded verdict: true
-- Premise: x * y = y * ((y * (z * y)) * x)
-- Conclusion: x * (y * x) = y * (x * (y * y))
-- Original submission SHA-256: dd0ab77b9899c5cd5b46c6bae73ea964ec55090beb3f361ae3a4206dca884c3d
-- Aurora-accepted correction SHA-256: 6e344062b177359550e7b0c2afc3fd6ceae9da6f0fa3fec202001b6f99c02a31
-- Generator: equational-challenges standalone v2
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = y ◇ ((y ◇ (z ◇ y)) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ (y ◇ x) = y ◇ (x ◇ (y ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Aurora-accepted corrected submission body
                   

namespace submission

section
                       

namespace Equation44575Kernel

class Law (G : Type) [Magma G] : Prop where
  source : ∀ (x y z : G), x ◇ y = y ◇ ((y ◇ (z ◇ y)) ◇ x)

variable {G : Type} [Magma G] [Law G]

                                         

set_option linter.unusedVariables false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000


theorem c_0_3 : ∀ (X1 X2 X3 : G), (X1 ◇ X2) = (X2 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X1)) := by
  intro X1 X2 X3
  exact (Law.source (G := G)) X1 X2 X3

theorem c_0_4 : ∀ (X1 X2 : G), (X1 ◇ ((X1 ◇ X1) ◇ X2)) = (X2 ◇ X1) := by
  intro X1 X2
  calc (X1 ◇ ((X1 ◇ X1) ◇ X2))
    _ = (X1 ◇ ((X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1)) ◇ X2)) := congrArg (X1 ◇ ·) (congrArg (· ◇ X2) (((c_0_3 X1 X1 X1).symm).symm))
    _ = (X2 ◇ X1) := (c_0_3 X2 X1 ((X1 ◇ (X1 ◇ X1)))).symm

theorem c_0_5 : ∀ (X1 X2 X3 : G), ((((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))) ◇ X3) ◇ X1) = (X1 ◇ (X3 ◇ (X1 ◇ X1))) := by
  intro X1 X2 X3
  calc ((((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))) ◇ X3) ◇ X1)
    _ = (X1 ◇ ((X1 ◇ X1) ◇ (((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))) ◇ X3))) := (c_0_4 X1 ((((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))) ◇ X3))).symm
    _ = (X1 ◇ (X3 ◇ (X1 ◇ X1))) := congrArg (X1 ◇ ·) ((c_0_3 X3 ((X1 ◇ X1)) X2).symm)

theorem c_0_6 : ∀ (X1 X2 : G), ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X2) ◇ X1) = (X1 ◇ (X2 ◇ (X1 ◇ X1))) := by
  intro X1 X2
  calc ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X2) ◇ X1)
    _ = (X1 ◇ ((X1 ◇ X1) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X2))) := (c_0_4 X1 ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X2))).symm
    _ = (X1 ◇ (X2 ◇ (X1 ◇ X1))) := congrArg (X1 ◇ ·) (c_0_4 ((X1 ◇ X1)) X2)

theorem c_0_7 : ∀ (X1 X2 X3 : G), ((((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) ◇ X3) ◇ X1) = (X1 ◇ (X3 ◇ (X1 ◇ (X2 ◇ X1)))) := by
  intro X1 X2 X3
  calc ((((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) ◇ X3) ◇ X1)
    _ = (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) ◇ X3))) := ((c_0_3 ((((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) ◇ X3)) X1 X2).symm).symm
    _ = (X1 ◇ (X3 ◇ (X1 ◇ (X2 ◇ X1)))) := congrArg (X1 ◇ ·) (c_0_4 ((X1 ◇ (X2 ◇ X1))) X3)

theorem c_0_8 : ∀ (X1 X2 : G), ((X1 ◇ ((X2 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) := by
  intro X1 X2
  calc ((X1 ◇ ((X2 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1))
    _ = (((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X2 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) ◇ X1) ◇ (X1 ◇ X1)) := congrArg (· ◇ (X1 ◇ X1)) ((c_0_6 X1 ((X2 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))))).symm)
    _ = ((X1 ◇ X1) ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) := c_0_5 ((X1 ◇ X1)) X2 X1
    _ = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) := congrArg ((X1 ◇ X1) ◇ ·) (((c_0_4 X1 ((X1 ◇ X1))).symm).symm)

theorem c_0_9 : ∀ (X1 X2 : G), ((X1 ◇ (((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X1)) := by
  intro X1 X2
  calc ((X1 ◇ (((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1))
    _ = (((((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))) ◇ ((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1)))) ◇ X1) ◇ (X1 ◇ X1)) := congrArg (· ◇ (X1 ◇ X1)) ((c_0_5 X1 X2 (((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))))).symm)
    _ = ((X1 ◇ X1) ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))))) := c_0_7 ((X1 ◇ X1)) X2 X1
    _ = ((X1 ◇ X1) ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X1)) := congrArg ((X1 ◇ X1) ◇ ·) (((c_0_4 X1 ((X2 ◇ (X1 ◇ X1)))).symm).symm)

theorem c_0_10 : ∀ (X1 : G), ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) = (X1 ◇ (X1 ◇ X1)) := by
  intro X1
  calc ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1))
    _ = ((X1 ◇ (((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1)) := (c_0_8 X1 ((X1 ◇ X1))).symm
    _ = ((X1 ◇ X1) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X1)) := ((c_0_9 X1 ((X1 ◇ X1))).symm).symm
    _ = (X1 ◇ (X1 ◇ X1)) := ((c_0_4 ((X1 ◇ X1)) X1).symm).symm

theorem c_0_11 : ∀ (X1 X2 : G), ((X1 ◇ ((X2 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ X1)) := by
  intro X1 X2
  calc ((X1 ◇ ((X2 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1))
    _ = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) := ((c_0_8 X1 X2).symm).symm
    _ = (X1 ◇ (X1 ◇ X1)) := c_0_10 X1

theorem c_0_12 : ∀ (X1 X2 X3 X4 : G), ((((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X4) ◇ X1) = (X1 ◇ (X4 ◇ (X1 ◇ (X2 ◇ X1)))) := by
  intro X1 X2 X3 X4
  calc ((((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X4) ◇ X1)
    _ = (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X4))) := ((c_0_3 ((((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X4)) X1 X2).symm).symm
    _ = (X1 ◇ (X4 ◇ (X1 ◇ (X2 ◇ X1)))) := congrArg (X1 ◇ ·) ((c_0_3 X4 ((X1 ◇ (X2 ◇ X1))) X3).symm)

theorem c_0_13 : ∀ (X1 X2 : G), ((X1 ◇ X1) ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X1)) = (X1 ◇ (X1 ◇ X1)) := by
  intro X1 X2
  calc ((X1 ◇ X1) ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X1))
    _ = ((X1 ◇ (((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1)) := (c_0_9 X1 X2).symm
    _ = ((X1 ◇ ((X1 ◇ X1) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1)))))) ◇ (X1 ◇ X1)) := congrArg (· ◇ (X1 ◇ X1)) (congrArg (X1 ◇ ·) ((c_0_4 ((X1 ◇ X1)) (((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))))).symm))
    _ = ((X1 ◇ (((((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))) ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))))) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1)) := congrArg (· ◇ (X1 ◇ X1)) (congrArg (X1 ◇ ·) ((c_0_12 ((X1 ◇ X1)) X2 X1 (((X1 ◇ X1) ◇ (X1 ◇ X1)))).symm))
    _ = (X1 ◇ (X1 ◇ X1)) := c_0_11 X1 ((((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))) ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))))))

theorem c_0_14 : ∀ (X1 X2 X3 : G), ((X1 ◇ ((X2 ◇ ((X1 ◇ (X3 ◇ X1)) ◇ (X1 ◇ (X3 ◇ X1)))) ◇ (X1 ◇ (X3 ◇ X1)))) ◇ (X1 ◇ (X3 ◇ X1))) = ((X1 ◇ (X3 ◇ X1)) ◇ ((X1 ◇ (X3 ◇ X1)) ◇ X1)) := by
  intro X1 X2 X3
  calc ((X1 ◇ ((X2 ◇ ((X1 ◇ (X3 ◇ X1)) ◇ (X1 ◇ (X3 ◇ X1)))) ◇ (X1 ◇ (X3 ◇ X1)))) ◇ (X1 ◇ (X3 ◇ X1)))
    _ = (((((X1 ◇ (X3 ◇ X1)) ◇ (X1 ◇ (X3 ◇ X1))) ◇ (X2 ◇ ((X1 ◇ (X3 ◇ X1)) ◇ (X1 ◇ (X3 ◇ X1))))) ◇ X1) ◇ (X1 ◇ (X3 ◇ X1))) := congrArg (· ◇ (X1 ◇ (X3 ◇ X1))) ((c_0_7 X1 X3 ((X2 ◇ ((X1 ◇ (X3 ◇ X1)) ◇ (X1 ◇ (X3 ◇ X1)))))).symm)
    _ = ((X1 ◇ (X3 ◇ X1)) ◇ (X1 ◇ ((X1 ◇ (X3 ◇ X1)) ◇ (X1 ◇ (X3 ◇ X1))))) := c_0_5 ((X1 ◇ (X3 ◇ X1))) X2 X1
    _ = ((X1 ◇ (X3 ◇ X1)) ◇ ((X1 ◇ (X3 ◇ X1)) ◇ X1)) := congrArg ((X1 ◇ (X3 ◇ X1)) ◇ ·) ((c_0_3 ((X1 ◇ (X3 ◇ X1))) X1 X3).symm)

theorem c_0_15 : ∀ (X1 X2 X3 : G), ((X1 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X1 ◇ (X2 ◇ X1))) = ((X1 ◇ (X2 ◇ X1)) ◇ ((X3 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1)) := by
  intro X1 X2 X3
  calc ((X1 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X1 ◇ (X2 ◇ X1)))
    _ = (((((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X1))))) ◇ X1) ◇ (X1 ◇ (X2 ◇ X1))) := congrArg (· ◇ (X1 ◇ (X2 ◇ X1))) ((c_0_12 X1 X2 X3 (((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X1)))))).symm)
    _ = ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X1)))))) := c_0_7 ((X1 ◇ (X2 ◇ X1))) X3 X1
    _ = ((X1 ◇ (X2 ◇ X1)) ◇ ((X3 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1)) := congrArg ((X1 ◇ (X2 ◇ X1)) ◇ ·) ((c_0_3 ((X3 ◇ (X1 ◇ (X2 ◇ X1)))) X1 X2).symm)

theorem c_0_16 : ∀ (X1 X2 : G), (((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ X2) = (X2 ◇ (X2 ◇ (X2 ◇ X2))) := by
  intro X1 X2
  calc (((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ X2)
    _ = (X2 ◇ ((X2 ◇ X2) ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X2))) := (c_0_4 X2 (((X1 ◇ (X2 ◇ X2)) ◇ X2))).symm
    _ = (X2 ◇ (X2 ◇ (X2 ◇ X2))) := congrArg (X2 ◇ ·) (c_0_13 X2 X1)

theorem c_0_17 : ∀ (X1 X2 : G), ((X1 ◇ (X2 ◇ X1)) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) = (X1 ◇ (X1 ◇ (X2 ◇ X1))) := by
  intro X1 X2
  calc ((X1 ◇ (X2 ◇ X1)) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1))
    _ = ((X1 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X1 ◇ (X2 ◇ X1))) := (c_0_14 X1 ((X1 ◇ (X2 ◇ X1))) X2).symm
    _ = ((X1 ◇ (X2 ◇ X1)) ◇ (((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1)) := ((c_0_15 X1 X2 ((X1 ◇ (X2 ◇ X1)))).symm).symm
    _ = (X1 ◇ (X1 ◇ (X2 ◇ X1))) := ((c_0_4 ((X1 ◇ (X2 ◇ X1))) X1).symm).symm

theorem c_0_18 : ∀ (X1 X2 : G), (((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ (X1 ◇ X1))) := by
  intro X1 X2
  calc (((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ X1)
    _ = ((X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X1) := congrArg (· ◇ X1) ((c_0_4 X1 ((X1 ◇ (X2 ◇ X1)))).symm)
    _ = (((((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X1 ◇ X1)) ◇ X1) ◇ X1) := congrArg (· ◇ X1) ((c_0_12 X1 X2 X1 ((X1 ◇ X1))).symm)
    _ = (X1 ◇ (X1 ◇ (X1 ◇ X1))) := c_0_16 (((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1))))) X1

theorem c_0_19 : ∀ (X1 X2 X3 : G), (((X1 ◇ X1) ◇ X2) ◇ ((((X1 ◇ X1) ◇ X2) ◇ (X2 ◇ X1)) ◇ X3)) = (X3 ◇ ((X1 ◇ X1) ◇ X2)) := by
  intro X1 X2 X3
  calc (((X1 ◇ X1) ◇ X2) ◇ ((((X1 ◇ X1) ◇ X2) ◇ (X2 ◇ X1)) ◇ X3))
    _ = (((X1 ◇ X1) ◇ X2) ◇ ((((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))) ◇ X3)) := congrArg (((X1 ◇ X1) ◇ X2) ◇ ·) (congrArg (· ◇ X3) (congrArg (((X1 ◇ X1) ◇ X2) ◇ ·) ((c_0_4 X1 X2).symm)))
    _ = (X3 ◇ ((X1 ◇ X1) ◇ X2)) := (c_0_3 X3 (((X1 ◇ X1) ◇ X2)) X1).symm

theorem c_0_20 : ∀ (X1 X2 : G), (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) = (X1 ◇ (X1 ◇ (X1 ◇ X1))) := by
  intro X1 X2
  calc (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1))))
    _ = (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1))) := congrArg (X1 ◇ ·) ((c_0_17 X1 X2).symm)
    _ = (((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ X1) := (c_0_3 (((X1 ◇ (X2 ◇ X1)) ◇ X1)) X1 X2).symm
    _ = (X1 ◇ (X1 ◇ (X1 ◇ X1))) := ((c_0_18 X1 X2).symm).symm

theorem c_0_21 : ∀ (X1 : G), ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) = ((((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) := by
  intro X1
  calc ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))))
    _ = (((X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) := (c_0_16 X1 ((X1 ◇ X1))).symm
    _ = ((((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) := congrArg (· ◇ (X1 ◇ X1)) (congrArg (· ◇ (X1 ◇ X1)) (c_0_4 X1 ((X1 ◇ X1))))

theorem c_0_22 : ∀ (X1 : G), (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)))) = ((X1 ◇ X1) ◇ X1) := by
  intro X1
  calc (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X1))))
    _ = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ X1)) ◇ X1)) := congrArg (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ·) ((c_0_6 X1 (((X1 ◇ X1) ◇ X1))).symm)
    _ = (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := c_0_19 X1 ((X1 ◇ X1)) X1
    _ = ((X1 ◇ X1) ◇ X1) := ((c_0_4 X1 ((X1 ◇ X1))).symm).symm

theorem c_0_23 : ∀ (X1 X2 X3 : G), ((X1 ◇ ((X2 ◇ ((X1 ◇ X1) ◇ (X3 ◇ (X1 ◇ X1)))) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ X1)) := by
  intro X1 X2 X3
  calc ((X1 ◇ ((X2 ◇ ((X1 ◇ X1) ◇ (X3 ◇ (X1 ◇ X1)))) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1))
    _ = (((((X1 ◇ X1) ◇ (X3 ◇ (X1 ◇ X1))) ◇ (X2 ◇ ((X1 ◇ X1) ◇ (X3 ◇ (X1 ◇ X1))))) ◇ X1) ◇ (X1 ◇ X1)) := congrArg (· ◇ (X1 ◇ X1)) ((c_0_5 X1 X3 ((X2 ◇ ((X1 ◇ X1) ◇ (X3 ◇ (X1 ◇ X1)))))).symm)
    _ = ((X1 ◇ X1) ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X3 ◇ (X1 ◇ X1))))) := c_0_12 ((X1 ◇ X1)) X3 X2 X1
    _ = ((X1 ◇ X1) ◇ ((X3 ◇ (X1 ◇ X1)) ◇ X1)) := congrArg ((X1 ◇ X1) ◇ ·) (((c_0_4 X1 ((X3 ◇ (X1 ◇ X1)))).symm).symm)
    _ = (X1 ◇ (X1 ◇ X1)) := ((c_0_13 X1 X3).symm).symm

theorem c_0_24 : ∀ (X1 : G), ((X1 ◇ X1) ◇ ((((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) = ((((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) := by
  intro X1
  calc ((X1 ◇ X1) ◇ ((((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)))
    _ = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))))) := congrArg ((X1 ◇ X1) ◇ ·) ((c_0_21 X1).symm)
    _ = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) := c_0_20 ((X1 ◇ X1)) ((X1 ◇ X1))
    _ = ((((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) := ((c_0_21 X1).symm).symm

theorem c_0_25 : ∀ (X1 : G), ((X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) := by
  intro X1
  calc ((X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1))
    _ = ((X1 ◇ X1) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X1))))) := (c_0_4 ((X1 ◇ X1)) ((X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X1))))).symm
    _ = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) := congrArg ((X1 ◇ X1) ◇ ·) (c_0_22 X1)

theorem c_0_26 : ∀ (X1 X2 : G), ((X1 ◇ ((X2 ◇ ((((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ X1)) := by
  intro X1 X2
  calc ((X1 ◇ ((X2 ◇ ((((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1))
    _ = ((X1 ◇ ((X2 ◇ ((X1 ◇ X1) ◇ ((((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)))) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1)) := congrArg (· ◇ (X1 ◇ X1)) (congrArg (X1 ◇ ·) (congrArg (· ◇ (X1 ◇ X1)) (congrArg (X2 ◇ ·) ((c_0_24 X1).symm))))
    _ = (X1 ◇ (X1 ◇ X1)) := c_0_23 X1 X2 ((((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)))

theorem c_0_27 : ∀ (X1 X2 X3 : G), (X1 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) ◇ X3)) = (X3 ◇ X1) := by
  intro X1 X2 X3
  calc (X1 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) ◇ X3))
    _ = (X1 ◇ ((X1 ◇ ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X2) ◇ X1)) ◇ X3)) := congrArg (X1 ◇ ·) (congrArg (· ◇ X3) (congrArg (X1 ◇ ·) ((c_0_6 X1 X2).symm)))
    _ = (X3 ◇ X1) := (c_0_3 X3 X1 ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X2))).symm

theorem c_0_28 : ∀ (X1 : G), ((X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ X1)) := by
  intro X1
  calc ((X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1))
    _ = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) := ((c_0_25 X1).symm).symm
    _ = (X1 ◇ (X1 ◇ X1)) := c_0_10 X1

theorem c_0_29 : ∀ (X1 : G), (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ X1)) := by
  intro X1
  calc (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X1))
    _ = ((X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1)) := congrArg (· ◇ (X1 ◇ X1)) (c_0_3 ((X1 ◇ X1)) X1 X1)
    _ = ((X1 ◇ (((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1)) := congrArg (· ◇ (X1 ◇ X1)) (congrArg (X1 ◇ ·) (congrArg (· ◇ (X1 ◇ X1)) ((c_0_10 X1).symm)))
    _ = ((X1 ◇ ((((X1 ◇ X1) ◇ X1) ◇ ((((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1)) := congrArg (· ◇ (X1 ◇ X1)) (congrArg (X1 ◇ ·) (congrArg (· ◇ (X1 ◇ X1)) ((c_0_19 X1 X1 ((X1 ◇ X1))).symm)))
    _ = (X1 ◇ (X1 ◇ X1)) := c_0_26 X1 (((X1 ◇ X1) ◇ X1))

theorem c_0_30 : ∀ (X1 X2 : G), (X1 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X2)) = (X2 ◇ X1) := by
  intro X1 X2
  calc (X1 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X2))
    _ = (X1 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ X2)) := congrArg (X1 ◇ ·) (congrArg (· ◇ X2) ((c_0_20 X1 X1).symm))
    _ = (X2 ◇ X1) := c_0_27 X1 X1 X2

theorem c_0_31 : ∀ (X1 : G), ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ X1)) := by
  intro X1
  calc ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1))
    _ = ((X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1)) := congrArg (· ◇ (X1 ◇ X1)) (congrArg (X1 ◇ ·) ((c_0_29 X1).symm))
    _ = (X1 ◇ (X1 ◇ X1)) := c_0_28 X1

theorem c_0_32 : ∀ (X1 : G), (X1 ◇ (X1 ◇ (X1 ◇ X1))) = ((X1 ◇ X1) ◇ X1) := by
  intro X1
  calc (X1 ◇ (X1 ◇ (X1 ◇ X1)))
    _ = (X1 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1))) := congrArg (X1 ◇ ·) ((c_0_31 X1).symm)
    _ = ((X1 ◇ X1) ◇ X1) := c_0_30 X1 ((X1 ◇ X1))

theorem c_0_33 : ∀ (X1 X2 : G), (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) = ((X1 ◇ X1) ◇ X1) := by
  intro X1 X2
  calc (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1))))
    _ = (X1 ◇ (X1 ◇ (X1 ◇ X1))) := ((c_0_20 X1 X2).symm).symm
    _ = ((X1 ◇ X1) ◇ X1) := c_0_32 X1

theorem c_0_34 : ∀ (X1 : G), (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)))) = ((X1 ◇ X1) ◇ X1) := by
  intro X1
  calc (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))))
    _ = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ X1)) := congrArg (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ·) ((c_0_6 X1 (((X1 ◇ X1) ◇ (X1 ◇ X1)))).symm)
    _ = (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := c_0_4 (((X1 ◇ X1) ◇ (X1 ◇ X1))) X1
    _ = ((X1 ◇ X1) ◇ X1) := ((c_0_4 X1 ((X1 ◇ X1))).symm).symm

theorem c_0_35 : ∀ (X1 : G), ((X1 ◇ X1) ◇ X1) = (X1 ◇ X1) := by
  intro X1
  calc ((X1 ◇ X1) ◇ X1)
    _ = (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) := (c_0_33 X1 X1).symm
    _ = (X1 ◇ ((X1 ◇ X1) ◇ X1)) := congrArg (X1 ◇ ·) (c_0_32 X1)
    _ = (X1 ◇ X1) := ((c_0_4 X1 X1).symm).symm

theorem c_0_36 : ∀ (X1 : G), ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (X1 ◇ X1) := by
  intro X1
  calc ((X1 ◇ X1) ◇ (X1 ◇ X1))
    _ = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) := (c_0_35 ((X1 ◇ X1))).symm
    _ = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ X1)) := congrArg (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ·) ((c_0_35 X1).symm)
    _ = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) := congrArg (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ·) ((c_0_4 X1 ((X1 ◇ X1))).symm)
    _ = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)))) := congrArg (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ·) (congrArg (X1 ◇ ·) ((c_0_35 ((X1 ◇ X1))).symm))
    _ = ((X1 ◇ X1) ◇ X1) := ((c_0_34 X1).symm).symm
    _ = (X1 ◇ X1) := ((c_0_35 X1).symm).symm

theorem c_0_37 : ∀ (X1 : G), (X1 ◇ (X1 ◇ X1)) = (X1 ◇ X1) := by
  intro X1
  calc (X1 ◇ (X1 ◇ X1))
    _ = (X1 ◇ ((X1 ◇ X1) ◇ X1)) := congrArg (X1 ◇ ·) ((c_0_35 X1).symm)
    _ = (X1 ◇ X1) := c_0_4 X1 X1

theorem c_0_38 : ∀ (X1 X2 : G), ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X2)) = (X2 ◇ (X1 ◇ X1)) := by
  intro X1 X2
  calc ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X2))
    _ = ((X1 ◇ X1) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X2)) := congrArg ((X1 ◇ X1) ◇ ·) (congrArg (· ◇ X2) ((c_0_36 X1).symm))
    _ = (X2 ◇ (X1 ◇ X1)) := c_0_4 ((X1 ◇ X1)) X2

theorem c_0_39 : ∀ (X1 X2 : G), ((X1 ◇ X1) ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X1)) = (X1 ◇ X1) := by
  intro X1 X2
  calc ((X1 ◇ X1) ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X1))
    _ = (X1 ◇ (X1 ◇ X1)) := ((c_0_13 X1 X2).symm).symm
    _ = (X1 ◇ X1) := c_0_37 X1

theorem c_0_40 : ∀ (X1 X2 : G), (((X1 ◇ X1) ◇ X2) ◇ X1) = (X1 ◇ (X2 ◇ (X1 ◇ X1))) := by
  intro X1 X2
  calc (((X1 ◇ X1) ◇ X2) ◇ X1)
    _ = ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X2) ◇ X1) := congrArg (· ◇ X1) (congrArg (· ◇ X2) ((c_0_36 X1).symm))
    _ = (X1 ◇ (X2 ◇ (X1 ◇ X1))) := c_0_6 X1 X2

theorem c_0_41 : ∀ (X1 X2 : G), (((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))) ◇ (X1 ◇ (((X2 ◇ (X1 ◇ X1)) ◇ X1) ◇ (X1 ◇ X1)))) = ((X2 ◇ (X1 ◇ X1)) ◇ X1) := by
  intro X1 X2
  calc (((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))) ◇ (X1 ◇ (((X2 ◇ (X1 ◇ X1)) ◇ X1) ◇ (X1 ◇ X1))))
    _ = (((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))) ◇ ((((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))) ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X1)) ◇ X1)) := congrArg (((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))) ◇ ·) ((c_0_5 X1 X2 (((X2 ◇ (X1 ◇ X1)) ◇ X1))).symm)
    _ = (X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1)))) := c_0_19 X1 ((X2 ◇ (X1 ◇ X1))) X1
    _ = ((X2 ◇ (X1 ◇ X1)) ◇ X1) := ((c_0_4 X1 ((X2 ◇ (X1 ◇ X1)))).symm).symm

theorem c_0_42 : ∀ (X1 X2 : G), (((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ (X2 ◇ X2)) = (X2 ◇ X2) := by
  intro X1 X2
  calc (((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ (X2 ◇ X2))
    _ = ((X2 ◇ X2) ◇ ((X2 ◇ X2) ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X2))) := (c_0_38 X2 (((X1 ◇ (X2 ◇ X2)) ◇ X2))).symm
    _ = ((X2 ◇ X2) ◇ (X2 ◇ X2)) := congrArg ((X2 ◇ X2) ◇ ·) (c_0_39 X2 X1)
    _ = (X2 ◇ X2) := ((c_0_36 X2).symm).symm

theorem c_0_43 : ∀ (X1 X2 : G), (((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))) := by
  intro X1 X2
  calc (((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ X1))
    _ = ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X2) ◇ (X1 ◇ X1)) := congrArg (· ◇ (X1 ◇ X1)) (congrArg (· ◇ X2) ((c_0_36 X1).symm))
    _ = ((X1 ◇ X1) ◇ (X2 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) := c_0_40 ((X1 ◇ X1)) X2
    _ = ((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))) := congrArg ((X1 ◇ X1) ◇ ·) (congrArg (X2 ◇ ·) (((c_0_36 X1).symm).symm))

theorem c_0_44 : ∀ (X1 X2 : G), ((X1 ◇ X1) ◇ ((X2 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) = (X1 ◇ X1) := by
  intro X1 X2
  calc ((X1 ◇ X1) ◇ ((X2 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)))
    _ = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X2 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) := congrArg (· ◇ ((X2 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) ((c_0_36 X1).symm)
    _ = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X2 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1))) := congrArg (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ·) (congrArg (· ◇ (X1 ◇ X1)) (congrArg (X2 ◇ ·) ((c_0_36 X1).symm)))
    _ = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := ((c_0_39 ((X1 ◇ X1)) X2).symm).symm
    _ = (X1 ◇ X1) := ((c_0_36 X1).symm).symm

theorem c_0_45 : ∀ (X1 X2 X3 X4 : G), (((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ ((((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ (X3 ◇ X1)) ◇ X4)) = (X4 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X3)) := by
  intro X1 X2 X3 X4
  calc (((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ ((((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ (X3 ◇ X1)) ◇ X4))
    _ = (((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ ((((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X3))) ◇ X4)) := congrArg (((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ ·) (congrArg (· ◇ X4) (congrArg (((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ ·) (((c_0_3 X3 X1 X2).symm).symm)))
    _ = (X4 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X3)) := (c_0_3 X4 (((X1 ◇ (X2 ◇ X1)) ◇ X3)) X1).symm

theorem c_0_46 : ∀ (X1 X2 : G), ((X1 ◇ (X2 ◇ X2)) ◇ X2) = (X2 ◇ X2) := by
  intro X1 X2
  calc ((X1 ◇ (X2 ◇ X2)) ◇ X2)
    _ = (((X2 ◇ X2) ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X2 ◇ (((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ (X2 ◇ X2)))) := (c_0_41 X2 X1).symm
    _ = (((X2 ◇ X2) ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X2 ◇ (X2 ◇ X2))) := congrArg (((X2 ◇ X2) ◇ (X1 ◇ (X2 ◇ X2))) ◇ ·) (congrArg (X2 ◇ ·) (c_0_42 X1 X2))
    _ = (((X2 ◇ X2) ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X2 ◇ X2)) := congrArg (((X2 ◇ X2) ◇ (X1 ◇ (X2 ◇ X2))) ◇ ·) (c_0_37 X2)
    _ = ((X2 ◇ X2) ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X2))) := ((c_0_43 X2 ((X1 ◇ (X2 ◇ X2)))).symm).symm
    _ = (X2 ◇ X2) := ((c_0_44 X2 X1).symm).symm

theorem c_0_47 : ∀ (X1 X2 : G), (((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X1 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ (X1 ◇ (X2 ◇ X1))))) = ((X1 ◇ (X2 ◇ X1)) ◇ X1) := by
  intro X1 X2
  calc (((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X1 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ (X1 ◇ (X2 ◇ X1)))))
    _ = (((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) ◇ ((((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) ◇ X1)) := congrArg (((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) ◇ ·) ((c_0_7 X1 X2 (((X1 ◇ (X2 ◇ X1)) ◇ X1))).symm)
    _ = (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1)))) := c_0_45 X1 X2 ((X1 ◇ (X2 ◇ X1))) X1
    _ = ((X1 ◇ (X2 ◇ X1)) ◇ X1) := (c_0_3 ((X1 ◇ (X2 ◇ X1))) X1 X2).symm

theorem c_0_48 : ∀ (X1 X2 : G), ((X1 ◇ (X2 ◇ X1)) ◇ X1) = (X1 ◇ X1) := by
  intro X1 X2
  calc ((X1 ◇ (X2 ◇ X1)) ◇ X1)
    _ = (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ X1)))) := (c_0_4 X1 ((X1 ◇ (X2 ◇ X1)))).symm
    _ = ((((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X1 ◇ X1)) ◇ X1) := (c_0_12 X1 X2 X1 ((X1 ◇ X1))).symm
    _ = (X1 ◇ X1) := c_0_46 (((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1))))) X1

theorem c_0_49 : ∀ (X1 X2 : G), (((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X1 ◇ X1)) = (X1 ◇ X1) := by
  intro X1 X2
  calc (((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X1 ◇ X1))
    _ = (((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) := congrArg (((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) ◇ ·) ((c_0_48 X1 X2).symm)
    _ = (((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ X1))))) := congrArg (((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) ◇ ·) ((c_0_4 X1 ((X1 ◇ (X2 ◇ X1)))).symm)
    _ = (((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X1 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ (X1 ◇ (X2 ◇ X1))))) := congrArg (((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) ◇ ·) (congrArg (X1 ◇ ·) (congrArg (· ◇ (X1 ◇ (X2 ◇ X1))) ((c_0_48 X1 X2).symm)))
    _ = ((X1 ◇ (X2 ◇ X1)) ◇ X1) := ((c_0_47 X1 X2).symm).symm
    _ = (X1 ◇ X1) := ((c_0_48 X1 X2).symm).symm

theorem c_0_50 : ∀ (X1 X2 : G), ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ (X2 ◇ X1))) := by
  intro X1 X2
  calc ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X1))
    _ = ((X1 ◇ (X2 ◇ X1)) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) := congrArg ((X1 ◇ (X2 ◇ X1)) ◇ ·) ((c_0_48 X1 X2).symm)
    _ = (X1 ◇ (X1 ◇ (X2 ◇ X1))) := c_0_17 X1 X2

theorem c_0_51 : ∀ (X1 X2 : G), ((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ X1))) = (X1 ◇ (X1 ◇ (X2 ◇ X1))) := by
  intro X1 X2
  calc ((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ X1)))
    _ = ((X1 ◇ (X2 ◇ X1)) ◇ (((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X1 ◇ X1))) := (c_0_4 ((X1 ◇ (X2 ◇ X1))) ((X1 ◇ X1))).symm
    _ = ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X1)) := congrArg ((X1 ◇ (X2 ◇ X1)) ◇ ·) (c_0_49 X1 X2)
    _ = (X1 ◇ (X1 ◇ (X2 ◇ X1))) := ((c_0_50 X1 X2).symm).symm

theorem c_0_52 : ∀ (X1 X2 : G), ((X1 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X2)) = (X2 ◇ X2) := by
  intro X1 X2
  calc ((X1 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X2))
    _ = ((X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) ◇ (X2 ◇ X2)) := congrArg (· ◇ (X2 ◇ X2)) (congrArg (X1 ◇ ·) ((c_0_36 X2).symm))
    _ = ((X2 ◇ X2) ◇ (X2 ◇ X2)) := c_0_46 X1 ((X2 ◇ X2))
    _ = (X2 ◇ X2) := ((c_0_36 X2).symm).symm

theorem c_0_53 : ∀ (X1 X2 : G), ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) = (X1 ◇ (X1 ◇ (X2 ◇ X1))) := by
  intro X1 X2
  calc ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1))))
    _ = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ X1)))) := congrArg ((X1 ◇ X1) ◇ ·) ((c_0_51 X1 X2).symm)
    _ = ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X1)) := c_0_38 X1 ((X1 ◇ (X2 ◇ X1)))
    _ = (X1 ◇ (X1 ◇ (X2 ◇ X1))) := ((c_0_50 X1 X2).symm).symm

theorem c_0_54 : ∀ (X1 X2 : G), ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X1 ◇ X1)) = (X1 ◇ X1) := by
  intro X1 X2
  calc ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X1 ◇ X1))
    _ = (((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) := congrArg (· ◇ (X1 ◇ X1)) ((c_0_50 X1 X2).symm)
    _ = (X1 ◇ X1) := c_0_52 ((X1 ◇ (X2 ◇ X1))) X1

theorem c_0_55 : ∀ (X1 X2 : G), (X1 ◇ (X1 ◇ (X2 ◇ X1))) = (X1 ◇ X1) := by
  intro X1 X2
  calc (X1 ◇ (X1 ◇ (X2 ◇ X1)))
    _ = ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) := (c_0_53 X1 X2).symm
    _ = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1))))) := congrArg ((X1 ◇ X1) ◇ ·) ((c_0_53 X1 X2).symm)
    _ = ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X1 ◇ X1)) := ((c_0_38 X1 ((X1 ◇ (X1 ◇ (X2 ◇ X1))))).symm).symm
    _ = (X1 ◇ X1) := ((c_0_54 X1 X2).symm).symm

theorem c_0_56 : ∀ (X1 X2 : G), ((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ X1))) = (X1 ◇ X1) := by
  intro X1 X2
  calc ((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ X1)))
    _ = (X1 ◇ (X1 ◇ (X2 ◇ X1))) := ((c_0_51 X1 X2).symm).symm
    _ = (X1 ◇ X1) := c_0_55 X1 X2

theorem c_0_57 : ∀ (X1 X2 : G), ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) = (X1 ◇ X1) := by
  intro X1 X2
  calc ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1)))
    _ = ((X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X1 ◇ (X2 ◇ X1))) := (c_0_46 X1 ((X1 ◇ (X2 ◇ X1)))).symm
    _ = (((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ (X1 ◇ (X2 ◇ X1))) := congrArg (· ◇ (X1 ◇ (X2 ◇ X1))) ((c_0_3 ((X1 ◇ (X2 ◇ X1))) X1 X2).symm)
    _ = ((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ X1))) := congrArg (· ◇ (X1 ◇ (X2 ◇ X1))) (((c_0_48 X1 X2).symm).symm)
    _ = (X1 ◇ X1) := ((c_0_56 X1 X2).symm).symm

theorem c_0_58 : ∀ (X1 X2 X3 : G), ((X1 ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X3 ◇ X2))) = (X2 ◇ X2) := by
  intro X1 X2 X3
  calc ((X1 ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X3 ◇ X2)))
    _ = ((X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ (X2 ◇ (X3 ◇ X2)))) ◇ (X2 ◇ (X3 ◇ X2))) := congrArg (· ◇ (X2 ◇ (X3 ◇ X2))) (congrArg (X1 ◇ ·) ((c_0_57 X2 X3).symm))
    _ = ((X2 ◇ (X3 ◇ X2)) ◇ (X2 ◇ (X3 ◇ X2))) := c_0_46 X1 ((X2 ◇ (X3 ◇ X2)))
    _ = (X2 ◇ X2) := ((c_0_57 X2 X3).symm).symm

theorem c_0_59 : ∀ (X1 X2 X3 : G), ((X1 ◇ (X2 ◇ X2)) ◇ ((X2 ◇ X2) ◇ (X3 ◇ (X2 ◇ X2)))) = (X2 ◇ X2) := by
  intro X1 X2 X3
  calc ((X1 ◇ (X2 ◇ X2)) ◇ ((X2 ◇ X2) ◇ (X3 ◇ (X2 ◇ X2))))
    _ = ((X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) ◇ ((X2 ◇ X2) ◇ (X3 ◇ (X2 ◇ X2)))) := congrArg (· ◇ ((X2 ◇ X2) ◇ (X3 ◇ (X2 ◇ X2)))) (congrArg (X1 ◇ ·) ((c_0_36 X2).symm))
    _ = ((X2 ◇ X2) ◇ (X2 ◇ X2)) := c_0_58 X1 ((X2 ◇ X2)) X3
    _ = (X2 ◇ X2) := ((c_0_36 X2).symm).symm

theorem c_0_60 : ∀ (X1 X2 : G),
    ((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ (X2 ◇ X2))) = (X2 ◇ X2) := by
  intro X1 X2
  calc
    (X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ (X2 ◇ X2)) =
        (((X1 ◇ (X2 ◇ X2)) ◇ ((X2 ◇ X2) ◇ (X1 ◇ (X2 ◇ X2)))) ◇
          ((X1 ◇ (X2 ◇ X2)) ◇ ((X2 ◇ X2) ◇ (X1 ◇ (X2 ◇ X2))))) :=
      (c_0_57 (X1 ◇ (X2 ◇ X2)) (X2 ◇ X2)).symm
    _ = (X2 ◇ X2) ◇ (X2 ◇ X2) :=
      congrArg (fun t => t ◇ t) (c_0_59 X1 X2 X1)
    _ = X2 ◇ X2 := c_0_36 X2

theorem c_0_61 : ∀ (X1 X2 X3 : G), ((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ (X2 ◇ X2))) = (X2 ◇ X2) := by
  intro X1 X2 X3
  calc ((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ (X2 ◇ X2)))
    _ = ((X1 ◇ ((X3 ◇ (X2 ◇ X2)) ◇ (X3 ◇ (X2 ◇ X2)))) ◇ (X3 ◇ (X2 ◇ X2))) := congrArg (· ◇ (X3 ◇ (X2 ◇ X2))) (congrArg (X1 ◇ ·) ((c_0_60 X3 X2).symm))
    _ = ((X3 ◇ (X2 ◇ X2)) ◇ (X3 ◇ (X2 ◇ X2))) := c_0_46 X1 ((X3 ◇ (X2 ◇ X2)))
    _ = (X2 ◇ X2) := ((c_0_60 X3 X2).symm).symm

theorem c_0_62 : ∀ (X1 X2 X3 : G), ((X1 ◇ (X2 ◇ X2)) ◇ ((X2 ◇ X2) ◇ X3)) = (X3 ◇ (X1 ◇ (X2 ◇ X2))) := by
  intro X1 X2 X3
  calc ((X1 ◇ (X2 ◇ X2)) ◇ ((X2 ◇ X2) ◇ X3))
    _ = ((X1 ◇ (X2 ◇ X2)) ◇ (((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ (X2 ◇ X2))) ◇ X3)) := congrArg ((X1 ◇ (X2 ◇ X2)) ◇ ·) (congrArg (· ◇ X3) ((c_0_61 X1 X2 X1).symm))
    _ = (X3 ◇ (X1 ◇ (X2 ◇ X2))) := c_0_4 ((X1 ◇ (X2 ◇ X2))) X3

theorem c_0_63 : ∀ (X1 X2 : G), (X1 ◇ (X2 ◇ (X1 ◇ X1))) = (X1 ◇ X1) := by
  intro X1 X2
  calc (X1 ◇ (X2 ◇ (X1 ◇ X1)))
    _ = ((X2 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ X1)) := (c_0_62 X2 X1 X1).symm
    _ = ((X2 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) := congrArg ((X2 ◇ (X1 ◇ X1)) ◇ ·) (c_0_35 X1)
    _ = (X1 ◇ X1) := ((c_0_52 X2 X1).symm).symm

theorem c_0_64 : ∀ (X1 X2 : G), (((X1 ◇ X1) ◇ X2) ◇ X1) = (X1 ◇ X1) := by
  intro X1 X2
  calc (((X1 ◇ X1) ◇ X2) ◇ X1)
    _ = (X1 ◇ (X2 ◇ (X1 ◇ X1))) := ((c_0_40 X1 X2).symm).symm
    _ = (X1 ◇ X1) := c_0_63 X1 X2

theorem c_0_65 : ∀ (X1 X2 X3 : G), (((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ (X1 ◇ X1))) = (X1 ◇ X1) := by
  intro X1 X2 X3
  calc (((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ (X1 ◇ X1)))
    _ = ((((X3 ◇ (X1 ◇ X1)) ◇ (X3 ◇ (X1 ◇ X1))) ◇ X2) ◇ (X3 ◇ (X1 ◇ X1))) := congrArg (· ◇ (X3 ◇ (X1 ◇ X1))) (congrArg (· ◇ X2) ((c_0_61 X3 X1 X3).symm))
    _ = ((X3 ◇ (X1 ◇ X1)) ◇ (X3 ◇ (X1 ◇ X1))) := c_0_64 ((X3 ◇ (X1 ◇ X1))) X2
    _ = (X1 ◇ X1) := ((c_0_61 X3 X1 X3).symm).symm

theorem c_0_67 : ∀ (X1 X2 : G), (X1 ◇ (X2 ◇ X2)) = (X2 ◇ X2) := by
  intro X1 X2
  calc (X1 ◇ (X2 ◇ X2))
    _ = ((X2 ◇ X2) ◇ ((X2 ◇ X2) ◇ X1)) := (c_0_38 X2 X1).symm
    _ = (((X2 ◇ X2) ◇ X1) ◇ ((((X2 ◇ X2) ◇ X1) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X1))) ◇ (X2 ◇ X2))) := c_0_3 ((X2 ◇ X2)) (((X2 ◇ X2) ◇ X1)) X1
    _ = (X2 ◇ X2) := c_0_65 X2 X1 ((((X2 ◇ X2) ◇ X1) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X1))))

theorem c_0_69 : ∀ (X1 X2 : G), ((X1 ◇ X1) ◇ X2) = (X2 ◇ X2) := by
  intro X1 X2
  calc ((X1 ◇ X1) ◇ X2)
    _ = (((X2 ◇ X2) ◇ (X1 ◇ X1)) ◇ X2) := congrArg (· ◇ X2) ((c_0_67 ((X2 ◇ X2)) X1).symm)
    _ = (X2 ◇ X2) := c_0_64 X2 ((X1 ◇ X1))

theorem c_0_71 : ∀ (X1 X2 : G), (X1 ◇ X1) = (X1 ◇ X2) := by
  intro X1 X2
  calc (X1 ◇ X1)
    _ = (X2 ◇ (X1 ◇ X1)) := (c_0_67 X2 X1).symm
    _ = (X2 ◇ ((X2 ◇ X2) ◇ X1)) := congrArg (X2 ◇ ·) ((c_0_69 X2 X1).symm)
    _ = (X1 ◇ X2) := ((c_0_4 X2 X1).symm).symm

theorem compactInterface :
    (∀ (a b : G), a ◇ a = a ◇ b) ∧
    (∀ (a b : G), a ◇ (b ◇ b) = b ◇ b) := by
  exact ⟨c_0_71, c_0_67⟩

end Equation44575Kernel

end

end submission

open submission
                   
                          

def submission : Goal := by
  intro G _ h
  letI : Equation44575Kernel.Law G := ⟨h⟩
  rcases Equation44575Kernel.compactInterface (G := G) with
    ⟨rightConstant, squareAbsorb⟩
  intro x y
  calc
    x ◇ (y ◇ x) = x ◇ x := (rightConstant x (y ◇ x)).symm
    _ = x ◇ (y ◇ y) := rightConstant x (y ◇ y)
    _ = y ◇ y := squareAbsorb x y
    _ = y ◇ (y ◇ y) := (squareAbsorb y y).symm
    _ = y ◇ (x ◇ (y ◇ y)) :=
      congrArg (fun t => y ◇ t) (squareAbsorb x y).symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_44575_to_54051 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_44575_to_54051
