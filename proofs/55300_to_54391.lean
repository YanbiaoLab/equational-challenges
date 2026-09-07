-- Equation55300 → Equation54391
-- Recorded verdict: true
-- Premise: x ◇ (y ◇ z) = y ◇ ((z ◇ x) ◇ x)
-- Conclusion: x ◇ (y ◇ z) = y ◇ (x ◇ (x ◇ z))
-- Original submission SHA-256: fc9683424dabd5e3ab2371b6c17e2fea2a41c746a48eb5454afe8defd309beed
-- Aurora-accepted correction SHA-256: ab3d86ed6d09f3c9f9a2fa0e17c24e655718444bff9a98ce80e98b09db9995e1
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ z) = y ◇ ((z ◇ x) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ z) = y ◇ (x ◇ (x ◇ z))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Aurora-accepted corrected submission body
                   

namespace submission

                       

namespace Equation55300Kernel

class Law (G : Type) [Magma G] : Prop where
  eq55300 : ∀ (x y z : G), x ◇ (y ◇ z) = y ◇ ((z ◇ x) ◇ x)

variable {G : Type} [Magma G] [Law G]

abbrev h := Law.eq55300 (G := G)

set_option linter.unusedVariables false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

theorem c_0_3 : ∀ (X1 X2 X3 : G), (X1 ◇ (X2 ◇ X3)) = (X2 ◇ ((X3 ◇ X1) ◇ X1)) := by
  intro X1 X2 X3
  exact h X1 X2 X3

theorem c_0_4 : ∀ (X1 X2 X3 X4 : G), (X1 ◇ (X2 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X4))) = (((X4 ◇ X2) ◇ X2) ◇ (X1 ◇ X3)) := by
  intro X1 X2 X3 X4
  calc (X1 ◇ (X2 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X4)))
    _ = (X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ ((X4 ◇ X2) ◇ X2))) := congrArg (X1 ◇ ·) (c_0_3 X2 ((X2 ◇ (X3 ◇ X4))) X4)
    _ = (X1 ◇ ((X3 ◇ ((X4 ◇ X2) ◇ X2)) ◇ ((X4 ◇ X2) ◇ X2))) := congrArg (X1 ◇ ·) (congrArg (· ◇ ((X4 ◇ X2) ◇ X2)) (c_0_3 X2 X3 X4))
    _ = (((X4 ◇ X2) ◇ X2) ◇ (X1 ◇ X3)) := (c_0_3 (((X4 ◇ X2) ◇ X2)) X1 X3).symm

theorem c_0_5 : ∀ (X1 X2 X3 X4 : G), (X1 ◇ (X2 ◇ ((X3 ◇ (X2 ◇ X4)) ◇ X3))) = (((X3 ◇ X2) ◇ X2) ◇ (X1 ◇ (X4 ◇ X3))) := by
  intro X1 X2 X3 X4
  calc (X1 ◇ (X2 ◇ ((X3 ◇ (X2 ◇ X4)) ◇ X3)))
    _ = (X1 ◇ (X2 ◇ ((X2 ◇ ((X4 ◇ X3) ◇ X3)) ◇ X3))) := congrArg (X1 ◇ ·) (congrArg (X2 ◇ ·) (congrArg (· ◇ X3) (((c_0_3 X3 X2 X4).symm).symm)))
    _ = (((X3 ◇ X2) ◇ X2) ◇ (X1 ◇ (X4 ◇ X3))) := c_0_4 X1 X2 ((X4 ◇ X3)) X3

theorem c_0_6 : ∀ (X1 X2 X3 X4 : G), (X1 ◇ (X2 ◇ ((X3 ◇ (X2 ◇ (X4 ◇ X3))) ◇ X3))) = (((X3 ◇ X2) ◇ X2) ◇ (X3 ◇ (X1 ◇ X4))) := by
  intro X1 X2 X3 X4
  calc (X1 ◇ (X2 ◇ ((X3 ◇ (X2 ◇ (X4 ◇ X3))) ◇ X3)))
    _ = (((X3 ◇ X2) ◇ X2) ◇ (X1 ◇ ((X4 ◇ X3) ◇ X3))) := ((c_0_5 X1 X2 X3 ((X4 ◇ X3))).symm).symm
    _ = (((X3 ◇ X2) ◇ X2) ◇ (X3 ◇ (X1 ◇ X4))) := congrArg (((X3 ◇ X2) ◇ X2) ◇ ·) ((c_0_3 X3 X1 X4).symm)

theorem c_0_7 : ∀ (X1 X2 X3 X4 : G), (X1 ◇ (X2 ◇ ((X3 ◇ (X3 ◇ (X2 ◇ X4))) ◇ X3))) = (((X3 ◇ X2) ◇ X2) ◇ (X3 ◇ (X1 ◇ (X4 ◇ X3)))) := by
  intro X1 X2 X3 X4
  calc (X1 ◇ (X2 ◇ ((X3 ◇ (X3 ◇ (X2 ◇ X4))) ◇ X3)))
    _ = (X1 ◇ (X2 ◇ ((X3 ◇ (X2 ◇ ((X4 ◇ X3) ◇ X3))) ◇ X3))) := congrArg (X1 ◇ ·) (congrArg (X2 ◇ ·) (congrArg (· ◇ X3) (congrArg (X3 ◇ ·) (((c_0_3 X3 X2 X4).symm).symm))))
    _ = (((X3 ◇ X2) ◇ X2) ◇ (X3 ◇ (X1 ◇ (X4 ◇ X3)))) := c_0_6 X1 X2 X3 ((X4 ◇ X3))

theorem c_0_8 : ∀ (X1 X2 X3 X4 : G), (X1 ◇ (X2 ◇ ((X3 ◇ (X2 ◇ (X1 ◇ (X4 ◇ X3)))) ◇ X3))) = (((X3 ◇ X1) ◇ X1) ◇ (((X3 ◇ X2) ◇ X2) ◇ X4)) := by
  intro X1 X2 X3 X4
  calc (X1 ◇ (X2 ◇ ((X3 ◇ (X2 ◇ (X1 ◇ (X4 ◇ X3)))) ◇ X3)))
    _ = (((X3 ◇ X2) ◇ X2) ◇ (X1 ◇ ((X1 ◇ (X4 ◇ X3)) ◇ X3))) := ((c_0_5 X1 X2 X3 ((X1 ◇ (X4 ◇ X3)))).symm).symm
    _ = (((X3 ◇ X1) ◇ X1) ◇ (((X3 ◇ X2) ◇ X2) ◇ X4)) := c_0_4 (((X3 ◇ X2) ◇ X2)) X1 X4 X3

theorem c_0_9 : ∀ (X1 X2 X3 X4 : G), (X1 ◇ (X2 ◇ ((X3 ◇ (X3 ◇ (X2 ◇ (X4 ◇ X3)))) ◇ X3))) = (((X3 ◇ X2) ◇ X2) ◇ (X3 ◇ (X3 ◇ (X1 ◇ X4)))) := by
  intro X1 X2 X3 X4
  calc (X1 ◇ (X2 ◇ ((X3 ◇ (X3 ◇ (X2 ◇ (X4 ◇ X3)))) ◇ X3)))
    _ = (((X3 ◇ X2) ◇ X2) ◇ (X3 ◇ (X1 ◇ ((X4 ◇ X3) ◇ X3)))) := ((c_0_7 X1 X2 X3 ((X4 ◇ X3))).symm).symm
    _ = (((X3 ◇ X2) ◇ X2) ◇ (X3 ◇ (X3 ◇ (X1 ◇ X4)))) := congrArg (((X3 ◇ X2) ◇ X2) ◇ ·) (congrArg (X3 ◇ ·) ((c_0_3 X3 X1 X4).symm))

theorem c_0_10 : ∀ (X1 X2 : G), (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) = (X1 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1))) := by
  intro X1 X2
  calc (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1))))
    _ = (X2 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1))) := (c_0_7 X2 X1 X1 X1).symm
    _ = (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ (X2 ◇ X1))) := c_0_6 X2 X1 X1 X1
    _ = (X1 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1))) := (c_0_5 X1 X1 X1 X2).symm

theorem c_0_11 : ∀ (X1 X2 : G), (((X1 ◇ X1) ◇ X1) ◇ (((X1 ◇ X1) ◇ X1) ◇ X2)) = (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) := by
  intro X1 X2
  calc (((X1 ◇ X1) ◇ X1) ◇ (((X1 ◇ X1) ◇ X1) ◇ X2))
    _ = (X1 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X1))) := (c_0_8 X1 X1 X1 X2).symm
    _ = (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) := c_0_9 X1 X1 X1 X2

theorem c_0_12 : ∀ (X1 X2 : G), (((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))) = (((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ X1)) := by
  intro X1 X2
  calc (((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ (X1 ◇ X1)))
    _ = (X2 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1))) := (c_0_5 X2 X1 X1 X1).symm
    _ = (((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ X1)) := c_0_4 X2 X1 X1 X1

theorem c_0_13 : ∀ (X1 X2 : G), (X1 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) ◇ X1))) = (((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X2))) := by
  intro X1 X2
  calc (X1 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) ◇ X1)))
    _ = (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)))) := (c_0_10 X1 ((X2 ◇ (X1 ◇ X1)))).symm
    _ = (((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X2))) := congrArg (((X1 ◇ X1) ◇ X1) ◇ ·) ((c_0_3 ((X1 ◇ X1)) X1 X2).symm)

theorem c_0_14 : ∀ (X1 : G), (X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X1))) = (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) := by
  intro X1
  calc (X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)))
    _ = (((X1 ◇ X1) ◇ X1) ◇ (((X1 ◇ X1) ◇ X1) ◇ X1)) := c_0_3 X1 (((X1 ◇ X1) ◇ X1)) ((X1 ◇ X1))
    _ = (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) := c_0_11 X1 X1
    _ = (X1 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1))) := ((c_0_10 X1 X1).symm).symm
    _ = (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) := ((c_0_4 X1 X1 X1 X1).symm).symm

theorem c_0_15 : ∀ (X1 X2 X3 : G), (X1 ◇ ((((X2 ◇ X2) ◇ X2) ◇ (X3 ◇ X2)) ◇ (X3 ◇ (X2 ◇ X2)))) = ((X3 ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X1 ◇ X2))) := by
  intro X1 X2 X3
  calc (X1 ◇ ((((X2 ◇ X2) ◇ X2) ◇ (X3 ◇ X2)) ◇ (X3 ◇ (X2 ◇ X2))))
    _ = (X1 ◇ ((((X2 ◇ X2) ◇ X2) ◇ (X3 ◇ (X2 ◇ X2))) ◇ (X3 ◇ (X2 ◇ X2)))) := congrArg (X1 ◇ ·) (congrArg (· ◇ (X3 ◇ (X2 ◇ X2))) ((c_0_12 X2 X3).symm))
    _ = ((X3 ◇ (X2 ◇ X2)) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X2))) := (c_0_3 ((X3 ◇ (X2 ◇ X2))) X1 (((X2 ◇ X2) ◇ X2))).symm
    _ = ((X3 ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X1 ◇ X2))) := congrArg ((X3 ◇ (X2 ◇ X2)) ◇ ·) ((c_0_3 X2 X1 X2).symm)

theorem c_0_16 : ∀ (X1 : G), (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ (X1 ◇ X1))) := by
  intro X1
  calc (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X1))
    _ = (X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X1))) := (c_0_14 X1).symm
    _ = (((X1 ◇ X1) ◇ X1) ◇ (((X1 ◇ X1) ◇ X1) ◇ X1)) := c_0_3 X1 (((X1 ◇ X1) ◇ X1)) ((X1 ◇ X1))
    _ = (X1 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ X1))) := (c_0_8 X1 X1 X1 X1).symm
    _ = (((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := c_0_13 X1 X1
    _ = (((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) := ((c_0_12 X1 ((X1 ◇ X1))).symm).symm
    _ = (X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ X1)) := (c_0_3 X1 (((X1 ◇ X1) ◇ X1)) X1).symm
    _ = (X1 ◇ (X1 ◇ (X1 ◇ X1))) := (c_0_3 X1 X1 ((X1 ◇ X1))).symm

theorem c_0_17 : ∀ (X1 X2 : G), ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) = ((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X1)) := by
  intro X1 X2
  calc ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1)))
    _ = (X2 ◇ ((((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1)))) := (c_0_15 X2 X1 X1).symm
    _ = (X2 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ (X1 ◇ X1)))) := congrArg (X2 ◇ ·) (congrArg (· ◇ (X1 ◇ (X1 ◇ X1))) (c_0_16 X1))
    _ = ((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X1)) := (c_0_3 ((X1 ◇ (X1 ◇ X1))) X2 X1).symm

theorem c_0_18 : ∀ (X1 X2 : G), ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X2))) = (X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2)) := by
  intro X1 X2
  calc ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X2)))
    _ = ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) := congrArg ((X1 ◇ (X1 ◇ X1)) ◇ ·) (c_0_3 X1 X1 X2)
    _ = ((X1 ◇ (X1 ◇ X1)) ◇ ((X2 ◇ X1) ◇ X1)) := c_0_17 X1 ((X2 ◇ X1))
    _ = (X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2)) := (c_0_3 X1 ((X1 ◇ (X1 ◇ X1))) X2).symm

theorem c_0_19 : ∀ (X1 : G), ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) = (X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1)) := by
  intro X1
  calc ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))
    _ = ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))) := (c_0_17 X1 X1).symm
    _ = (X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1)) := c_0_18 X1 X1

theorem c_0_20 : ∀ (X1 X2 : G), (((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ X1)) = ((X1 ◇ X1) ◇ (X2 ◇ X1)) := by
  intro X1 X2
  calc (((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ X1))
    _ = (X2 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1))) := (c_0_4 X2 X1 X1 X1).symm
    _ = (X2 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) := congrArg (X2 ◇ ·) ((c_0_19 X1).symm)
    _ = ((X1 ◇ X1) ◇ (X2 ◇ X1)) := (c_0_3 ((X1 ◇ X1)) X2 X1).symm

theorem c_0_21 : ∀ (X1 X2 : G), (X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ X2)) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := by
  intro X1 X2
  calc (X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ X2))
    _ = (((X1 ◇ X1) ◇ X1) ◇ ((X2 ◇ X1) ◇ X1)) := c_0_3 X1 (((X1 ◇ X1) ◇ X1)) X2
    _ = ((X1 ◇ X1) ◇ ((X2 ◇ X1) ◇ X1)) := c_0_20 X1 ((X2 ◇ X1))
    _ = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := (c_0_3 X1 ((X1 ◇ X1)) X2).symm

theorem c_0_22 : ∀ (X1 X2 : G), (X1 ◇ ((X2 ◇ (X2 ◇ (X2 ◇ X2))) ◇ (X2 ◇ X2))) = ((X2 ◇ X2) ◇ (X2 ◇ (X1 ◇ X2))) := by
  intro X1 X2
  calc (X1 ◇ ((X2 ◇ (X2 ◇ (X2 ◇ X2))) ◇ (X2 ◇ X2)))
    _ = (X1 ◇ ((((X2 ◇ X2) ◇ X2) ◇ (X2 ◇ X2)) ◇ (X2 ◇ X2))) := congrArg (X1 ◇ ·) (congrArg (· ◇ (X2 ◇ X2)) ((c_0_16 X2).symm))
    _ = ((X2 ◇ X2) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X2))) := (c_0_3 ((X2 ◇ X2)) X1 (((X2 ◇ X2) ◇ X2))).symm
    _ = ((X2 ◇ X2) ◇ (X2 ◇ (X1 ◇ X2))) := congrArg ((X2 ◇ X2) ◇ ·) ((c_0_3 X2 X1 X2).symm)

theorem c_0_23 : ∀ (X1 : G), (X1 ◇ (X1 ◇ (X1 ◇ X1))) = (X1 ◇ (X1 ◇ X1)) := by
  intro X1
  calc (X1 ◇ (X1 ◇ (X1 ◇ X1)))
    _ = (X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ X1)) := c_0_3 X1 X1 ((X1 ◇ X1))
    _ = (X1 ◇ ((X1 ◇ X1) ◇ X1)) := c_0_21 X1 X1
    _ = (X1 ◇ (X1 ◇ X1)) := (c_0_3 X1 X1 X1).symm

theorem c_0_24 : ∀ (X1 : G), ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ (X1 ◇ X1))) := by
  intro X1
  calc ((X1 ◇ X1) ◇ (X1 ◇ X1))
    _ = (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) := (c_0_20 X1 X1).symm
    _ = (X1 ◇ (X1 ◇ (X1 ◇ X1))) := c_0_16 X1

theorem c_0_25 : ∀ (X1 X2 : G), ((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ X1))) = ((X1 ◇ X1) ◇ (X2 ◇ X1)) := by
  intro X1 X2
  calc ((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ X1)))
    _ = (X2 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1))) := (c_0_22 X2 X1).symm
    _ = (X2 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) := congrArg (X2 ◇ ·) (congrArg (· ◇ (X1 ◇ X1)) (c_0_23 X1))
    _ = (X2 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1))) := congrArg (X2 ◇ ·) (c_0_19 X1)
    _ = (((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ X1)) := ((c_0_4 X2 X1 X1 X1).symm).symm
    _ = ((X1 ◇ X1) ◇ (X2 ◇ X1)) := ((c_0_20 X1 X2).symm).symm

theorem c_0_26 : ∀ (X1 : G), ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ X1)) := by
  intro X1
  calc ((X1 ◇ X1) ◇ (X1 ◇ X1))
    _ = (X1 ◇ (X1 ◇ (X1 ◇ X1))) := ((c_0_24 X1).symm).symm
    _ = (X1 ◇ (X1 ◇ X1)) := c_0_23 X1

theorem c_0_27 : ∀ (X1 X2 : G), ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := by
  intro X1 X2
  calc ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2)))
    _ = ((X1 ◇ X1) ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) := congrArg ((X1 ◇ X1) ◇ ·) (c_0_3 X1 X1 X2)
    _ = ((X1 ◇ X1) ◇ ((X2 ◇ X1) ◇ X1)) := c_0_25 X1 ((X2 ◇ X1))
    _ = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := (c_0_3 X1 ((X1 ◇ X1)) X2).symm

theorem c_0_28 : ∀ (X1 X2 : G), (((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))) = ((X1 ◇ X1) ◇ (X2 ◇ X1)) := by
  intro X1 X2
  calc (((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ (X1 ◇ X1)))
    _ = (((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ X1)) := ((c_0_12 X1 X2).symm).symm
    _ = ((X1 ◇ X1) ◇ (X2 ◇ X1)) := c_0_20 X1 X2

theorem c_0_29 : ∀ (X1 X2 X3 : G), ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X2))) = ((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ X2))) := by
  intro X1 X2 X3
  calc ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X2)))
    _ = (X3 ◇ (((X2 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) := c_0_3 ((X1 ◇ X2)) X3 ((X2 ◇ X2))
    _ = (X3 ◇ ((((X2 ◇ X2) ◇ X2) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) := congrArg (X3 ◇ ·) (congrArg (· ◇ (X1 ◇ X2)) ((c_0_20 X2 X1).symm))
    _ = ((X1 ◇ X2) ◇ (X3 ◇ ((X2 ◇ X2) ◇ X2))) := (c_0_3 ((X1 ◇ X2)) X3 (((X2 ◇ X2) ◇ X2))).symm
    _ = ((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ X2))) := congrArg ((X1 ◇ X2) ◇ ·) ((c_0_3 X2 X3 X2).symm)

theorem c_0_30 : ∀ (X1 : G), (X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1)) = (X1 ◇ (X1 ◇ X1)) := by
  intro X1
  calc (X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1))
    _ = ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))) := (c_0_18 X1 X1).symm
    _ = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))) := congrArg (· ◇ (X1 ◇ (X1 ◇ X1))) ((c_0_26 X1).symm)
    _ = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := congrArg (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ·) ((c_0_26 X1).symm)
    _ = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := c_0_26 ((X1 ◇ X1))
    _ = ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) := congrArg ((X1 ◇ X1) ◇ ·) (((c_0_26 X1).symm).symm)
    _ = (X1 ◇ ((X1 ◇ X1) ◇ X1)) := ((c_0_27 X1 X1).symm).symm
    _ = (X1 ◇ (X1 ◇ X1)) := (c_0_3 X1 X1 X1).symm

theorem c_0_31 : ∀ (X1 X2 : G), (X1 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1))) = ((X1 ◇ X1) ◇ (X2 ◇ X1)) := by
  intro X1 X2
  calc (X1 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1)))
    _ = (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ (X2 ◇ X1))) := c_0_5 X1 X1 X1 X2
    _ = (((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))) := (c_0_29 ((X1 ◇ X1)) X1 X2).symm
    _ = ((X1 ◇ X1) ◇ (X2 ◇ X1)) := ((c_0_28 X1 X2).symm).symm

theorem c_0_32 : ∀ (X1 X2 : G), ((X1 ◇ X1) ◇ (X2 ◇ X1)) = (X2 ◇ (X1 ◇ (X1 ◇ X1))) := by
  intro X1 X2
  calc ((X1 ◇ X1) ◇ (X2 ◇ X1))
    _ = (((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ X1)) := (c_0_20 X1 X2).symm
    _ = (X2 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1))) := (c_0_4 X2 X1 X1 X1).symm
    _ = (X2 ◇ (X1 ◇ (X1 ◇ X1))) := congrArg (X2 ◇ ·) (((c_0_30 X1).symm).symm)

theorem c_0_33 : ∀ (X1 X2 : G), (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := by
  intro X1 X2
  calc (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ (X1 ◇ X2)))
    _ = (X1 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1))) := (c_0_6 X1 X1 X1 X2).symm
    _ = ((X1 ◇ X1) ◇ ((X2 ◇ X1) ◇ X1)) := c_0_31 X1 ((X2 ◇ X1))
    _ = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := (c_0_3 X1 ((X1 ◇ X1)) X2).symm

theorem c_0_34 : ∀ (X1 X2 : G), ((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X1)) = (X2 ◇ (X1 ◇ (X1 ◇ X1))) := by
  intro X1 X2
  calc ((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X1))
    _ = (X2 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ (X1 ◇ X1)))) := c_0_3 ((X1 ◇ (X1 ◇ X1))) X2 X1
    _ = (X2 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1)))) := congrArg (X2 ◇ ·) (congrArg (· ◇ (X1 ◇ (X1 ◇ X1))) (c_0_23 X1))
    _ = (X2 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1))) := congrArg (X2 ◇ ·) (((c_0_18 X1 X1).symm).symm)
    _ = (X2 ◇ (X1 ◇ (X1 ◇ X1))) := congrArg (X2 ◇ ·) (((c_0_30 X1).symm).symm)

theorem c_0_35 : ∀ (X1 X2 X3 : G), (X1 ◇ ((X2 ◇ (X3 ◇ (X3 ◇ X3))) ◇ (X2 ◇ X3))) = ((X2 ◇ X3) ◇ (X1 ◇ (X3 ◇ X3))) := by
  intro X1 X2 X3
  calc (X1 ◇ ((X2 ◇ (X3 ◇ (X3 ◇ X3))) ◇ (X2 ◇ X3)))
    _ = (X1 ◇ (((X3 ◇ X3) ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3))) := congrArg (X1 ◇ ·) (congrArg (· ◇ (X2 ◇ X3)) ((c_0_32 X3 X2).symm))
    _ = ((X2 ◇ X3) ◇ (X1 ◇ (X3 ◇ X3))) := (c_0_3 ((X2 ◇ X3)) X1 ((X3 ◇ X3))).symm

theorem c_0_36 : ∀ (X1 X2 : G), (((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X2)) = ((X1 ◇ X1) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) := by
  intro X1 X2
  calc (((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X2))
    _ = ((X1 ◇ X1) ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1))) := (c_0_4 ((X1 ◇ X1)) X1 X2 X1).symm
    _ = ((X1 ◇ X1) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) := c_0_25 X1 ((X1 ◇ (X2 ◇ X1)))

theorem c_0_37 : ∀ (X1 X2 : G), ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X1)) = (X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1))) := by
  intro X1 X2
  calc ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X1))
    _ = (X1 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X1))) := (c_0_31 X1 ((X1 ◇ X2))).symm
    _ = (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) := c_0_7 X1 X1 X1 X2
    _ = (X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1))) := ((c_0_33 X1 ((X2 ◇ X1))).symm).symm

theorem c_0_38 : ∀ (X1 X2 X3 : G), ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ (X2 ◇ X2)))) = ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X2))) := by
  intro X1 X2 X3
  calc ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ (X2 ◇ X2))))
    _ = (X3 ◇ (((X2 ◇ (X2 ◇ X2)) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) := c_0_3 ((X1 ◇ X2)) X3 ((X2 ◇ (X2 ◇ X2)))
    _ = (X3 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X2))) ◇ (X1 ◇ X2))) := congrArg (X3 ◇ ·) (congrArg (· ◇ (X1 ◇ X2)) (c_0_34 X2 X1))
    _ = ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X2))) := ((c_0_35 X3 X1 X2).symm).symm

theorem c_0_39 : ∀ (X1 X2 : G), (((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X2)) = (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))) := by
  intro X1 X2
  calc (((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X2))
    _ = ((X1 ◇ X1) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) := c_0_36 X1 X2
    _ = (X1 ◇ ((X1 ◇ X1) ◇ ((X2 ◇ X1) ◇ X1))) := c_0_37 X1 ((X2 ◇ X1))
    _ = (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))) := congrArg (X1 ◇ ·) ((c_0_3 X1 ((X1 ◇ X1)) X2).symm)

theorem c_0_40 : ∀ (X1 X2 X3 : G), ((X1 ◇ X2) ◇ ((X2 ◇ X2) ◇ (X3 ◇ X2))) = ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X2))) := by
  intro X1 X2 X3
  calc ((X1 ◇ X2) ◇ ((X2 ◇ X2) ◇ (X3 ◇ X2)))
    _ = ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ (X2 ◇ X2)))) := congrArg ((X1 ◇ X2) ◇ ·) (((c_0_32 X2 X3).symm).symm)
    _ = ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X2))) := c_0_38 X1 X2 X3

theorem c_0_41 : ∀ (X1 X2 : G), (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1)))) = ((X1 ◇ X1) ◇ (X2 ◇ X1)) := by
  intro X1 X2
  calc (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1))))
    _ = (((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1))) := (c_0_39 X1 ((X2 ◇ X1))).symm
    _ = (((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))) := c_0_40 ((X1 ◇ X1)) X1 X2
    _ = ((X1 ◇ X1) ◇ (X2 ◇ X1)) := ((c_0_28 X1 X2).symm).symm

theorem c_0_42 : ∀ (X1 X2 : G), ((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))) = ((X1 ◇ X1) ◇ (X2 ◇ X1)) := by
  intro X1 X2
  calc ((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1)))
    _ = (X2 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) := c_0_3 ((X1 ◇ X1)) X2 ((X1 ◇ X1))
    _ = (X2 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) := congrArg (X2 ◇ ·) (congrArg (· ◇ (X1 ◇ X1)) (c_0_26 X1))
    _ = ((X1 ◇ X1) ◇ (X2 ◇ X1)) := (c_0_3 ((X1 ◇ X1)) X2 X1).symm

theorem c_0_43 : ∀ (X1 X2 : G), (X1 ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X2))) = (X1 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2)))) := by
  intro X1 X2
  calc (X1 ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X2)))
    _ = (X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X2))) := (c_0_21 X1 (((X1 ◇ X1) ◇ X2))).symm
    _ = (X1 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2)))) := congrArg (X1 ◇ ·) (c_0_39 X1 X2)

theorem c_0_44 : ∀ (X1 X2 : G), (X1 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2)))) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := by
  intro X1 X2
  calc (X1 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))))
    _ = (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ ((X2 ◇ X1) ◇ X1)))) := congrArg (X1 ◇ ·) (congrArg (X1 ◇ ·) (c_0_3 X1 ((X1 ◇ X1)) X2))
    _ = ((X1 ◇ X1) ◇ ((X2 ◇ X1) ◇ X1)) := c_0_41 X1 ((X2 ◇ X1))
    _ = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := (c_0_3 X1 ((X1 ◇ X1)) X2).symm

theorem c_0_45 : ∀ (X1 X2 : G), ((X1 ◇ X1) ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X1)) = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X2)) := by
  intro X1 X2
  calc ((X1 ◇ X1) ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X1))
    _ = ((X1 ◇ X1) ◇ ((X2 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) := (c_0_42 X1 ((X2 ◇ (X1 ◇ X1)))).symm
    _ = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X2)) := (c_0_3 ((X1 ◇ X1)) ((X1 ◇ X1)) X2).symm

theorem c_0_46 : ∀ (X1 X2 : G), (X1 ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X2))) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := by
  intro X1 X2
  calc (X1 ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X2)))
    _ = (X1 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2)))) := ((c_0_43 X1 X2).symm).symm
    _ = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := c_0_44 X1 X2

theorem c_0_47 : ∀ (X1 X2 : G), ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X2)) = (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))) := by
  intro X1 X2
  calc ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X2))
    _ = ((X1 ◇ X1) ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X1)) := (c_0_45 X1 X2).symm
    _ = (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X1)))) := (c_0_41 X1 ((X2 ◇ (X1 ◇ X1)))).symm
    _ = (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X2)))) := congrArg (X1 ◇ ·) (congrArg (X1 ◇ ·) (((c_0_45 X1 X2).symm).symm))
    _ = (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))) := congrArg (X1 ◇ ·) (((c_0_46 X1 X2).symm).symm)

theorem c_0_48 : ∀ (X1 X2 X3 : G), ((X1 ◇ X1) ◇ (X2 ◇ ((X1 ◇ X1) ◇ X3))) = (X1 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X3)))) := by
  intro X1 X2 X3
  calc ((X1 ◇ X1) ◇ (X2 ◇ ((X1 ◇ X1) ◇ X3)))
    _ = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ ((X3 ◇ X2) ◇ X2))) := congrArg ((X1 ◇ X1) ◇ ·) (c_0_3 X2 ((X1 ◇ X1)) X3)
    _ = (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ ((X3 ◇ X2) ◇ X2)))) := c_0_47 X1 (((X3 ◇ X2) ◇ X2))
    _ = (X1 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X3)))) := congrArg (X1 ◇ ·) (congrArg (X1 ◇ ·) ((c_0_3 X2 ((X1 ◇ X1)) X3).symm))

theorem c_0_49 : ∀ (X1 X2 : G), (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) = ((X1 ◇ X1) ◇ (X2 ◇ X1)) := by
  intro X1 X2
  calc (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1))))
    _ = (X1 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X1)))) := congrArg (X1 ◇ ·) (congrArg (X1 ◇ ·) (c_0_3 X1 X2 X1))
    _ = ((X1 ◇ X1) ◇ (X2 ◇ ((X1 ◇ X1) ◇ X1))) := (c_0_48 X1 X2 X1).symm
    _ = ((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ X1))) := congrArg ((X1 ◇ X1) ◇ ·) ((c_0_3 X1 X2 X1).symm)
    _ = ((X1 ◇ X1) ◇ (X2 ◇ X1)) := ((c_0_25 X1 X2).symm).symm

theorem c_0_50 : ∀ (X1 X2 : G), (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) = ((X1 ◇ X1) ◇ (X2 ◇ X1)) := by
  intro X1 X2
  calc (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1))))
    _ = (X1 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1))) := ((c_0_10 X1 X2).symm).symm
    _ = ((X1 ◇ X1) ◇ (X2 ◇ X1)) := c_0_31 X1 X2

theorem c_0_51 : ∀ (X1 X2 : G), (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := by
  intro X1 X2
  calc (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2))))
    _ = (X1 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1)))) := congrArg (X1 ◇ ·) (congrArg (X1 ◇ ·) (c_0_3 X1 X1 X2))
    _ = ((X1 ◇ X1) ◇ ((X2 ◇ X1) ◇ X1)) := c_0_49 X1 ((X2 ◇ X1))
    _ = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := (c_0_3 X1 ((X1 ◇ X1)) X2).symm

theorem c_0_52 : ∀ (X1 X2 : G), (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1))))) = (X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1))) := by
  intro X1 X2
  calc (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))))
    _ = (X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1))))) := (c_0_21 X1 ((X1 ◇ (X2 ◇ (X1 ◇ X1))))).symm
    _ = (X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1))) := congrArg (X1 ◇ ·) (c_0_50 X1 X2)

theorem c_0_53 : ∀ (X1 X2 : G), (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X2))) = (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))) := by
  intro X1 X2
  calc (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X2)))
    _ = (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2))))) := (c_0_51 X1 ((X1 ◇ X2))).symm
    _ = (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))) := congrArg (X1 ◇ ·) (c_0_51 X1 X2)

theorem c_0_54 : ∀ (X1 X2 : G), (X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1))) = ((X1 ◇ X1) ◇ (X2 ◇ X1)) := by
  intro X1 X2
  calc (X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1)))
    _ = (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1))))) := (c_0_52 X1 X2).symm
    _ = (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))))) := c_0_53 X1 ((X2 ◇ (X1 ◇ X1)))
    _ = (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1)))) := congrArg (X1 ◇ ·) (congrArg (X1 ◇ ·) (((c_0_42 X1 X2).symm).symm))
    _ = ((X1 ◇ X1) ◇ (X2 ◇ X1)) := ((c_0_41 X1 X2).symm).symm

theorem c_0_55 : ∀ (X1 X2 : G), (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := by
  intro X1 X2
  calc (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2)))
    _ = (X1 ◇ ((X1 ◇ X1) ◇ ((X2 ◇ X1) ◇ X1))) := congrArg (X1 ◇ ·) (c_0_3 X1 ((X1 ◇ X1)) X2)
    _ = ((X1 ◇ X1) ◇ ((X2 ◇ X1) ◇ X1)) := c_0_54 X1 ((X2 ◇ X1))
    _ = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := (c_0_3 X1 ((X1 ◇ X1)) X2).symm

theorem c_0_56 : ∀ (X1 X2 X3 : G), (X1 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X3)))) = (X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X3))) := by
  intro X1 X2 X3
  calc (X1 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X3))))
    _ = (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ ((X3 ◇ X2) ◇ X2)))) := congrArg (X1 ◇ ·) (congrArg (X1 ◇ ·) (c_0_3 X2 ((X1 ◇ X1)) X3))
    _ = (X1 ◇ ((X1 ◇ X1) ◇ ((X3 ◇ X2) ◇ X2))) := c_0_55 X1 (((X3 ◇ X2) ◇ X2))
    _ = (X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X3))) := congrArg (X1 ◇ ·) ((c_0_3 X2 ((X1 ◇ X1)) X3).symm)

theorem c_0_57 : ∀ (X1 X2 : G), ((X1 ◇ X1) ◇ (X2 ◇ X1)) = (X1 ◇ (X1 ◇ (X2 ◇ X1))) := by
  intro X1 X2
  calc ((X1 ◇ X1) ◇ (X2 ◇ X1))
    _ = (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) := (c_0_49 X1 X2).symm
    _ = (X1 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X1)))) := congrArg (X1 ◇ ·) (congrArg (X1 ◇ ·) (c_0_3 X1 X2 X1))
    _ = (X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X1))) := ((c_0_56 X1 X2 X1).symm).symm
    _ = (X1 ◇ (X1 ◇ (X2 ◇ X1))) := congrArg (X1 ◇ ·) ((c_0_3 X1 X2 X1).symm)

theorem c_0_58 : ∀ (X1 X2 : G), (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) = (X1 ◇ (X1 ◇ (X2 ◇ X1))) := by
  intro X1 X2
  calc (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1))))
    _ = ((X1 ◇ X1) ◇ (X2 ◇ X1)) := ((c_0_49 X1 X2).symm).symm
    _ = (X1 ◇ (X1 ◇ (X2 ◇ X1))) := c_0_57 X1 X2

theorem c_0_59 : ∀ (X1 X2 : G), (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := by
  intro X1 X2
  calc (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2))))
    _ = (X1 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1)))) := congrArg (X1 ◇ ·) (congrArg (X1 ◇ ·) (c_0_3 X1 X1 X2))
    _ = (X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) := c_0_58 X1 ((X2 ◇ X1))
    _ = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := congrArg (X1 ◇ ·) ((c_0_3 X1 X1 X2).symm)

theorem c_0_60 : ∀ (X1 X2 : G), (X1 ◇ ((X1 ◇ X1) ◇ X2)) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := by
  intro X1 X2
  calc (X1 ◇ ((X1 ◇ X1) ◇ X2))
    _ = ((X1 ◇ X1) ◇ ((X2 ◇ X1) ◇ X1)) := c_0_3 X1 ((X1 ◇ X1)) X2
    _ = (X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) := c_0_57 X1 ((X2 ◇ X1))
    _ = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := congrArg (X1 ◇ ·) ((c_0_3 X1 X1 X2).symm)

theorem c_0_61 : ∀ (X1 X2 X3 : G), (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3))))) = (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) := by
  intro X1 X2 X3
  calc (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))))
    _ = (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ ((X3 ◇ X2) ◇ X2))))) := congrArg (X1 ◇ ·) (congrArg (X1 ◇ ·) (congrArg (X1 ◇ ·) (c_0_3 X2 X1 X3)))
    _ = (X1 ◇ (X1 ◇ (X1 ◇ ((X3 ◇ X2) ◇ X2)))) := c_0_59 X1 (((X3 ◇ X2) ◇ X2))
    _ = (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) := congrArg (X1 ◇ ·) (congrArg (X1 ◇ ·) ((c_0_3 X2 X1 X3).symm))

theorem c_0_62 : ∀ (X1 X2 X3 : G), (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) = (X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X3))) := by
  intro X1 X2 X3
  calc (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3))))
    _ = (X1 ◇ (X1 ◇ (X1 ◇ ((X3 ◇ X2) ◇ X2)))) := congrArg (X1 ◇ ·) (congrArg (X1 ◇ ·) (c_0_3 X2 X1 X3))
    _ = (X1 ◇ ((X1 ◇ X1) ◇ ((X3 ◇ X2) ◇ X2))) := (c_0_60 X1 (((X3 ◇ X2) ◇ X2))).symm
    _ = (X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X3))) := congrArg (X1 ◇ ·) ((c_0_3 X2 ((X1 ◇ X1)) X3).symm)

theorem c_0_63 : ∀ (X1 X2 X3 : G), (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X3)))) = (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X3))) := by
  intro X1 X2 X3
  calc (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X3))))
    _ = (X1 ◇ (X1 ◇ (X1 ◇ ((X3 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))))) := congrArg (X1 ◇ ·) (congrArg (X1 ◇ ·) (c_0_3 ((X1 ◇ X2)) X1 X3))
    _ = (X1 ◇ (X1 ◇ ((X3 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)))) := c_0_61 X1 ((X3 ◇ (X1 ◇ X2))) X2
    _ = (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X3))) := congrArg (X1 ◇ ·) ((c_0_3 ((X1 ◇ X2)) X1 X3).symm)

theorem c_0_64 : ∀ (X1 X2 : G), ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X1)) = ((X1 ◇ X1) ◇ (X2 ◇ X1)) := by
  intro X1 X2
  calc ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X1))
    _ = (X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1))) := ((c_0_37 X1 X2).symm).symm
    _ = ((X1 ◇ X1) ◇ (X2 ◇ X1)) := c_0_54 X1 X2

theorem c_0_65 : ∀ (X1 X2 : G), (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) = (X1 ◇ (X1 ◇ (X2 ◇ X1))) := by
  intro X1 X2
  calc (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1))))
    _ = (X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X1))) := ((c_0_62 X1 X2 X1).symm).symm
    _ = (X1 ◇ (X1 ◇ (X2 ◇ X1))) := congrArg (X1 ◇ ·) ((c_0_3 X1 X2 X1).symm)

theorem c_0_66 : ∀ (X1 X2 : G), (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X1))) = ((X1 ◇ X2) ◇ (X1 ◇ X1)) := by
  intro X1 X2
  calc (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X1)))
    _ = (X1 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)))) := congrArg (X1 ◇ ·) (c_0_3 ((X1 ◇ X2)) X1 X1)
    _ = (X1 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) := c_0_63 X1 ((X1 ◇ X2)) X2
    _ = ((X1 ◇ X2) ◇ (X1 ◇ X1)) := (c_0_3 ((X1 ◇ X2)) X1 X1).symm

theorem c_0_67 : ∀ (X1 X2 : G), (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1))) = (X1 ◇ (X1 ◇ (X2 ◇ X1))) := by
  intro X1 X2
  calc (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1)))
    _ = ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X1)) := (c_0_57 X1 ((X1 ◇ X2))).symm
    _ = ((X1 ◇ X1) ◇ (X2 ◇ X1)) := c_0_64 X1 X2
    _ = (X1 ◇ (X1 ◇ (X2 ◇ X1))) := ((c_0_57 X1 X2).symm).symm

theorem c_0_68 : ∀ (X1 X2 : G), ((X1 ◇ X2) ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ (X2 ◇ X1))) := by
  intro X1 X2
  calc ((X1 ◇ X2) ◇ (X1 ◇ X1))
    _ = (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X1))) := (c_0_66 X1 X2).symm
    _ = (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X1)))) := (c_0_63 X1 X2 X1).symm
    _ = (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1))) := ((c_0_65 X1 ((X1 ◇ X2))).symm).symm
    _ = (X1 ◇ (X1 ◇ (X2 ◇ X1))) := ((c_0_67 X1 X2).symm).symm

theorem c_0_69 : ∀ (X1 X2 X3 : G), (X1 ◇ (X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ X1))) = ((X3 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X1)) := by
  intro X1 X2 X3
  calc (X1 ◇ (X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ X1)))
    _ = ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ (X1 ◇ X1)) := (c_0_68 X1 (((X2 ◇ X3) ◇ X3))).symm
    _ = ((X3 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X1)) := congrArg (· ◇ (X1 ◇ X1)) ((c_0_3 X3 X1 X2).symm)

theorem c_0_70 : ∀ (X1 X2 X3 : G), (X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ (X1 ◇ X1))) = ((X2 ◇ (X1 ◇ X3)) ◇ (X1 ◇ X1)) := by
  intro X1 X2 X3
  calc (X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ (X1 ◇ X1)))
    _ = (X1 ◇ (X1 ◇ (X1 ◇ (((X3 ◇ X2) ◇ X2) ◇ X1)))) := congrArg (X1 ◇ ·) ((c_0_69 X1 X3 X2).symm)
    _ = (X1 ◇ (X1 ◇ (((X3 ◇ X2) ◇ X2) ◇ X1))) := c_0_58 X1 (((X3 ◇ X2) ◇ X2))
    _ = ((X2 ◇ (X1 ◇ X3)) ◇ (X1 ◇ X1)) := ((c_0_69 X1 X3 X2).symm).symm

theorem c_0_71 : ∀ (X1 X2 : G), ((X1 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X2)) = ((X2 ◇ X2) ◇ (X2 ◇ X1)) := by
  intro X1 X2
  calc ((X1 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X2))
    _ = (X2 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X2))) := (c_0_70 X2 X1 X2).symm
    _ = ((X2 ◇ X2) ◇ (X2 ◇ X1)) := (c_0_3 ((X2 ◇ X2)) X2 X1).symm

theorem c_0_72 : ∀ (X1 X2 X3 : G), (X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X3))) = ((X2 ◇ X2) ◇ (X1 ◇ X3)) := by
  intro X1 X2 X3
  calc (X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X3)))
    _ = (X1 ◇ ((X3 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X2))) := congrArg (X1 ◇ ·) ((c_0_71 X3 X2).symm)
    _ = ((X2 ◇ X2) ◇ (X1 ◇ X3)) := (c_0_3 ((X2 ◇ X2)) X1 X3).symm

theorem c_0_73 : ∀ (X1 X2 : G), ((X1 ◇ X1) ◇ (X1 ◇ X2)) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := by
  intro X1 X2
  calc ((X1 ◇ X1) ◇ (X1 ◇ X2))
    _ = ((X2 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) := (c_0_71 X2 X1).symm
    _ = (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) := (c_0_70 X1 X2 X1).symm
    _ = (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X2))) := congrArg (X1 ◇ ·) (c_0_71 X2 X1)
    _ = (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) := ((c_0_60 X1 ((X1 ◇ X2))).symm).symm
    _ = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := ((c_0_59 X1 X2).symm).symm

theorem c_0_74 : ∀ (X1 X2 X3 : G), (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X3)))) = ((X2 ◇ X2) ◇ (X1 ◇ X3)) := by
  intro X1 X2 X3
  calc (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X3))))
    _ = (X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X3))) := congrArg (X1 ◇ ·) ((c_0_73 X2 X3).symm)
    _ = ((X2 ◇ X2) ◇ (X1 ◇ X3)) := c_0_72 X1 X2 X3

theorem c_0_75 : ∀ (X1 X2 X3 : G), ((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X3))) = (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) := by
  intro X1 X2 X3
  calc ((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X3)))
    _ = ((X1 ◇ X1) ◇ (X1 ◇ ((X3 ◇ X2) ◇ X2))) := congrArg ((X1 ◇ X1) ◇ ·) (c_0_3 X2 X1 X3)
    _ = (X1 ◇ (X1 ◇ (X1 ◇ ((X3 ◇ X2) ◇ X2)))) := c_0_73 X1 (((X3 ◇ X2) ◇ X2))
    _ = (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) := congrArg (X1 ◇ ·) (congrArg (X1 ◇ ·) ((c_0_3 X2 X1 X3).symm))

theorem c_0_76 : ∀ (X1 X2 X3 : G), (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) = ((X1 ◇ X1) ◇ (X2 ◇ X3)) := by
  intro X1 X2 X3
  calc (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3))))
    _ = ((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X3))) := (c_0_75 X1 X2 X3).symm
    _ = (X2 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X3))))) := (c_0_74 X2 X1 ((X1 ◇ X3))).symm
    _ = (X2 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X3))) := congrArg (X2 ◇ ·) (c_0_74 X1 X1 X3)
    _ = (X2 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X3)))) := congrArg (X2 ◇ ·) (((c_0_73 X1 X3).symm).symm)
    _ = ((X1 ◇ X1) ◇ (X2 ◇ X3)) := ((c_0_74 X2 X1 X3).symm).symm

theorem c_0_77 : ∀ (X1 X2 : G), ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := by
  intro X1 X2
  calc ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2)))
    _ = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := ((c_0_27 X1 X2).symm).symm
    _ = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := c_0_60 X1 X2

theorem c_0_78 : ∀ (X1 X2 X3 : G), ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) = (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X3))) := by
  intro X1 X2 X3
  calc ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3))
    _ = (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X3)))) := (c_0_76 X1 ((X1 ◇ X2)) X3).symm
    _ = (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X3))) := c_0_63 X1 X2 X3

theorem c_0_79 : ∀ (X1 X2 X3 : G), ((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) = (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) := by
  intro X1 X2 X3
  calc ((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3))))
    _ = ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ ((X3 ◇ X2) ◇ X2)))) := congrArg ((X1 ◇ X1) ◇ ·) (congrArg (X1 ◇ ·) (c_0_3 X2 X1 X3))
    _ = (X1 ◇ (X1 ◇ (X1 ◇ ((X3 ◇ X2) ◇ X2)))) := c_0_77 X1 (((X3 ◇ X2) ◇ X2))
    _ = (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) := congrArg (X1 ◇ ·) (congrArg (X1 ◇ ·) ((c_0_3 X2 X1 X3).symm))

theorem c_0_80 : ∀ (X1 X2 : G), (X1 ◇ (X1 ◇ (X2 ◇ X1))) = (X2 ◇ (X1 ◇ (X1 ◇ X1))) := by
  intro X1 X2
  calc (X1 ◇ (X1 ◇ (X2 ◇ X1)))
    _ = ((X1 ◇ X1) ◇ (X2 ◇ X1)) := (c_0_57 X1 X2).symm
    _ = (X2 ◇ (X1 ◇ (X1 ◇ X1))) := c_0_32 X1 X2

theorem c_0_81 : ∀ (X1 X2 : G), (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X1)))) = (X2 ◇ (X1 ◇ (X1 ◇ X1))) := by
  intro X1 X2
  calc (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X1))))
    _ = (X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1))) := congrArg (X1 ◇ ·) ((c_0_32 X1 X2).symm)
    _ = ((X1 ◇ X1) ◇ (X2 ◇ X1)) := c_0_54 X1 X2
    _ = (X2 ◇ (X1 ◇ (X1 ◇ X1))) := ((c_0_32 X1 X2).symm).symm

theorem c_0_82 : ∀ (X1 X2 : G), (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) = (X1 ◇ (X2 ◇ X1)) := by
  intro X1 X2
  calc (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2)))
    _ = ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X2)) := (c_0_78 X1 X2 X2).symm
    _ = (X2 ◇ ((X1 ◇ X1) ◇ X1)) := (c_0_3 X2 ((X1 ◇ X1)) X1).symm
    _ = (X1 ◇ (X2 ◇ X1)) := (c_0_3 X1 X2 X1).symm

theorem c_0_83 : ∀ (X1 X2 X3 : G), (X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ X3))) = (((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ X3)) := by
  intro X1 X2 X3
  calc (X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ X3)))
    _ = (X1 ◇ (X1 ◇ ((X3 ◇ ((X1 ◇ X1) ◇ X2)) ◇ ((X1 ◇ X1) ◇ X2)))) := congrArg (X1 ◇ ·) (c_0_3 (((X1 ◇ X1) ◇ X2)) X1 X3)
    _ = (X1 ◇ ((X3 ◇ ((X1 ◇ X1) ◇ X2)) ◇ ((X1 ◇ X1) ◇ X2))) := c_0_56 X1 ((X3 ◇ ((X1 ◇ X1) ◇ X2))) X2
    _ = (((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ X3)) := (c_0_3 (((X1 ◇ X1) ◇ X2)) X1 X3).symm

theorem c_0_84 : ∀ (X1 X2 X3 : G), ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X3))) = (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X3))) := by
  intro X1 X2 X3
  calc ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X3)))
    _ = ((X1 ◇ X1) ◇ (X1 ◇ ((X3 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)))) := congrArg ((X1 ◇ X1) ◇ ·) (c_0_3 ((X1 ◇ X2)) X1 X3)
    _ = (X1 ◇ (X1 ◇ ((X3 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)))) := c_0_79 X1 ((X3 ◇ (X1 ◇ X2))) X2
    _ = (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X3))) := congrArg (X1 ◇ ·) ((c_0_3 ((X1 ◇ X2)) X1 X3).symm)

theorem c_0_85 : ∀ (X1 X2 X3 : G), (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X3)))) = ((X3 ◇ X3) ◇ (X1 ◇ (X2 ◇ X3))) := by
  intro X1 X2 X3
  calc (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X3))))
    _ = (X1 ◇ (X3 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X3))))) := congrArg (X1 ◇ ·) ((c_0_81 X3 X2).symm)
    _ = (X1 ◇ (X3 ◇ (X3 ◇ (X3 ◇ (X2 ◇ X3))))) := congrArg (X1 ◇ ·) (congrArg (X3 ◇ ·) ((c_0_80 X3 X2).symm))
    _ = ((X3 ◇ X3) ◇ (X1 ◇ (X2 ◇ X3))) := ((c_0_74 X1 X3 ((X2 ◇ X3))).symm).symm

theorem c_0_86 : ∀ (X1 X2 : G), (X1 ◇ (X1 ◇ (X2 ◇ X1))) = (X1 ◇ (X2 ◇ X1)) := by
  intro X1 X2
  calc (X1 ◇ (X1 ◇ (X2 ◇ X1)))
    _ = (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2)))) := congrArg (X1 ◇ ·) ((c_0_82 X1 X2).symm)
    _ = ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X2)) := c_0_76 X1 ((X1 ◇ X2)) X2
    _ = (X2 ◇ ((X1 ◇ X1) ◇ X1)) := (c_0_3 X2 ((X1 ◇ X1)) X1).symm
    _ = (X1 ◇ (X2 ◇ X1)) := (c_0_3 X1 X2 X1).symm

theorem c_0_87 : ∀ (X1 X2 : G), (((X1 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) = (X1 ◇ (X1 ◇ (X2 ◇ X1))) := by
  intro X1 X2
  calc (((X1 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))
    _ = (X1 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) := (c_0_83 X1 ((X1 ◇ X2)) X2).symm
    _ = ((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X1))) := (c_0_3 ((X1 ◇ X2)) X1 ((X1 ◇ X1))).symm
    _ = (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1))) := (c_0_80 X1 ((X1 ◇ X2))).symm
    _ = (X1 ◇ (X1 ◇ (X2 ◇ X1))) := ((c_0_67 X1 X2).symm).symm

theorem c_0_88 : ∀ (X1 X2 : G), (X1 ◇ ((X1 ◇ X2) ◇ X1)) = (X1 ◇ (X1 ◇ (X2 ◇ X1))) := by
  intro X1 X2
  calc (X1 ◇ ((X1 ◇ X2) ◇ X1))
    _ = ((X1 ◇ X2) ◇ ((X1 ◇ X1) ◇ X1)) := c_0_3 X1 ((X1 ◇ X2)) X1
    _ = ((X1 ◇ X1) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) := c_0_3 ((X1 ◇ X2)) ((X1 ◇ X1)) X1
    _ = (X1 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) := c_0_84 X1 ((X1 ◇ X2)) X2
    _ = ((X1 ◇ X2) ◇ (X1 ◇ X1)) := (c_0_3 ((X1 ◇ X2)) X1 X1).symm
    _ = (X1 ◇ (X1 ◇ (X2 ◇ X1))) := ((c_0_68 X1 X2).symm).symm

theorem c_0_89 : ∀ (X1 X2 X3 : G), (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))) = ((X1 ◇ X1) ◇ (X2 ◇ X3)) := by
  intro X1 X2 X3
  calc (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3))))
    _ = ((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ X3))) := (c_0_73 X1 ((X2 ◇ X3))).symm
    _ = ((X1 ◇ X1) ◇ (X2 ◇ ((X3 ◇ X1) ◇ X1))) := congrArg ((X1 ◇ X1) ◇ ·) (c_0_3 X1 X2 X3)
    _ = (X2 ◇ ((X3 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1)))) := (c_0_85 X2 ((X3 ◇ X1)) X1).symm
    _ = (X2 ◇ (X1 ◇ (X1 ◇ ((X3 ◇ X1) ◇ X1)))) := congrArg (X2 ◇ ·) ((c_0_80 X1 ((X3 ◇ X1))).symm)
    _ = (X2 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X3)))) := congrArg (X2 ◇ ·) (congrArg (X1 ◇ ·) ((c_0_3 X1 X1 X3).symm))
    _ = ((X1 ◇ X1) ◇ (X2 ◇ X3)) := ((c_0_74 X2 X1 X3).symm).symm

theorem c_0_90 : ∀ (X1 X2 : G), (X1 ◇ (X1 ◇ (X1 ◇ X2))) = (X1 ◇ (X1 ◇ X2)) := by
  intro X1 X2
  calc (X1 ◇ (X1 ◇ (X1 ◇ X2)))
    _ = (X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) := congrArg (X1 ◇ ·) (c_0_3 X1 X1 X2)
    _ = (X1 ◇ ((X2 ◇ X1) ◇ X1)) := c_0_86 X1 ((X2 ◇ X1))
    _ = (X1 ◇ (X1 ◇ X2)) := (c_0_3 X1 X1 X2).symm

theorem c_0_91 : ∀ (X1 X2 : G), ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X1 ◇ X2)) = (X1 ◇ (X1 ◇ (X2 ◇ X1))) := by
  intro X1 X2
  calc ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X1 ◇ X2))
    _ = (((X1 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) := congrArg (· ◇ (X1 ◇ X2)) ((c_0_73 X1 X2).symm)
    _ = (X1 ◇ (X1 ◇ (X2 ◇ X1))) := c_0_87 X1 X2

theorem c_0_92 : ∀ (X1 X2 X3 : G), (((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ X3)) = ((X1 ◇ X1) ◇ (X2 ◇ X3)) := by
  intro X1 X2 X3
  calc (((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ X3))
    _ = (X2 ◇ (X1 ◇ ((X1 ◇ (X3 ◇ X1)) ◇ X1))) := (c_0_4 X2 X1 X3 X1).symm
    _ = (X2 ◇ (X1 ◇ (X1 ◇ ((X3 ◇ X1) ◇ X1)))) := congrArg (X2 ◇ ·) (c_0_88 X1 ((X3 ◇ X1)))
    _ = (X2 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X3)))) := congrArg (X2 ◇ ·) (congrArg (X1 ◇ ·) ((c_0_3 X1 X1 X3).symm))
    _ = ((X1 ◇ X1) ◇ (X2 ◇ X3)) := ((c_0_74 X2 X1 X3).symm).symm

theorem c_0_93 : ∀ (X1 X2 X3 : G), ((X1 ◇ X1) ◇ (X2 ◇ X3)) = (X1 ◇ (X1 ◇ (X2 ◇ X3))) := by
  intro X1 X2 X3
  calc ((X1 ◇ X1) ◇ (X2 ◇ X3))
    _ = (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))) := (c_0_89 X1 X2 X3).symm
    _ = (X1 ◇ (X1 ◇ (X2 ◇ X3))) := c_0_90 X1 ((X2 ◇ X3))

theorem c_0_94 : ∀ (X1 X2 : G), ((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ X1)) := by
  intro X1 X2
  calc ((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))
    _ = ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X1 ◇ X2)) := congrArg (· ◇ (X1 ◇ X2)) ((c_0_90 X1 X2).symm)
    _ = (X1 ◇ (X1 ◇ (X2 ◇ X1))) := c_0_91 X1 X2
    _ = (X1 ◇ (X2 ◇ X1)) := ((c_0_86 X1 X2).symm).symm

theorem c_0_95 : ∀ (X1 X2 X3 : G), (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X2)))) = ((X2 ◇ X2) ◇ (X1 ◇ (X3 ◇ X2))) := by
  intro X1 X2 X3
  calc (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X2))))
    _ = (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X2))))) := congrArg (X1 ◇ ·) ((c_0_58 X2 X3).symm)
    _ = (X1 ◇ (X2 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X2)))) := congrArg (X1 ◇ ·) (congrArg (X2 ◇ ·) ((c_0_88 X2 X3).symm))
    _ = (X1 ◇ (X2 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X2))) := congrArg (X1 ◇ ·) ((c_0_88 X2 ((X2 ◇ X3))).symm)
    _ = (((X2 ◇ X2) ◇ X2) ◇ (X1 ◇ (X3 ◇ X2))) := ((c_0_5 X1 X2 X2 X3).symm).symm
    _ = ((X2 ◇ X2) ◇ (X1 ◇ (X3 ◇ X2))) := ((c_0_92 X2 X1 ((X3 ◇ X2))).symm).symm

theorem c_0_96 : ∀ (X1 X2 X3 : G), (X1 ◇ (X2 ◇ (X1 ◇ X3))) = (X2 ◇ ((X1 ◇ X1) ◇ X3)) := by
  intro X1 X2 X3
  calc (X1 ◇ (X2 ◇ (X1 ◇ X3)))
    _ = (X1 ◇ (X1 ◇ ((X3 ◇ X2) ◇ X2))) := congrArg (X1 ◇ ·) (c_0_3 X2 X1 X3)
    _ = ((X1 ◇ X1) ◇ ((X3 ◇ X2) ◇ X2)) := (c_0_93 X1 ((X3 ◇ X2)) X2).symm
    _ = (X2 ◇ ((X1 ◇ X1) ◇ X3)) := (c_0_3 X2 ((X1 ◇ X1)) X3).symm

theorem c_0_97 : ∀ (X1 X2 : G), (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ (X2 ◇ X2)))) = ((X1 ◇ X2) ◇ (X1 ◇ (X2 ◇ X2))) := by
  intro X1 X2
  calc (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ (X2 ◇ X2))))
    _ = (X1 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X2))) ◇ (X1 ◇ X2)))) := congrArg (X1 ◇ ·) ((c_0_35 X1 X1 X2).symm)
    _ = (X1 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X2))) ◇ (X1 ◇ X2))) := c_0_63 X1 ((X2 ◇ (X2 ◇ X2))) X2
    _ = ((X1 ◇ X2) ◇ (X1 ◇ (X2 ◇ X2))) := ((c_0_35 X1 X1 X2).symm).symm

theorem c_0_98 : ∀ (X1 X2 X3 : G), (X1 ◇ (X2 ◇ (X3 ◇ X2))) = ((X2 ◇ X3) ◇ (X1 ◇ X2)) := by
  intro X1 X2 X3
  calc (X1 ◇ (X2 ◇ (X3 ◇ X2)))
    _ = (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3))) := congrArg (X1 ◇ ·) ((c_0_94 X2 X3).symm)
    _ = ((X2 ◇ X3) ◇ (X1 ◇ X2)) := (c_0_3 ((X2 ◇ X3)) X1 X2).symm

theorem c_0_99 : ∀ (X1 X2 X3 : G), (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))) = (X2 ◇ (X1 ◇ (X3 ◇ X1))) := by
  intro X1 X2 X3
  calc (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1))))
    _ = ((X1 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) := (c_0_93 X1 X2 ((X3 ◇ X1))).symm
    _ = (X2 ◇ (X1 ◇ (X1 ◇ (X3 ◇ X1)))) := (c_0_95 X2 X1 X3).symm
    _ = (X2 ◇ (X1 ◇ (X3 ◇ X1))) := congrArg (X2 ◇ ·) (((c_0_86 X1 X3).symm).symm)

theorem c_0_100 : ∀ (X1 X2 : G), (X1 ◇ (X2 ◇ (X1 ◇ X1))) = (X1 ◇ (X2 ◇ X1)) := by
  intro X1 X2
  calc (X1 ◇ (X2 ◇ (X1 ◇ X1)))
    _ = (X2 ◇ ((X1 ◇ X1) ◇ X1)) := ((c_0_96 X1 X2 X1).symm).symm
    _ = (X1 ◇ (X2 ◇ X1)) := (c_0_3 X1 X2 X1).symm

theorem c_0_101 : ∀ (X1 X2 : G), (X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X2)))) = ((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X2))) := by
  intro X1 X2
  calc (X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X2))))
    _ = (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ (X2 ◇ X2)))) := congrArg (X1 ◇ ·) ((c_0_29 X1 X2 X1).symm)
    _ = ((X1 ◇ X2) ◇ (X1 ◇ (X2 ◇ X2))) := c_0_97 X1 X2
    _ = ((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X2))) := ((c_0_29 X1 X2 X1).symm).symm

theorem c_0_102 : ∀ (X1 X2 X3 : G), ((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ X2))) = (X2 ◇ ((X2 ◇ X3) ◇ X1)) := by
  intro X1 X2 X3
  calc ((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ X2)))
    _ = ((X2 ◇ X3) ◇ ((X1 ◇ X2) ◇ X2)) := ((c_0_98 ((X1 ◇ X2)) X2 X3).symm).symm
    _ = (X2 ◇ ((X2 ◇ X3) ◇ X1)) := (c_0_3 X2 ((X2 ◇ X3)) X1).symm

theorem c_0_103 : ∀ (X1 X2 X3 : G), (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) = (X1 ◇ (X2 ◇ (X1 ◇ X3))) := by
  intro X1 X2 X3
  calc (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3))))
    _ = (X1 ◇ (X1 ◇ (X1 ◇ ((X3 ◇ X2) ◇ X2)))) := congrArg (X1 ◇ ·) (congrArg (X1 ◇ ·) (c_0_3 X2 X1 X3))
    _ = (X1 ◇ (X1 ◇ ((X3 ◇ X2) ◇ X2))) := c_0_90 X1 (((X3 ◇ X2) ◇ X2))
    _ = (X1 ◇ (X2 ◇ (X1 ◇ X3))) := congrArg (X1 ◇ ·) ((c_0_3 X2 X1 X3).symm)

theorem c_0_104 : ∀ (X1 X2 X3 : G), (X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X1)))) = (X2 ◇ (X1 ◇ (X3 ◇ X1))) := by
  intro X1 X2 X3
  calc (X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X1))))
    _ = (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1))))) := congrArg (X1 ◇ ·) ((c_0_99 X1 X2 X3).symm)
    _ = (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))) := c_0_90 X1 ((X2 ◇ (X3 ◇ X1)))
    _ = (X2 ◇ (X1 ◇ (X3 ◇ X1))) := ((c_0_99 X1 X2 X3).symm).symm

theorem c_0_105 : ∀ (X1 X2 : G), (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X1)))) = (X2 ◇ (X1 ◇ (X2 ◇ X1))) := by
  intro X1 X2
  calc (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X1))))
    _ = (X1 ◇ ((X2 ◇ X2) ◇ (X1 ◇ X1))) := congrArg (X1 ◇ ·) ((c_0_93 X2 X1 X1).symm)
    _ = (X2 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) := (c_0_96 X2 X1 ((X1 ◇ X1))).symm
    _ = (X2 ◇ (X1 ◇ (X2 ◇ X1))) := congrArg (X2 ◇ ·) (((c_0_100 X1 X2).symm).symm)

theorem c_0_106 : ∀ (X1 X2 : G), (X1 ◇ (X1 ◇ (X2 ◇ X2))) = (X1 ◇ (X2 ◇ X2)) := by
  intro X1 X2
  calc (X1 ◇ (X1 ◇ (X2 ◇ X2)))
    _ = (X1 ◇ (X2 ◇ ((X2 ◇ X1) ◇ X1))) := congrArg (X1 ◇ ·) (c_0_3 X1 X2 X2)
    _ = (X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X2)))) := congrArg (X1 ◇ ·) ((c_0_102 X1 X2 X1).symm)
    _ = ((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X2))) := c_0_101 X1 X2
    _ = (X2 ◇ ((X2 ◇ X1) ◇ X1)) := ((c_0_102 X1 X2 X1).symm).symm
    _ = (X1 ◇ (X2 ◇ X2)) := (c_0_3 X1 X2 X2).symm

theorem c_0_107 : ∀ (X1 X2 X3 : G), (X1 ◇ (X1 ◇ (X2 ◇ X3))) = (X1 ◇ (X2 ◇ (X1 ◇ X3))) := by
  intro X1 X2 X3
  calc (X1 ◇ (X1 ◇ (X2 ◇ X3)))
    _ = ((X1 ◇ X1) ◇ (X2 ◇ X3)) := (c_0_93 X1 X2 X3).symm
    _ = (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) := (c_0_76 X1 X2 X3).symm
    _ = (X1 ◇ (X2 ◇ (X1 ◇ X3))) := ((c_0_103 X1 X2 X3).symm).symm

theorem c_0_108 : ∀ (X1 X2 X3 : G), (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X3)))) = (X2 ◇ (X1 ◇ (X1 ◇ X3))) := by
  intro X1 X2 X3
  calc (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X3))))
    _ = (X1 ◇ (X2 ◇ (X1 ◇ ((X3 ◇ X1) ◇ X1)))) := congrArg (X1 ◇ ·) (congrArg (X2 ◇ ·) (c_0_3 X1 X1 X3))
    _ = (X2 ◇ (X1 ◇ ((X3 ◇ X1) ◇ X1))) := c_0_104 X1 X2 ((X3 ◇ X1))
    _ = (X2 ◇ (X1 ◇ (X1 ◇ X3))) := congrArg (X2 ◇ ·) ((c_0_3 X1 X1 X3).symm)

theorem c_0_109 : ∀ (X1 X2 : G), (X1 ◇ (X2 ◇ (X1 ◇ X2))) = (X2 ◇ (X1 ◇ X2)) := by
  intro X1 X2
  calc (X1 ◇ (X2 ◇ (X1 ◇ X2)))
    _ = (X2 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) := (c_0_105 X2 X1).symm
    _ = (X2 ◇ (X1 ◇ (X2 ◇ X2))) := congrArg (X2 ◇ ·) (c_0_106 X1 X2)
    _ = (X2 ◇ (X1 ◇ X2)) := ((c_0_100 X2 X1).symm).symm

theorem c_0_110 : ∀ (X1 X2 X3 : G), (X1 ◇ (X2 ◇ (X2 ◇ X3))) = (X2 ◇ (X1 ◇ (X2 ◇ X3))) := by
  intro X1 X2 X3
  calc (X1 ◇ (X2 ◇ (X2 ◇ X3)))
    _ = (X2 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) := (c_0_108 X2 X1 X3).symm
    _ = (X2 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X3)))) := (c_0_107 X2 X1 ((X2 ◇ X3))).symm
    _ = (X2 ◇ (X1 ◇ (X2 ◇ X3))) := ((c_0_103 X2 X1 X3).symm).symm

theorem c_0_111 : ∀ (X1 X2 X3 : G), (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X3))) = ((X1 ◇ X2) ◇ (X1 ◇ X3)) := by
  intro X1 X2 X3
  calc (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X3)))
    _ = (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X3))) := c_0_107 X1 ((X1 ◇ X2)) X3
    _ = (X1 ◇ (X1 ◇ ((X3 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)))) := congrArg (X1 ◇ ·) (c_0_3 ((X1 ◇ X2)) X1 X3)
    _ = (X1 ◇ ((X3 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) := ((c_0_103 X1 ((X3 ◇ (X1 ◇ X2))) X2).symm).symm
    _ = ((X1 ◇ X2) ◇ (X1 ◇ X3)) := (c_0_3 ((X1 ◇ X2)) X1 X3).symm

theorem c_0_112 : ∀ (X1 X2 : G), (X1 ◇ (X2 ◇ X1)) = (X2 ◇ (X1 ◇ X1)) := by
  intro X1 X2
  calc (X1 ◇ (X2 ◇ X1))
    _ = (X2 ◇ (X1 ◇ (X2 ◇ X1))) := (c_0_109 X2 X1).symm
    _ = (X2 ◇ (X2 ◇ (X1 ◇ X1))) := (c_0_107 X2 X1 X1).symm
    _ = (X2 ◇ (X1 ◇ X1)) := ((c_0_106 X2 X1).symm).symm

theorem c_0_113 : ∀ (X1 X2 : G), (X1 ◇ (X2 ◇ X1)) = (X2 ◇ (X2 ◇ X1)) := by
  intro X1 X2
  calc (X1 ◇ (X2 ◇ X1))
    _ = (X2 ◇ (X1 ◇ (X2 ◇ X1))) := (c_0_109 X2 X1).symm
    _ = (X2 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))) := congrArg (X2 ◇ ·) ((c_0_109 X2 X1).symm)
    _ = (X2 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X1))) := congrArg (X2 ◇ ·) (c_0_98 X2 X1 X2)
    _ = ((X1 ◇ X2) ◇ (X2 ◇ (X2 ◇ X1))) := (c_0_110 ((X1 ◇ X2)) X2 X1).symm
    _ = ((X1 ◇ X2) ◇ (X2 ◇ ((X1 ◇ X2) ◇ X2))) := congrArg ((X1 ◇ X2) ◇ ·) (((c_0_3 X2 X2 X1).symm).symm)
    _ = (X2 ◇ ((X1 ◇ X2) ◇ X2)) := ((c_0_109 ((X1 ◇ X2)) X2).symm).symm
    _ = (X2 ◇ (X2 ◇ X1)) := (c_0_3 X2 X2 X1).symm

theorem c_0_114 : ∀ (X1 X2 X3 : G), ((X1 ◇ X2) ◇ (X1 ◇ X3)) = (X1 ◇ ((X1 ◇ X2) ◇ X3)) := by
  intro X1 X2 X3
  calc ((X1 ◇ X2) ◇ (X1 ◇ X3))
    _ = (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X3))) := (c_0_111 X1 X2 X3).symm
    _ = (X1 ◇ ((X3 ◇ X1) ◇ (X1 ◇ (X2 ◇ X1)))) := congrArg (X1 ◇ ·) ((c_0_102 X3 X1 X2).symm)
    _ = ((X3 ◇ X1) ◇ (X1 ◇ (X2 ◇ X1))) := ((c_0_104 X1 ((X3 ◇ X1)) X2).symm).symm
    _ = (X1 ◇ ((X1 ◇ X2) ◇ X3)) := ((c_0_102 X3 X1 X2).symm).symm

theorem c_0_115 : ∀ (X1 X2 X3 : G), (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) = (X1 ◇ (X1 ◇ (X2 ◇ X3))) := by
  intro X1 X2 X3
  calc (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3))))
    _ = ((X1 ◇ X1) ◇ (X2 ◇ X3)) := ((c_0_76 X1 X2 X3).symm).symm
    _ = (X1 ◇ (X1 ◇ (X2 ◇ X3))) := c_0_93 X1 X2 X3

theorem c_0_116 : ∀ (X1 X2 : G), (X1 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ X2)) := by
  intro X1 X2
  calc (X1 ◇ (X1 ◇ X2))
    _ = (X2 ◇ (X1 ◇ X2)) := (c_0_113 X2 X1).symm
    _ = (X1 ◇ (X2 ◇ X2)) := c_0_112 X2 X1

theorem c_0_117 : ∀ (X1 X2 : G), (X1 ◇ (X2 ◇ X2)) = (X2 ◇ (X1 ◇ X1)) := by
  intro X1 X2
  calc (X1 ◇ (X2 ◇ X2))
    _ = (X1 ◇ (X1 ◇ (X2 ◇ X2))) := (c_0_106 X1 X2).symm
    _ = (X1 ◇ (X2 ◇ ((X2 ◇ X1) ◇ X1))) := congrArg (X1 ◇ ·) (c_0_3 X1 X2 X2)
    _ = (X1 ◇ ((X2 ◇ X1) ◇ (X2 ◇ X1))) := congrArg (X1 ◇ ·) ((c_0_114 X2 X1 X1).symm)
    _ = ((X2 ◇ X1) ◇ (X1 ◇ (X2 ◇ X1))) := (c_0_112 ((X2 ◇ X1)) X1).symm
    _ = (X1 ◇ ((X1 ◇ X2) ◇ X2)) := ((c_0_102 X2 X1 X2).symm).symm
    _ = (X2 ◇ (X1 ◇ X1)) := (c_0_3 X2 X1 X1).symm

theorem c_0_118 : ∀ (X1 X2 X3 : G), (X1 ◇ (X2 ◇ (X2 ◇ X3))) = (X2 ◇ (X2 ◇ (X1 ◇ X3))) := by
  intro X1 X2 X3
  calc (X1 ◇ (X2 ◇ (X2 ◇ X3)))
    _ = (X2 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) := (c_0_108 X2 X1 X3).symm
    _ = (X2 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X3)))) := (c_0_107 X2 X1 ((X2 ◇ X3))).symm
    _ = (X2 ◇ (X2 ◇ (X1 ◇ X3))) := ((c_0_115 X2 X1 X3).symm).symm

theorem c_0_119 : ∀ (X1 X2 : G), (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (X1 ◇ X1)) := by
  intro X1 X2
  calc (X1 ◇ (X1 ◇ X2))
    _ = (X1 ◇ (X2 ◇ X2)) := ((c_0_116 X1 X2).symm).symm
    _ = (X2 ◇ (X1 ◇ X1)) := c_0_117 X1 X2

theorem c_0_120 : ∀ (X1 X2 X3 : G), (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))) = (X2 ◇ (X1 ◇ (X3 ◇ X3))) := by
  intro X1 X2 X3
  calc (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3))))
    _ = (X2 ◇ (X1 ◇ (X1 ◇ (X3 ◇ X3)))) := (c_0_118 X2 X1 ((X3 ◇ X3))).symm
    _ = (X2 ◇ (X1 ◇ (X3 ◇ X3))) := congrArg (X2 ◇ ·) (c_0_106 X1 X3)

theorem c_0_121 : ∀ (X1 X2 : G), (X1 ◇ (X2 ◇ X1)) = (X1 ◇ (X1 ◇ X2)) := by
  intro X1 X2
  calc (X1 ◇ (X2 ◇ X1))
    _ = (X2 ◇ (X1 ◇ X1)) := ((c_0_112 X1 X2).symm).symm
    _ = (X1 ◇ (X1 ◇ X2)) := (c_0_119 X1 X2).symm

theorem c_0_122 : ∀ (X1 X2 X3 : G), (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X1)))) = (X2 ◇ (X3 ◇ (X3 ◇ X1))) := by
  intro X1 X2 X3
  calc (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X1))))
    _ = (X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X1)))) := congrArg (X1 ◇ ·) (congrArg (X2 ◇ ·) ((c_0_113 X1 X3).symm))
    _ = (X2 ◇ (X1 ◇ (X3 ◇ X1))) := c_0_104 X1 X2 X3
    _ = (X2 ◇ (X3 ◇ (X3 ◇ X1))) := congrArg (X2 ◇ ·) (((c_0_113 X1 X3).symm).symm)

theorem c_0_123 : ∀ (X1 X2 X3 : G), ((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ X2))) = (X3 ◇ (X2 ◇ (X3 ◇ X1))) := by
  intro X1 X2 X3
  calc ((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ X2)))
    _ = (X3 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X2))) := ((c_0_118 ((X1 ◇ X2)) X3 X2).symm).symm
    _ = (X3 ◇ (X2 ◇ (X3 ◇ X1))) := congrArg (X3 ◇ ·) ((c_0_3 X2 X3 X1).symm)

theorem c_0_124 : ∀ (X1 X2 X3 : G), (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) = (X3 ◇ (X1 ◇ (X2 ◇ X2))) := by
  intro X1 X2 X3
  calc (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3))))
    _ = (X1 ◇ (X1 ◇ (X3 ◇ (X2 ◇ X2)))) := congrArg (X1 ◇ ·) (congrArg (X1 ◇ ·) (((c_0_119 X2 X3).symm).symm))
    _ = (X3 ◇ (X1 ◇ (X2 ◇ X2))) := c_0_120 X1 X3 X2

theorem c_0_125 : ∀ (X1 X2 X3 : G), (X1 ◇ ((X2 ◇ X3) ◇ X1)) = (X1 ◇ (X2 ◇ (X1 ◇ X3))) := by
  intro X1 X2 X3
  calc (X1 ◇ ((X2 ◇ X3) ◇ X1))
    _ = (X1 ◇ (X1 ◇ (X2 ◇ X3))) := ((c_0_121 X1 ((X2 ◇ X3))).symm).symm
    _ = (X1 ◇ (X2 ◇ (X1 ◇ X3))) := c_0_107 X1 X2 X3

theorem c_0_126 : ∀ (X1 X2 X3 : G), (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X3)))) = (X2 ◇ (X1 ◇ (X2 ◇ X3))) := by
  intro X1 X2 X3
  calc (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X3))))
    _ = (X1 ◇ ((X3 ◇ X1) ◇ (X2 ◇ (X2 ◇ X1)))) := congrArg (X1 ◇ ·) ((c_0_123 X3 X1 X2).symm)
    _ = ((X3 ◇ X1) ◇ (X2 ◇ (X2 ◇ X1))) := c_0_122 X1 ((X3 ◇ X1)) X2
    _ = (X2 ◇ (X1 ◇ (X2 ◇ X3))) := ((c_0_123 X3 X1 X2).symm).symm

theorem c_0_127 : ∀ (X1 X2 X3 : G), (X1 ◇ (X2 ◇ (X1 ◇ X3))) = (X3 ◇ (X2 ◇ (X1 ◇ X1))) := by
  intro X1 X2 X3
  calc (X1 ◇ (X2 ◇ (X1 ◇ X3)))
    _ = (X2 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) := (c_0_126 X2 X1 X3).symm
    _ = (X2 ◇ ((X1 ◇ (X1 ◇ X3)) ◇ X2)) := (c_0_125 X2 X1 ((X1 ◇ X3))).symm
    _ = (X2 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X3)))) := ((c_0_121 X2 ((X1 ◇ (X1 ◇ X3)))).symm).symm
    _ = (X3 ◇ (X2 ◇ (X1 ◇ X1))) := ((c_0_124 X2 X1 X3).symm).symm

theorem c_0_128 : ∀ (X1 X2 X3 : G), (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))) = (X2 ◇ (X3 ◇ (X1 ◇ X1))) := by
  intro X1 X2 X3
  calc (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1))))
    _ = (X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X1)))) := congrArg (X1 ◇ ·) (congrArg (X2 ◇ ·) ((c_0_112 X1 X3).symm))
    _ = (X2 ◇ (X1 ◇ (X3 ◇ X1))) := c_0_104 X1 X2 X3
    _ = (X2 ◇ (X3 ◇ (X1 ◇ X1))) := congrArg (X2 ◇ ·) (((c_0_112 X1 X3).symm).symm)

theorem c_0_129 : ∀ (X1 X2 X3 : G), (X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X3)))) = (X2 ◇ (X1 ◇ (X3 ◇ X3))) := by
  intro X1 X2 X3
  calc (X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X3))))
    _ = (X2 ◇ (X1 ◇ (X1 ◇ (X3 ◇ X3)))) := (c_0_110 X2 X1 ((X3 ◇ X3))).symm
    _ = (X2 ◇ (X1 ◇ (X3 ◇ X3))) := congrArg (X2 ◇ ·) (c_0_106 X1 X3)

theorem c_0_130 : ∀ (X1 X2 X3 : G), ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X2))) = (X2 ◇ ((X2 ◇ X3) ◇ X1)) := by
  intro X1 X2 X3
  calc ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X2)))
    _ = ((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ X2))) := ((c_0_29 X1 X2 X3).symm).symm
    _ = (X2 ◇ ((X2 ◇ X3) ◇ X1)) := c_0_102 X1 X2 X3

theorem c_0_131 : ∀ (X1 X2 X3 : G), (X1 ◇ (X2 ◇ (X3 ◇ X3))) = (X3 ◇ (X3 ◇ (X2 ◇ X1))) := by
  intro X1 X2 X3
  calc (X1 ◇ (X2 ◇ (X3 ◇ X3)))
    _ = (X3 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))) := (c_0_128 X3 X1 X2).symm
    _ = (X3 ◇ (X3 ◇ (X2 ◇ (X3 ◇ X1)))) := congrArg (X3 ◇ ·) ((c_0_127 X3 X2 X1).symm)
    _ = (X3 ◇ (X3 ◇ (X2 ◇ X1))) := ((c_0_115 X3 X2 X1).symm).symm

theorem c_0_132 : ∀ (X1 X2 X3 : G), ((X1 ◇ X2) ◇ (X3 ◇ X3)) = (X1 ◇ (X3 ◇ (X3 ◇ X2))) := by
  intro X1 X2 X3
  calc ((X1 ◇ X2) ◇ (X3 ◇ X3))
    _ = (X3 ◇ (X3 ◇ (X1 ◇ X2))) := (c_0_119 X3 ((X1 ◇ X2))).symm
    _ = (X1 ◇ (X3 ◇ (X3 ◇ X2))) := (c_0_118 X1 X3 X2).symm

theorem c_0_133 : ∀ (X1 X2 X3 : G), (X1 ◇ (X2 ◇ (X1 ◇ X3))) = (X2 ◇ ((X2 ◇ X1) ◇ X3)) := by
  intro X1 X2 X3
  calc (X1 ◇ (X2 ◇ (X1 ◇ X3)))
    _ = ((X3 ◇ X2) ◇ (X1 ◇ (X1 ◇ X2))) := (c_0_123 X3 X2 X1).symm
    _ = ((X3 ◇ X2) ◇ (X2 ◇ (X1 ◇ X2))) := congrArg ((X3 ◇ X2) ◇ ·) ((c_0_113 X2 X1).symm)
    _ = (X2 ◇ ((X2 ◇ X1) ◇ X3)) := ((c_0_102 X3 X2 X1).symm).symm

theorem c_0_134 : ∀ (X1 X2 X3 : G), (X1 ◇ (X2 ◇ ((X2 ◇ X1) ◇ X3))) = (X2 ◇ ((X2 ◇ X1) ◇ X3)) := by
  intro X1 X2 X3
  calc (X1 ◇ (X2 ◇ ((X2 ◇ X1) ◇ X3)))
    _ = (X1 ◇ ((X3 ◇ X2) ◇ (X1 ◇ (X2 ◇ X2)))) := congrArg (X1 ◇ ·) ((c_0_130 X3 X2 X1).symm)
    _ = ((X3 ◇ X2) ◇ (X1 ◇ (X2 ◇ X2))) := c_0_129 X1 ((X3 ◇ X2)) X2
    _ = (X2 ◇ ((X2 ◇ X1) ◇ X3)) := ((c_0_130 X3 X2 X1).symm).symm

theorem c_0_135 : ∀ (X1 X2 X3 : G), (X1 ◇ (X2 ◇ (X2 ◇ X3))) = (X2 ◇ (X3 ◇ (X2 ◇ X1))) := by
  intro X1 X2 X3
  calc (X1 ◇ (X2 ◇ (X2 ◇ X3)))
    _ = (X3 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) := (c_0_122 X3 X1 X2).symm
    _ = (X3 ◇ ((X1 ◇ X3) ◇ (X2 ◇ X2))) := congrArg (X3 ◇ ·) ((c_0_132 X1 X3 X2).symm)
    _ = (X2 ◇ (X2 ◇ ((X1 ◇ X3) ◇ X3))) := ((c_0_131 X3 ((X1 ◇ X3)) X2).symm).symm
    _ = (X2 ◇ (X3 ◇ (X2 ◇ X1))) := congrArg (X2 ◇ ·) ((c_0_3 X3 X2 X1).symm)

theorem c_0_136 : ∀ (X1 X2 X3 : G), (X1 ◇ ((X1 ◇ X2) ◇ X3)) = (X2 ◇ (X2 ◇ (X1 ◇ X3))) := by
  intro X1 X2 X3
  calc (X1 ◇ ((X1 ◇ X2) ◇ X3))
    _ = (X2 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X3))) := (c_0_134 X2 X1 X3).symm
    _ = (X2 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X3)))) := congrArg (X2 ◇ ·) ((c_0_133 X2 X1 X3).symm)
    _ = (X2 ◇ (X2 ◇ (X1 ◇ X3))) := ((c_0_115 X2 X1 X3).symm).symm

theorem c_0_137 : ∀ (X1 X2 X3 : G), (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X3))) = (X1 ◇ ((X1 ◇ X2) ◇ X3)) := by
  intro X1 X2 X3
  calc (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X3)))
    _ = ((X1 ◇ X2) ◇ (X1 ◇ X3)) := ((c_0_111 X1 X2 X3).symm).symm
    _ = (X1 ◇ ((X1 ◇ X2) ◇ X3)) := c_0_114 X1 X2 X3

theorem c_0_138 : ∀ (X1 X2 X3 : G), (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X1)))) = (X2 ◇ (X2 ◇ (X3 ◇ X1))) := by
  intro X1 X2 X3
  calc (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X1))))
    _ = (X1 ◇ (X3 ◇ (X2 ◇ (X2 ◇ X1)))) := congrArg (X1 ◇ ·) ((c_0_118 X3 X2 X1).symm)
    _ = (X3 ◇ (X2 ◇ (X2 ◇ X1))) := c_0_122 X1 X3 X2
    _ = (X2 ◇ (X2 ◇ (X3 ◇ X1))) := ((c_0_118 X3 X2 X1).symm).symm

theorem c_0_139 : ∀ (X1 X2 X3 : G), (X1 ◇ (X2 ◇ (X2 ◇ X3))) = (X2 ◇ (X2 ◇ (X3 ◇ X1))) := by
  intro X1 X2 X3
  calc (X1 ◇ (X2 ◇ (X2 ◇ X3)))
    _ = (X2 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) := (c_0_108 X2 X1 X3).symm
    _ = (X2 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X1)))) := congrArg (X2 ◇ ·) (c_0_135 X1 X2 X3)
    _ = (X2 ◇ (X2 ◇ (X3 ◇ X1))) := ((c_0_115 X2 X3 X1).symm).symm

theorem c_0_140 : ∀ (X1 X2 X3 : G), (X1 ◇ ((X1 ◇ X2) ◇ X3)) = (X3 ◇ (X2 ◇ (X1 ◇ X1))) := by
  intro X1 X2 X3
  calc (X1 ◇ ((X1 ◇ X2) ◇ X3))
    _ = (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X3))) := (c_0_137 X1 X2 X3).symm
    _ = (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X3))) := congrArg (X1 ◇ ·) ((c_0_114 X1 X2 X3).symm)
    _ = (X2 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X3)))) := ((c_0_136 X1 X2 ((X1 ◇ X3))).symm).symm
    _ = (X3 ◇ (X2 ◇ (X1 ◇ X1))) := ((c_0_124 X2 X1 X3).symm).symm

theorem c_0_141 : ∀ (X1 X2 X3 : G), (X1 ◇ (X2 ◇ (X1 ◇ X3))) = (X1 ◇ (X1 ◇ (X3 ◇ X2))) := by
  intro X1 X2 X3
  calc (X1 ◇ (X2 ◇ (X1 ◇ X3)))
    _ = (X1 ◇ (X1 ◇ ((X3 ◇ X2) ◇ X2))) := congrArg (X1 ◇ ·) (c_0_3 X2 X1 X3)
    _ = (X2 ◇ (X1 ◇ (X1 ◇ (X3 ◇ X2)))) := (c_0_139 X2 X1 ((X3 ◇ X2))).symm
    _ = (X1 ◇ (X1 ◇ (X3 ◇ X2))) := ((c_0_138 X2 X1 X3).symm).symm

theorem c_0_142 : ∀ (X1 X2 X3 X4 : G), (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) = (X1 ◇ (X3 ◇ (X2 ◇ (X1 ◇ X4)))) := by
  intro X1 X2 X3 X4
  calc (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))
    _ = (X1 ◇ (X1 ◇ (X3 ◇ ((X4 ◇ X2) ◇ X2)))) := congrArg (X1 ◇ ·) (congrArg (X1 ◇ ·) (c_0_3 X2 X3 X4))
    _ = (X1 ◇ (X3 ◇ (X1 ◇ ((X4 ◇ X2) ◇ X2)))) := c_0_107 X1 X3 (((X4 ◇ X2) ◇ X2))
    _ = (X1 ◇ (X3 ◇ (X2 ◇ (X1 ◇ X4)))) := congrArg (X1 ◇ ·) (congrArg (X3 ◇ ·) ((c_0_3 X2 X1 X4).symm))

theorem c_0_143 : ∀ (X1 X2 X3 : G), (X1 ◇ ((X1 ◇ X2) ◇ X3)) = (X1 ◇ (X2 ◇ (X1 ◇ X3))) := by
  intro X1 X2 X3
  calc (X1 ◇ ((X1 ◇ X2) ◇ X3))
    _ = (X3 ◇ (X2 ◇ (X1 ◇ X1))) := ((c_0_140 X1 X2 X3).symm).symm
    _ = (X1 ◇ (X2 ◇ (X1 ◇ X3))) := (c_0_127 X1 X2 X3).symm

theorem c_0_144 : ∀ (X1 X2 X3 X4 : G), (X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X4))) = (X1 ◇ (X2 ◇ (X4 ◇ (X1 ◇ X3)))) := by
  intro X1 X2 X3 X4
  calc (X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X4)))
    _ = (X1 ◇ (X1 ◇ (X4 ◇ (X2 ◇ X3)))) := ((c_0_141 X1 ((X2 ◇ X3)) X4).symm).symm
    _ = (X1 ◇ (X2 ◇ (X4 ◇ (X1 ◇ X3)))) := c_0_142 X1 X4 X2 X3

theorem c_0_145 : ∀ (X1 X2 : G), (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (X2 ◇ X1)) := by
  intro X1 X2
  calc (X1 ◇ (X1 ◇ X2))
    _ = (X2 ◇ (X1 ◇ X1)) := ((c_0_119 X1 X2).symm).symm
    _ = (X2 ◇ (X2 ◇ X1)) := (c_0_116 X2 X1).symm

theorem c_0_146 : ∀ (X1 X2 X3 : G), (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2)))) = (X3 ◇ (X1 ◇ (X2 ◇ X2))) := by
  intro X1 X2 X3
  calc (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2))))
    _ = (X1 ◇ (X1 ◇ (X3 ◇ (X2 ◇ X2)))) := congrArg (X1 ◇ ·) (congrArg (X1 ◇ ·) (((c_0_112 X2 X3).symm).symm))
    _ = (X3 ◇ (X1 ◇ (X2 ◇ X2))) := c_0_120 X1 X3 X2

theorem c_0_147 : ∀ (X1 X2 X3 : G), ((X1 ◇ X2) ◇ (X1 ◇ X3)) = (X1 ◇ (X2 ◇ (X1 ◇ X3))) := by
  intro X1 X2 X3
  calc ((X1 ◇ X2) ◇ (X1 ◇ X3))
    _ = (X1 ◇ ((X1 ◇ X2) ◇ X3)) := ((c_0_114 X1 X2 X3).symm).symm
    _ = (X1 ◇ (X2 ◇ (X1 ◇ X3))) := c_0_143 X1 X2 X3

theorem c_0_148 : ∀ (X1 X2 X3 X4 : G), (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ (X1 ◇ X3)))) = (X1 ◇ ((X3 ◇ (X1 ◇ X2)) ◇ X4)) := by
  intro X1 X2 X3 X4
  calc (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ (X1 ◇ X3))))
    _ = (X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ (X1 ◇ X4))) := (c_0_144 X1 ((X2 ◇ X3)) X3 X4).symm
    _ = (X1 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X4)) := (c_0_143 X1 (((X2 ◇ X3) ◇ X3)) X4).symm
    _ = (X1 ◇ ((X3 ◇ (X1 ◇ X2)) ◇ X4)) := congrArg (X1 ◇ ·) (congrArg (· ◇ X4) ((c_0_3 X3 X1 X2).symm))

theorem c_0_149 : ∀ (X1 X2 X3 : G), ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X3)) = (X1 ◇ ((X1 ◇ X3) ◇ X2)) := by
  intro X1 X2 X3
  calc ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X3))
    _ = (X3 ◇ (X3 ◇ (X1 ◇ X2))) := (c_0_145 X3 ((X1 ◇ X2))).symm
    _ = (X1 ◇ ((X1 ◇ X3) ◇ X2)) := (c_0_136 X1 X3 X2).symm

theorem c_0_150 : ∀ (X1 X2 X3 : G), (X1 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X1 ◇ (X3 ◇ X3))) := by
  intro X1 X2 X3
  calc (X1 ◇ (X1 ◇ (X2 ◇ X3)))
    _ = (X3 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))) := (c_0_138 X3 X1 X2).symm
    _ = ((X3 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X1)) := (c_0_132 X3 ((X2 ◇ X3)) X1).symm
    _ = (X1 ◇ (X1 ◇ (X3 ◇ (X2 ◇ X3)))) := (c_0_119 X1 ((X3 ◇ (X2 ◇ X3)))).symm
    _ = (X2 ◇ (X1 ◇ (X3 ◇ X3))) := ((c_0_146 X1 X3 X2).symm).symm

theorem c_0_151 : ∀ (X1 X2 X3 X4 : G), ((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X4)) = (X2 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X4)) := by
  intro X1 X2 X3 X4
  calc ((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X4))
    _ = ((X2 ◇ ((X3 ◇ X1) ◇ X1)) ◇ (X2 ◇ X4)) := congrArg (· ◇ (X2 ◇ X4)) (c_0_3 X1 X2 X3)
    _ = (X2 ◇ (((X3 ◇ X1) ◇ X1) ◇ (X2 ◇ X4))) := c_0_147 X2 (((X3 ◇ X1) ◇ X1)) X4
    _ = (X2 ◇ ((X3 ◇ X1) ◇ (X4 ◇ (X2 ◇ X1)))) := ((c_0_144 X2 ((X3 ◇ X1)) X1 X4).symm).symm
    _ = (X2 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X4)) := ((c_0_148 X2 X3 X1 X4).symm).symm

theorem c_0_152 : ∀ (X1 X2 X3 : G), (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X1)))) = (X2 ◇ (X3 ◇ (X2 ◇ X1))) := by
  intro X1 X2 X3
  calc (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X1))))
    _ = (X1 ◇ (X3 ◇ (X2 ◇ (X2 ◇ X1)))) := congrArg (X1 ◇ ·) ((c_0_110 X3 X2 X1).symm)
    _ = (X3 ◇ (X2 ◇ (X2 ◇ X1))) := c_0_122 X1 X3 X2
    _ = (X2 ◇ (X3 ◇ (X2 ◇ X1))) := ((c_0_110 X3 X2 X1).symm).symm

theorem c_0_153 : ∀ (X1 X2 X3 X4 : G), (X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) = (X4 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) := by
  intro X1 X2 X3 X4
  calc (X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4))
    _ = (X1 ◇ ((X3 ◇ X2) ◇ (X4 ◇ (X1 ◇ X2)))) := (c_0_148 X1 X3 X2 X4).symm
    _ = (X1 ◇ (((X3 ◇ X2) ◇ X2) ◇ (X1 ◇ X4))) := (c_0_144 X1 ((X3 ◇ X2)) X2 X4).symm
    _ = (X4 ◇ (X1 ◇ (X1 ◇ ((X3 ◇ X2) ◇ X2)))) := (c_0_135 X4 X1 (((X3 ◇ X2) ◇ X2))).symm
    _ = (X4 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) := congrArg (X4 ◇ ·) (congrArg (X1 ◇ ·) ((c_0_3 X2 X1 X3).symm))

theorem c_0_154 : ∀ (X1 X2 X3 X4 : G), (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X4)))) = (X2 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X4)))) := by
  intro X1 X2 X3 X4
  calc (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X4))))
    _ = (X1 ◇ (X2 ◇ (X2 ◇ ((X4 ◇ X3) ◇ X3)))) := congrArg (X1 ◇ ·) (congrArg (X2 ◇ ·) (c_0_3 X3 X2 X4))
    _ = (X2 ◇ (X2 ◇ (X1 ◇ ((X4 ◇ X3) ◇ X3)))) := c_0_118 X1 X2 (((X4 ◇ X3) ◇ X3))
    _ = (X2 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X4)))) := congrArg (X2 ◇ ·) (congrArg (X2 ◇ ·) ((c_0_3 X3 X1 X4).symm))

theorem c_0_155 : ∀ (X1 X2 X3 : G), ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X3)) = (X1 ◇ (X3 ◇ (X1 ◇ X2))) := by
  intro X1 X2 X3
  calc ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X3))
    _ = (X1 ◇ ((X1 ◇ X3) ◇ X2)) := ((c_0_149 X1 X2 X3).symm).symm
    _ = (X1 ◇ (X3 ◇ (X1 ◇ X2))) := c_0_143 X1 X3 X2

theorem c_0_156 : ∀ (X1 X2 X3 : G), ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X3)) = (X1 ◇ (X3 ◇ (X2 ◇ X2))) := by
  intro X1 X2 X3
  calc ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X3))
    _ = (X3 ◇ (X3 ◇ (X1 ◇ X2))) := (c_0_145 X3 ((X1 ◇ X2))).symm
    _ = (X1 ◇ (X3 ◇ (X2 ◇ X2))) := c_0_150 X3 X1 X2

theorem c_0_157 : ∀ (X1 X2 X3 X4 : G), (X1 ◇ (X2 ◇ ((X3 ◇ (X2 ◇ X4)) ◇ X4))) = ((X2 ◇ X4) ◇ (X1 ◇ X3)) := by
  intro X1 X2 X3 X4
  calc (X1 ◇ (X2 ◇ ((X3 ◇ (X2 ◇ X4)) ◇ X4)))
    _ = (X1 ◇ ((X3 ◇ (X2 ◇ X4)) ◇ (X2 ◇ X4))) := congrArg (X1 ◇ ·) ((c_0_151 X3 X2 X4 X4).symm)
    _ = ((X2 ◇ X4) ◇ (X1 ◇ X3)) := (c_0_3 ((X2 ◇ X4)) X1 X3).symm

theorem c_0_158 : ∀ (X1 X2 X3 : G), (X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X3)) = (X1 ◇ (X2 ◇ (X1 ◇ X3))) := by
  intro X1 X2 X3
  calc (X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X3))
    _ = (X3 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) := ((c_0_153 X1 X2 X3 X3).symm).symm
    _ = (X1 ◇ (X2 ◇ (X1 ◇ X3))) := c_0_152 X3 X1 X2

theorem c_0_159 : ∀ (X1 X2 X3 : G), (X1 ◇ (X2 ◇ (X3 ◇ X3))) = (X2 ◇ (X3 ◇ (X3 ◇ X1))) := by
  intro X1 X2 X3
  calc (X1 ◇ (X2 ◇ (X3 ◇ X3)))
    _ = (X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X1)))) := (c_0_124 X2 X3 X1).symm
    _ = (X2 ◇ (X3 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X1))))) := congrArg (X2 ◇ ·) ((c_0_108 X3 X2 X1).symm)
    _ = (X3 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X1)))) := ((c_0_126 X2 X3 ((X3 ◇ X1))).symm).symm
    _ = (X2 ◇ (X3 ◇ (X3 ◇ X1))) := ((c_0_108 X3 X2 X1).symm).symm

theorem c_0_160 : ∀ (X1 X2 X3 X4 : G), ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X4))) = (X1 ◇ (X4 ◇ (X3 ◇ (X4 ◇ X2)))) := by
  intro X1 X2 X3 X4
  calc ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X4)))
    _ = (X4 ◇ (X4 ◇ (X3 ◇ (X1 ◇ X2)))) := ((c_0_131 ((X1 ◇ X2)) X3 X4).symm).symm
    _ = (X1 ◇ (X4 ◇ (X3 ◇ (X4 ◇ X2)))) := (c_0_154 X1 X4 X3 X2).symm

theorem c_0_161 : ∀ (X1 X2 X3 X4 : G), (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X4)))) = (X2 ◇ (X1 ◇ (X4 ◇ (X1 ◇ X3)))) := by
  intro X1 X2 X3 X4
  calc (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X4))))
    _ = (X1 ◇ ((X2 ◇ X4) ◇ (X3 ◇ X3))) := congrArg (X1 ◇ ·) ((c_0_132 X2 X4 X3).symm)
    _ = ((X1 ◇ X3) ◇ ((X1 ◇ X3) ◇ (X2 ◇ X4))) := (c_0_156 X1 X3 ((X2 ◇ X4))).symm
    _ = (X2 ◇ ((X1 ◇ X3) ◇ ((X1 ◇ X3) ◇ X4))) := (c_0_118 X2 ((X1 ◇ X3)) X4).symm
    _ = (X2 ◇ (X1 ◇ (X4 ◇ (X1 ◇ X3)))) := congrArg (X2 ◇ ·) (((c_0_155 X1 X3 X4).symm).symm)

theorem c_0_162 : ∀ (X1 X2 X3 X4 : G), (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X4)))) = ((X2 ◇ X4) ◇ (X1 ◇ X3)) := by
  intro X1 X2 X3 X4
  calc (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X4))))
    _ = (X1 ◇ (X2 ◇ ((X3 ◇ (X2 ◇ X4)) ◇ X4))) := congrArg (X1 ◇ ·) ((c_0_158 X2 X3 X4).symm)
    _ = ((X2 ◇ X4) ◇ (X1 ◇ X3)) := c_0_157 X1 X2 X3 X4

theorem c_0_163 : ∀ (X1 X2 X3 : G), (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X3)))) = (X3 ◇ (X2 ◇ (X1 ◇ X1))) := by
  intro X1 X2 X3
  calc (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X3))))
    _ = ((X1 ◇ (X1 ◇ X3)) ◇ (X2 ◇ X2)) := (c_0_132 X1 ((X1 ◇ X3)) X2).symm
    _ = (X2 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X3)))) := (c_0_119 X2 ((X1 ◇ (X1 ◇ X3)))).symm
    _ = (X3 ◇ (X2 ◇ (X1 ◇ X1))) := ((c_0_124 X2 X1 X3).symm).symm

theorem c_0_164 : ∀ (X1 X2 X3 X4 : G), (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X4)))) = (X2 ◇ (X3 ◇ (X1 ◇ (X3 ◇ X4)))) := by
  intro X1 X2 X3 X4
  calc (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X4))))
    _ = (X1 ◇ (X3 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X4))))) := congrArg (X1 ◇ ·) ((c_0_108 X3 X2 X4).symm)
    _ = ((X1 ◇ (X3 ◇ X4)) ◇ (X2 ◇ (X3 ◇ X3))) := (c_0_160 X1 ((X3 ◇ X4)) X2 X3).symm
    _ = (X2 ◇ (X3 ◇ (X3 ◇ (X1 ◇ (X3 ◇ X4))))) := ((c_0_159 ((X1 ◇ (X3 ◇ X4))) X2 X3).symm).symm
    _ = (X2 ◇ (X3 ◇ (X1 ◇ (X3 ◇ X4)))) := congrArg (X2 ◇ ·) (((c_0_103 X3 X1 X4).symm).symm)

theorem c_0_165 : ∀ (X1 X2 X3 X4 : G), (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X4)))) = ((X1 ◇ X3) ◇ (X2 ◇ X4)) := by
  intro X1 X2 X3 X4
  calc (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X4))))
    _ = (X2 ◇ (X1 ◇ (X4 ◇ (X1 ◇ X3)))) := ((c_0_161 X1 X2 X3 X4).symm).symm
    _ = ((X1 ◇ X3) ◇ (X2 ◇ X4)) := c_0_162 X2 X1 X4 X3

theorem c_0_166 : ∀ (X1 X2 X3 : G), (X1 ◇ (X2 ◇ (X3 ◇ X3))) = (X2 ◇ (X2 ◇ (X3 ◇ X1))) := by
  intro X1 X2 X3
  calc (X1 ◇ (X2 ◇ (X3 ◇ X3)))
    _ = (X3 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X1)))) := (c_0_163 X3 X2 X1).symm
    _ = (X3 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X1)))) := congrArg (X3 ◇ ·) (c_0_107 X2 X3 X1)
    _ = (X2 ◇ (X3 ◇ (X2 ◇ X1))) := ((c_0_126 X3 X2 X1).symm).symm
    _ = (X2 ◇ (X2 ◇ (X3 ◇ X1))) := (c_0_107 X2 X3 X1).symm

theorem c_0_167 : ∀ (X1 X2 X3 X4 : G), ((X1 ◇ X2) ◇ (X3 ◇ X4)) = ((X2 ◇ X4) ◇ (X3 ◇ X1)) := by
  intro X1 X2 X3 X4
  calc ((X1 ◇ X2) ◇ (X3 ◇ X4))
    _ = (X1 ◇ (X3 ◇ (X2 ◇ (X2 ◇ X4)))) := (c_0_165 X1 X3 X2 X4).symm
    _ = (X3 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X4)))) := c_0_164 X1 X3 X2 X4
    _ = ((X2 ◇ X4) ◇ (X3 ◇ X1)) := ((c_0_162 X3 X2 X1 X4).symm).symm

theorem c_0_169 : ∀ (X1 X2 X3 : G), (X1 ◇ (X2 ◇ (X3 ◇ X3))) = (X3 ◇ (X2 ◇ (X1 ◇ X1))) := by
  intro X1 X2 X3
  calc (X1 ◇ (X2 ◇ (X3 ◇ X3)))
    _ = (X2 ◇ (X2 ◇ (X3 ◇ X1))) := c_0_166 X1 X2 X3
    _ = ((X3 ◇ X1) ◇ ((X3 ◇ X1) ◇ X2)) := c_0_145 X2 ((X3 ◇ X1))
    _ = (X3 ◇ (X2 ◇ (X1 ◇ X1))) := ((c_0_156 X3 X1 X2).symm).symm

theorem c_0_170 : ∀ (X1 X2 X3 : G), (X1 ◇ (X2 ◇ (X3 ◇ X3))) = (X1 ◇ (X3 ◇ X2)) := by
  intro X1 X2 X3
  calc (X1 ◇ (X2 ◇ (X3 ◇ X3)))
    _ = ((X1 ◇ X3) ◇ ((X1 ◇ X3) ◇ X2)) := (c_0_156 X1 X3 X2).symm
    _ = ((X2 ◇ X1) ◇ ((X1 ◇ X3) ◇ X3)) := (c_0_167 X2 X1 ((X1 ◇ X3)) X3).symm
    _ = (X3 ◇ ((X2 ◇ X1) ◇ X1)) := (c_0_3 X3 ((X2 ◇ X1)) X1).symm
    _ = (X1 ◇ (X3 ◇ X2)) := (c_0_3 X1 X3 X2).symm

theorem c_0_171 : ∀ (X1 X2 X3 : G), (X1 ◇ (X2 ◇ (X3 ◇ X3))) = (X3 ◇ (X1 ◇ (X2 ◇ X2))) := by
  intro X1 X2 X3
  calc (X1 ◇ (X2 ◇ (X3 ◇ X3)))
    _ = (X1 ◇ (X3 ◇ ((X3 ◇ X2) ◇ X2))) := congrArg (X1 ◇ ·) (c_0_3 X2 X3 X3)
    _ = (X1 ◇ ((X3 ◇ X2) ◇ (X3 ◇ X2))) := congrArg (X1 ◇ ·) ((c_0_114 X3 X2 X2).symm)
    _ = (X1 ◇ (X1 ◇ (X3 ◇ X2))) := (c_0_116 X1 ((X3 ◇ X2))).symm
    _ = (X3 ◇ (X1 ◇ (X2 ◇ X2))) := ((c_0_150 X1 X3 X2).symm).symm

theorem c_0_173 : ∀ (X1 X2 X3 : G), (X1 ◇ (X2 ◇ X3)) = (X2 ◇ (X1 ◇ X3)) := by
  intro X1 X2 X3
  calc (X1 ◇ (X2 ◇ X3))
    _ = (X1 ◇ (X3 ◇ (X2 ◇ X2))) := (c_0_170 X1 X3 X2).symm
    _ = (X2 ◇ (X3 ◇ (X1 ◇ X1))) := c_0_169 X1 X3 X2
    _ = (X2 ◇ (X1 ◇ X3)) := ((c_0_170 X2 X3 X1).symm).symm

theorem c_0_174 : ∀ (X1 X2 X3 : G), (X1 ◇ (X2 ◇ X3)) = (X2 ◇ (X3 ◇ X1)) := by
  intro X1 X2 X3
  calc (X1 ◇ (X2 ◇ X3))
    _ = (X1 ◇ (X3 ◇ (X2 ◇ X2))) := (c_0_170 X1 X3 X2).symm
    _ = (X2 ◇ (X1 ◇ (X3 ◇ X3))) := c_0_171 X1 X3 X2
    _ = (X2 ◇ (X3 ◇ X1)) := ((c_0_170 X2 X1 X3).symm).symm

theorem c_0_176 : ∀ (X1 X2 X3 : G), (X1 ◇ (X2 ◇ X3)) = (X1 ◇ (X3 ◇ X2)) := by
  intro X1 X2 X3
  calc (X1 ◇ (X2 ◇ X3))
    _ = (X3 ◇ (X1 ◇ X2)) := (c_0_174 X3 X1 X2).symm
    _ = (X1 ◇ (X3 ◇ X2)) := c_0_173 X3 X1 X2

theorem triplePermutation :
    (∀ (a b c : G), a ◇ (b ◇ c) = b ◇ (a ◇ c)) ∧
    (∀ (a b c : G), a ◇ (b ◇ c) = a ◇ (c ◇ b)) := by
  exact ⟨c_0_173, c_0_176⟩

end Equation55300Kernel

end submission

open submission

                   
                          

def submission : Goal := by
  intro G _ h
  letI : Equation55300Kernel.Law G := ⟨h⟩
  rcases Equation55300Kernel.triplePermutation (G := G) with ⟨swapOuter, swapInner⟩
  intro x y z
  calc
    x ◇ (y ◇ z) = y ◇ ((z ◇ x) ◇ x) := h x y z
    _ = y ◇ (x ◇ (z ◇ x)) := swapInner y (z ◇ x) x
    _ = y ◇ (x ◇ (x ◇ z)) := congrArg (fun t => y ◇ t) (swapInner x z x)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_55300_to_54391 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_55300_to_54391
