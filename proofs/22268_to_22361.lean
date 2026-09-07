-- Equation22268 → Equation22361
-- Recorded verdict: true
-- Premise: x = (x ◇ (x ◇ y)) ◇ ((y ◇ z) ◇ z)
-- Conclusion: x = (x ◇ (y ◇ z)) ◇ ((x ◇ x) ◇ x)
-- Original submission SHA-256: 4ec12f3bef86de461d3ee53c2511696955bfe1d519de92fd361188d22c086ca8
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (x ◇ (x ◇ y)) ◇ ((y ◇ z) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (x ◇ (y ◇ z)) ◇ ((x ◇ x) ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
set_option linter.unusedVariables false
set_option maxHeartbeats 2400000
set_option maxRecDepth 100000
def submission : Goal := by
 intro G _ h
 intro x y z
 have c_0_3 : ∀ (X1 X2 X3 : G), X1 = ((X1◇(X1◇X2))◇((X2◇X3)◇X3)) := by
  intro X1 X2 X3
  exact h X1 X2 X3
 have c_0_4 : ∀ (X1 X2 : G), ((X1◇(X1◇(X2◇X2)))◇(X2◇X2)) = X1 := by
  intro X1 X2
  calc ((X1◇(X1◇(X2◇X2)))◇(X2◇X2))
   _ = ((X1◇(X1◇(X2◇X2)))◇(((X2◇X2)◇((X2◇X2)◇X2))◇((X2◇X2)◇X2))) := congrArg ((X1◇(X1◇(X2◇X2)))◇·) (((c_0_3 ((X2◇X2)) X2 X2).symm).symm)
   _ = X1 := (c_0_3 X1 ((X2◇X2)) (((X2◇X2)◇X2))).symm
 have c_0_5 : ∀ (X1 X2 : G), (((X1◇(X1◇(X2◇X2)))◇X1)◇(X2◇X2)) = (X1◇(X1◇(X2◇X2))) := by
  intro X1 X2
  calc (((X1◇(X1◇(X2◇X2)))◇X1)◇(X2◇X2))
   _ = (((X1◇(X1◇(X2◇X2)))◇((X1◇(X1◇(X2◇X2)))◇(X2◇X2)))◇(X2◇X2)) := congrArg (·◇(X2◇X2)) (congrArg ((X1◇(X1◇(X2◇X2)))◇·) ((c_0_4 X1 X2).symm))
   _ = (X1◇(X1◇(X2◇X2))) := c_0_4 ((X1◇(X1◇(X2◇X2)))) X2
 have c_0_6x : ∀ (X0 X1 X2 : G), X0 = ((X0◇(X0◇((X1◇(X1◇(X2◇X2)))◇X1)))◇((X1◇(X1◇(X2◇X2)))◇(X2◇X2))) := by
  intro X0 X1 X2
  calc X0
   _ = ((X0◇(X0◇((X1◇(X1◇(X2◇X2)))◇X1)))◇((((X1◇(X1◇(X2◇X2)))◇X1)◇(X2◇X2))◇(X2◇X2))) := c_0_3 X0 (((X1◇(X1◇(X2◇X2)))◇X1)) ((X2◇X2))
   _ = ((X0◇(X0◇((X1◇(X1◇(X2◇X2)))◇X1)))◇((X1◇(X1◇(X2◇X2)))◇(X2◇X2))) := congrArg ((X0◇(X0◇((X1◇(X1◇(X2◇X2)))◇X1)))◇·) (congrArg (·◇(X2◇X2)) (c_0_5 X1 X2))
 have c_0_6 : ∀ (X1 X2 X3 : G), ((X1◇(X1◇((X2◇(X2◇(X3◇X3)))◇X2)))◇X2) = X1 := by
  intro X1 X2 X3
  have strict_rw_1 := ((c_0_6x X1 X2 X3).symm)
  rw [c_0_4] at strict_rw_1
  exact strict_rw_1
 have c_0_7 : ∀ (X1 X2 X3 X4 : G), (((X1◇(X1◇((X2◇(X2◇(X3◇X3)))◇X2)))◇X1)◇((X2◇X4)◇X4)) = (X1◇(X1◇((X2◇(X2◇(X3◇X3)))◇X2))) := by
  intro X1 X2 X3 X4
  calc (((X1◇(X1◇((X2◇(X2◇(X3◇X3)))◇X2)))◇X1)◇((X2◇X4)◇X4))
   _ = (((X1◇(X1◇((X2◇(X2◇(X3◇X3)))◇X2)))◇((X1◇(X1◇((X2◇(X2◇(X3◇X3)))◇X2)))◇X2))◇((X2◇X4)◇X4)) := congrArg (·◇((X2◇X4)◇X4)) (congrArg ((X1◇(X1◇((X2◇(X2◇(X3◇X3)))◇X2)))◇·) ((c_0_6 X1 X2 X3).symm))
   _ = (X1◇(X1◇((X2◇(X2◇(X3◇X3)))◇X2))) := (c_0_3 ((X1◇(X1◇((X2◇(X2◇(X3◇X3)))◇X2)))) X2 X4).symm
 have c_0_8 : ∀ (X1 X2 X3 X4 : G), ((X1◇(X1◇(X2◇(X2◇((X3◇(X3◇(X4◇X4)))◇X3)))))◇(X2◇X3)) = X1 := by
  intro X1 X2 X3 X4
  calc ((X1◇(X1◇(X2◇(X2◇((X3◇(X3◇(X4◇X4)))◇X3)))))◇(X2◇X3))
   _ = ((X1◇(X1◇(X2◇(X2◇((X3◇(X3◇(X4◇X4)))◇X3)))))◇(((X2◇(X2◇((X3◇(X3◇(X4◇X4)))◇X3)))◇X3)◇X3)) := congrArg ((X1◇(X1◇(X2◇(X2◇((X3◇(X3◇(X4◇X4)))◇X3)))))◇·) (congrArg (·◇X3) ((c_0_6 X2 X3 X4).symm))
   _ = X1 := (c_0_3 X1 ((X2◇(X2◇((X3◇(X3◇(X4◇X4)))◇X3)))) X3).symm
 have c_0_9 : ∀ (X1 X2 X3 : G), (X1◇((X1◇X2)◇X2)) = (X1◇(X1◇((X1◇(X1◇(X3◇X3)))◇X1))) := by
  intro X1 X2 X3
  calc (X1◇((X1◇X2)◇X2))
   _ = (((X1◇(X1◇((X1◇(X1◇(X3◇X3)))◇X1)))◇X1)◇((X1◇X2)◇X2)) := congrArg (·◇((X1◇X2)◇X2)) ((c_0_6 X1 X1 X3).symm)
   _ = (X1◇(X1◇((X1◇(X1◇(X3◇X3)))◇X1))) := c_0_7 X1 X1 X3 X2
 have c_0_10 : ∀ (X1 X2 : G), (X1◇(((X1◇X1)◇X2)◇X2)) = (X1◇(X1◇X1)) := by
  intro X1 X2
  calc (X1◇(((X1◇X1)◇X2)◇X2))
   _ = (((X1◇(X1◇X1))◇((X1◇(X1◇X1))◇(X1◇X1)))◇(((X1◇X1)◇X2)◇X2)) := congrArg (·◇(((X1◇X1)◇X2)◇X2)) (((c_0_3 X1 X1 ((X1◇X1))).symm).symm)
   _ = (X1◇(X1◇X1)) := (c_0_3 ((X1◇(X1◇X1))) ((X1◇X1)) X2).symm
 have c_0_11 : ∀ (X1 X2 X3 : G), ((X1◇(X1◇(X2◇(X2◇(X3◇X3)))))◇(X2◇(X3◇X3))) = X1 := by
  intro X1 X2 X3
  calc ((X1◇(X1◇(X2◇(X2◇(X3◇X3)))))◇(X2◇(X3◇X3)))
   _ = ((X1◇(X1◇(X2◇(X2◇(X3◇X3)))))◇(((X2◇(X2◇(X3◇X3)))◇(X3◇X3))◇(X3◇X3))) := congrArg ((X1◇(X1◇(X2◇(X2◇(X3◇X3)))))◇·) (congrArg (·◇(X3◇X3)) ((c_0_4 X2 X3).symm))
   _ = X1 := (c_0_3 X1 ((X2◇(X2◇(X3◇X3)))) ((X3◇X3))).symm
 have c_0_12 : ∀ (X1 X2 X3 : G), ((X1◇(X1◇(X2◇((X2◇X3)◇X3))))◇(X2◇X2)) = X1 := by
  intro X1 X2 X3
  calc ((X1◇(X1◇(X2◇((X2◇X3)◇X3))))◇(X2◇X2))
   _ = ((X1◇(X1◇(X2◇(X2◇((X2◇(X2◇(X1◇X1)))◇X2)))))◇(X2◇X2)) := congrArg (·◇(X2◇X2)) (congrArg (X1◇·) (congrArg (X1◇·) (((c_0_9 X2 X3 X1).symm).symm)))
   _ = X1 := c_0_8 X1 X2 X2 X1
 have c_0_13 : ∀ (X1 X2 X3 : G), ((X1◇(X1◇X2))◇((X2◇(X2◇X2))◇(((X2◇X2)◇X3)◇X3))) = X1 := by
  intro X1 X2 X3
  calc ((X1◇(X1◇X2))◇((X2◇(X2◇X2))◇(((X2◇X2)◇X3)◇X3)))
   _ = ((X1◇(X1◇X2))◇((X2◇(((X2◇X2)◇X3)◇X3))◇(((X2◇X2)◇X3)◇X3))) := congrArg ((X1◇(X1◇X2))◇·) (congrArg (·◇(((X2◇X2)◇X3)◇X3)) ((c_0_10 X2 X3).symm))
   _ = X1 := (c_0_3 X1 X2 ((((X2◇X2)◇X3)◇X3))).symm
 have c_0_14 : ∀ (X1 X2 X3 X4 : G), ((X1◇(X1◇((X2◇(X2◇(X3◇((X3◇X4)◇X4))))◇X2)))◇X2) = X1 := by
  intro X1 X2 X3 X4
  clear h c_0_3 c_0_4 c_0_5 c_0_6x c_0_6 c_0_7 c_0_8 c_0_9 c_0_10 c_0_13
  grind
 have c_0_15 : ∀ (X1 X2 X3 : G), ((X1◇(X1◇(X1◇X1)))◇(((((X1◇X1)◇X2)◇X2)◇X3)◇X3)) = X1 := by
  intro X1 X2 X3
  calc ((X1◇(X1◇(X1◇X1)))◇(((((X1◇X1)◇X2)◇X2)◇X3)◇X3))
   _ = ((X1◇(X1◇(((X1◇X1)◇X2)◇X2)))◇(((((X1◇X1)◇X2)◇X2)◇X3)◇X3)) := congrArg (·◇(((((X1◇X1)◇X2)◇X2)◇X3)◇X3)) (congrArg (X1◇·) ((c_0_10 X1 X2).symm))
   _ = X1 := (c_0_3 X1 ((((X1◇X1)◇X2)◇X2)) X3).symm
 have c_0_16 : ∀ (X1 X2 X3 : G), (X1◇(((((X1◇X1)◇X2)◇X2)◇X3)◇X3)) = (X1◇(X1◇X1)) := by
  intro X1 X2 X3
  calc (X1◇(((((X1◇X1)◇X2)◇X2)◇X3)◇X3))
   _ = (((X1◇(X1◇X1))◇((X1◇(X1◇X1))◇(((X1◇X1)◇X2)◇X2)))◇(((((X1◇X1)◇X2)◇X2)◇X3)◇X3)) := congrArg (·◇(((((X1◇X1)◇X2)◇X2)◇X3)◇X3)) ((c_0_13 X1 X1 X2).symm)
   _ = (X1◇(X1◇X1)) := (c_0_3 ((X1◇(X1◇X1))) ((((X1◇X1)◇X2)◇X2)) X3).symm
 have c_0_17x : ∀ (X0 X1 X2 X3 X4 : G), ((X0◇(X0◇((X1◇(X1◇((X2◇(X2◇(X2◇X2)))◇(X2◇(((((X2◇X2)◇X3)◇X3)◇X4)◇X4)))))◇X1)))◇X1) = X0 := by
  intro X0 X1 X2 X3 X4
  calc ((X0◇(X0◇((X1◇(X1◇((X2◇(X2◇(X2◇X2)))◇(X2◇(((((X2◇X2)◇X3)◇X3)◇X4)◇X4)))))◇X1)))◇X1)
   _ = ((X0◇(X0◇((X1◇(X1◇((X2◇(X2◇(X2◇X2)))◇(((X2◇(X2◇(X2◇X2)))◇(((((X2◇X2)◇X3)◇X3)◇X4)◇X4))◇(((((X2◇X2)◇X3)◇X3)◇X4)◇X4)))))◇X1)))◇X1) := congrArg (·◇X1) (congrArg (X0◇·) (congrArg (X0◇·) (congrArg (·◇X1) (congrArg (X1◇·) (congrArg (X1◇·) (congrArg ((X2◇(X2◇(X2◇X2)))◇·) (congrArg (·◇(((((X2◇X2)◇X3)◇X3)◇X4)◇X4)) ((c_0_15 X2 X3 X4).symm))))))))
   _ = X0 := c_0_14 X0 X1 ((X2◇(X2◇(X2◇X2)))) ((((((X2◇X2)◇X3)◇X3)◇X4)◇X4))
 have c_0_17 : ∀ (X1 X2 X3 : G), ((X1◇(X1◇((X2◇(X2◇((X3◇(X3◇(X3◇X3)))◇(X3◇(X3◇X3)))))◇X2)))◇X2) = X1 := by
  intro X1 X2 X3
  have strict_rw_2 := (c_0_17x X1 X2 X3 X1 X1)
  rw [c_0_16] at strict_rw_2
  exact strict_rw_2
 have c_0_18 : ∀ (X1 X2 X3 X4 : G), ((X1◇((X1◇X2)◇X2))◇((((X1◇(X1◇(X3◇X3)))◇X1)◇X4)◇X4)) = X1 := by
  intro X1 X2 X3 X4
  calc ((X1◇((X1◇X2)◇X2))◇((((X1◇(X1◇(X3◇X3)))◇X1)◇X4)◇X4))
   _ = ((X1◇(X1◇((X1◇(X1◇(X3◇X3)))◇X1)))◇((((X1◇(X1◇(X3◇X3)))◇X1)◇X4)◇X4)) := congrArg (·◇((((X1◇(X1◇(X3◇X3)))◇X1)◇X4)◇X4)) (((c_0_9 X1 X2 X3).symm).symm)
   _ = X1 := (c_0_3 X1 (((X1◇(X1◇(X3◇X3)))◇X1)) X4).symm
 have c_0_19 : ∀ (X1 X2 : G), ((X1◇((X1◇X2)◇X2))◇X1) = X1 := by
  intro X1 X2
  calc ((X1◇((X1◇X2)◇X2))◇X1)
   _ = ((X1◇(X1◇((X1◇(X1◇(X1◇X1)))◇X1)))◇X1) := congrArg (·◇X1) (((c_0_9 X1 X2 X1).symm).symm)
   _ = X1 := c_0_6 X1 X1 X1
 have c_0_20x : ∀ (X0 X1 X2 X3 : G), ((X0◇(X0◇(((X1◇((X1◇X2)◇X2))◇X1)◇(X1◇((X1◇X2)◇X2)))))◇(X1◇((X1◇X2)◇X2))) = X0 := by
  intro X0 X1 X2 X3
  calc ((X0◇(X0◇(((X1◇((X1◇X2)◇X2))◇X1)◇(X1◇((X1◇X2)◇X2)))))◇(X1◇((X1◇X2)◇X2)))
   _ = ((X0◇(X0◇(((X1◇((X1◇X2)◇X2))◇((X1◇((X1◇X2)◇X2))◇((((X1◇(X1◇(X3◇X3)))◇X1)◇(((X1◇(X1◇(X3◇X3)))◇X1)◇(((X1◇(X1◇(X3◇X3)))◇X1)◇((X1◇(X1◇(X3◇X3)))◇X1))))◇(((X1◇(X1◇(X3◇X3)))◇X1)◇(((X1◇(X1◇(X3◇X3)))◇X1)◇((X1◇(X1◇(X3◇X3)))◇X1))))))◇(X1◇((X1◇X2)◇X2)))))◇(X1◇((X1◇X2)◇X2))) := congrArg (·◇(X1◇((X1◇X2)◇X2))) (congrArg (X0◇·) (congrArg (X0◇·) (congrArg (·◇(X1◇((X1◇X2)◇X2))) (congrArg ((X1◇((X1◇X2)◇X2))◇·) ((c_0_18 X1 X2 X3 ((((X1◇(X1◇(X3◇X3)))◇X1)◇(((X1◇(X1◇(X3◇X3)))◇X1)◇((X1◇(X1◇(X3◇X3)))◇X1))))).symm)))))
   _ = X0 := c_0_17 X0 ((X1◇((X1◇X2)◇X2))) (((X1◇(X1◇(X3◇X3)))◇X1))
 have c_0_20 : ∀ (X1 X2 X3 : G), ((X1◇(X1◇(X2◇(X2◇((X2◇X3)◇X3)))))◇(X2◇((X2◇X3)◇X3))) = X1 := by
  intro X1 X2 X3
  have strict_rw_3 := (c_0_20x X1 X2 X3 X1)
  rw [c_0_19] at strict_rw_3
  exact strict_rw_3
 have c_0_21 : ∀ (X1 X2 X3 : G), (((X1◇(X1◇X2))◇(X1◇((X2◇X3)◇X3)))◇(X1◇(X1◇X2))) = (X1◇(X1◇X2)) := by
  intro X1 X2 X3
  calc (((X1◇(X1◇X2))◇(X1◇((X2◇X3)◇X3)))◇(X1◇(X1◇X2)))
   _ = (((X1◇(X1◇X2))◇(((X1◇(X1◇X2))◇((X2◇X3)◇X3))◇((X2◇X3)◇X3)))◇(X1◇(X1◇X2))) := congrArg (·◇(X1◇(X1◇X2))) (congrArg ((X1◇(X1◇X2))◇·) (congrArg (·◇((X2◇X3)◇X3)) (((c_0_3 X1 X2 X3).symm).symm)))
   _ = (X1◇(X1◇X2)) := c_0_19 ((X1◇(X1◇X2))) (((X2◇X3)◇X3))
 have c_0_22 : ∀ (X1 X2 X3 : G), ((X1◇(X1◇((X1◇X2)◇X2)))◇(X1◇((((X1◇X2)◇X2)◇X3)◇X3))) = ((X1◇(X1◇((X1◇X2)◇X2)))◇(X1◇((X1◇X2)◇X2))) := by
  intro X1 X2 X3
  calc ((X1◇(X1◇((X1◇X2)◇X2)))◇(X1◇((((X1◇X2)◇X2)◇X3)◇X3)))
   _ = ((((X1◇(X1◇((X1◇X2)◇X2)))◇(X1◇((((X1◇X2)◇X2)◇X3)◇X3)))◇(((X1◇(X1◇((X1◇X2)◇X2)))◇(X1◇((((X1◇X2)◇X2)◇X3)◇X3)))◇(X1◇(X1◇((X1◇X2)◇X2)))))◇(X1◇((X1◇X2)◇X2))) := (c_0_20 (((X1◇(X1◇((X1◇X2)◇X2)))◇(X1◇((((X1◇X2)◇X2)◇X3)◇X3)))) X1 X2).symm
   _ = ((((X1◇(X1◇((X1◇X2)◇X2)))◇(X1◇((((X1◇X2)◇X2)◇X3)◇X3)))◇(X1◇(X1◇((X1◇X2)◇X2))))◇(X1◇((X1◇X2)◇X2))) := congrArg (·◇(X1◇((X1◇X2)◇X2))) (congrArg (((X1◇(X1◇((X1◇X2)◇X2)))◇(X1◇((((X1◇X2)◇X2)◇X3)◇X3)))◇·) (c_0_21 X1 (((X1◇X2)◇X2)) X3))
   _ = ((X1◇(X1◇((X1◇X2)◇X2)))◇(X1◇((X1◇X2)◇X2))) := congrArg (·◇(X1◇((X1◇X2)◇X2))) (((c_0_21 X1 (((X1◇X2)◇X2)) X3).symm).symm)
 have c_0_23 : ∀ (X1 X2 X3 : G), (X1◇((X1◇(X1◇X1))◇(((X1◇X1)◇X2)◇X2))) = (X1◇((X1◇X3)◇X3)) := by
  intro X1 X2 X3
  calc (X1◇((X1◇(X1◇X1))◇(((X1◇X1)◇X2)◇X2)))
   _ = (((X1◇((X1◇X3)◇X3))◇X1)◇((X1◇(X1◇X1))◇(((X1◇X1)◇X2)◇X2))) := congrArg (·◇((X1◇(X1◇X1))◇(((X1◇X1)◇X2)◇X2))) ((c_0_19 X1 X3).symm)
   _ = (((X1◇((X1◇X3)◇X3))◇((X1◇((X1◇X3)◇X3))◇X1))◇((X1◇(X1◇X1))◇(((X1◇X1)◇X2)◇X2))) := congrArg (·◇((X1◇(X1◇X1))◇(((X1◇X1)◇X2)◇X2))) (congrArg ((X1◇((X1◇X3)◇X3))◇·) ((c_0_19 X1 X3).symm))
   _ = (X1◇((X1◇X3)◇X3)) := ((c_0_13 ((X1◇((X1◇X3)◇X3))) X1 X2).symm).symm
 have c_0_24 : ∀ (X1 X2 X3 X4 : G), (((X1◇(X1◇X2))◇X1)◇((((X2◇X3)◇X3)◇X4)◇X4)) = (X1◇(X1◇X2)) := by
  intro X1 X2 X3 X4
  calc (((X1◇(X1◇X2))◇X1)◇((((X2◇X3)◇X3)◇X4)◇X4))
   _ = (((X1◇(X1◇X2))◇((X1◇(X1◇X2))◇((X2◇X3)◇X3)))◇((((X2◇X3)◇X3)◇X4)◇X4)) := congrArg (·◇((((X2◇X3)◇X3)◇X4)◇X4)) (congrArg ((X1◇(X1◇X2))◇·) (((c_0_3 X1 X2 X3).symm).symm))
   _ = (X1◇(X1◇X2)) := (c_0_3 ((X1◇(X1◇X2))) (((X2◇X3)◇X3)) X4).symm
 have c_0_25 : ∀ (X1 esk1_0 X2 X3 : G), ((X1◇(X1◇((X1◇esk1_0)◇esk1_0)))◇(X1◇((((X1◇X2)◇X2)◇X3)◇X3))) = ((X1◇(X1◇((X1◇esk1_0)◇esk1_0)))◇(X1◇((X1◇esk1_0)◇esk1_0))) := by
  intro X1 esk1_0 X2 X3
  calc ((X1◇(X1◇((X1◇esk1_0)◇esk1_0)))◇(X1◇((((X1◇X2)◇X2)◇X3)◇X3)))
   _ = ((X1◇(X1◇((X1◇(X1◇X1))◇(((X1◇X1)◇X1)◇X1))))◇(X1◇((((X1◇X2)◇X2)◇X3)◇X3))) := congrArg (·◇(X1◇((((X1◇X2)◇X2)◇X3)◇X3))) (congrArg (X1◇·) ((c_0_23 X1 X1 esk1_0).symm))
   _ = ((X1◇(X1◇((X1◇X2)◇X2)))◇(X1◇((((X1◇X2)◇X2)◇X3)◇X3))) := congrArg (·◇(X1◇((((X1◇X2)◇X2)◇X3)◇X3))) (congrArg (X1◇·) (c_0_23 X1 X1 X2))
   _ = ((X1◇(X1◇((X1◇X2)◇X2)))◇(X1◇((X1◇X2)◇X2))) := c_0_22 X1 X2 X3
   _ = ((X1◇(X1◇((X1◇(X1◇X1))◇(((X1◇X1)◇X1)◇X1))))◇(X1◇((X1◇X2)◇X2))) := congrArg (·◇(X1◇((X1◇X2)◇X2))) (congrArg (X1◇·) ((c_0_23 X1 X1 X2).symm))
   _ = ((X1◇(X1◇((X1◇(X1◇X1))◇(((X1◇X1)◇X1)◇X1))))◇(X1◇((X1◇(X1◇X1))◇(((X1◇X1)◇X1)◇X1)))) := congrArg ((X1◇(X1◇((X1◇(X1◇X1))◇(((X1◇X1)◇X1)◇X1))))◇·) ((c_0_23 X1 X1 X2).symm)
   _ = ((X1◇(X1◇((X1◇(X1◇X1))◇(((X1◇X1)◇X1)◇X1))))◇(X1◇((X1◇esk1_0)◇esk1_0))) := congrArg ((X1◇(X1◇((X1◇(X1◇X1))◇(((X1◇X1)◇X1)◇X1))))◇·) (((c_0_23 X1 X1 esk1_0).symm).symm)
   _ = ((X1◇(X1◇((X1◇esk1_0)◇esk1_0)))◇(X1◇((X1◇esk1_0)◇esk1_0))) := congrArg (·◇(X1◇((X1◇esk1_0)◇esk1_0))) (congrArg (X1◇·) (((c_0_23 X1 X1 esk1_0).symm).symm))
 have c_0_26 : ∀ (X1 X2 X3 X4 : G), ((X1◇(X1◇((X1◇X2)◇X2)))◇((((X1◇X3)◇X3)◇X4)◇X4)) = X1 := by
  intro X1 X2 X3 X4
  clear h c_0_3 c_0_4 c_0_5 c_0_6x c_0_6 c_0_7 c_0_8 c_0_9 c_0_10 c_0_11 c_0_12 c_0_13 c_0_14 c_0_15 c_0_16 c_0_17x c_0_17 c_0_18 c_0_20x c_0_20 c_0_21 c_0_22 c_0_23
  clear c_0_25
  grind
 have c_0_27 : ∀ (X1 esk1_0 : G), (((X1◇(X1◇((X1◇esk1_0)◇esk1_0)))◇(X1◇((X1◇esk1_0)◇esk1_0)))◇(X1◇(X1◇((X1◇esk1_0)◇esk1_0)))) = (X1◇(X1◇((X1◇esk1_0)◇esk1_0))) := by
  intro X1 esk1_0
  calc (((X1◇(X1◇((X1◇esk1_0)◇esk1_0)))◇(X1◇((X1◇esk1_0)◇esk1_0)))◇(X1◇(X1◇((X1◇esk1_0)◇esk1_0))))
   _ = (((X1◇(X1◇((X1◇esk1_0)◇esk1_0)))◇(X1◇((((X1◇esk1_0)◇esk1_0)◇X1)◇X1)))◇(X1◇(X1◇((X1◇esk1_0)◇esk1_0)))) := congrArg (·◇(X1◇(X1◇((X1◇esk1_0)◇esk1_0)))) ((c_0_25 X1 esk1_0 esk1_0 X1).symm)
   _ = (X1◇(X1◇((X1◇esk1_0)◇esk1_0))) := c_0_21 X1 (((X1◇esk1_0)◇esk1_0)) X1
 have c_0_28 : ∀ (X1 X2 esk1_0 : G), ((X1◇(X1◇((X1◇X2)◇X2)))◇((X1◇(X1◇((X1◇esk1_0)◇esk1_0)))◇(X1◇(X1◇((X1◇esk1_0)◇esk1_0))))) = X1 := by
  intro X1 X2 esk1_0
  calc ((X1◇(X1◇((X1◇X2)◇X2)))◇((X1◇(X1◇((X1◇esk1_0)◇esk1_0)))◇(X1◇(X1◇((X1◇esk1_0)◇esk1_0)))))
   _ = ((X1◇(X1◇((X1◇X2)◇X2)))◇((((X1◇(X1◇((X1◇esk1_0)◇esk1_0)))◇(X1◇((X1◇esk1_0)◇esk1_0)))◇(X1◇(X1◇((X1◇esk1_0)◇esk1_0))))◇(X1◇(X1◇((X1◇esk1_0)◇esk1_0))))) := congrArg ((X1◇(X1◇((X1◇X2)◇X2)))◇·) (congrArg (·◇(X1◇(X1◇((X1◇esk1_0)◇esk1_0)))) ((c_0_27 X1 esk1_0).symm))
   _ = X1 := c_0_26 X1 X2 ((X1◇((X1◇esk1_0)◇esk1_0))) ((X1◇(X1◇((X1◇esk1_0)◇esk1_0))))
 have c_0_29 : ∀ (X1 X2 X3 X4 : G), ((X1◇(X1◇(X2◇(X2◇X3))))◇(X2◇((X3◇X4)◇X4))) = X1 := by
  intro X1 X2 X3 X4
  calc ((X1◇(X1◇(X2◇(X2◇X3))))◇(X2◇((X3◇X4)◇X4)))
   _ = ((X1◇(X1◇(X2◇(X2◇X3))))◇(((X2◇(X2◇X3))◇((X3◇X4)◇X4))◇((X3◇X4)◇X4))) := congrArg ((X1◇(X1◇(X2◇(X2◇X3))))◇·) (congrArg (·◇((X3◇X4)◇X4)) (((c_0_3 X2 X3 X4).symm).symm))
   _ = X1 := (c_0_3 X1 ((X2◇(X2◇X3))) (((X3◇X4)◇X4))).symm
 have c_0_30 : ∀ (X1 esk1_0 X2 : G), (X1◇(((X1◇(X1◇((X1◇esk1_0)◇esk1_0)))◇X2)◇X2)) = (X1◇(X1◇((X1◇esk1_0)◇esk1_0))) := by
  intro X1 esk1_0 X2
  calc (X1◇(((X1◇(X1◇((X1◇esk1_0)◇esk1_0)))◇X2)◇X2))
   _ = (((X1◇(X1◇((X1◇esk1_0)◇esk1_0)))◇((X1◇(X1◇((X1◇esk1_0)◇esk1_0)))◇(X1◇(X1◇((X1◇esk1_0)◇esk1_0)))))◇(((X1◇(X1◇((X1◇esk1_0)◇esk1_0)))◇X2)◇X2)) := congrArg (·◇(((X1◇(X1◇((X1◇esk1_0)◇esk1_0)))◇X2)◇X2)) ((c_0_28 X1 esk1_0 esk1_0).symm)
   _ = (X1◇(X1◇((X1◇esk1_0)◇esk1_0))) := (c_0_3 ((X1◇(X1◇((X1◇esk1_0)◇esk1_0)))) ((X1◇(X1◇((X1◇esk1_0)◇esk1_0)))) X2).symm
 have c_0_31 : ∀ (X1 X2 X3 : G), (X1◇((X1◇X2)◇X2)) = (X1◇((X1◇X3)◇X3)) := by
  intro X1 X2 X3
  calc (X1◇((X1◇X2)◇X2))
   _ = (X1◇(X1◇((X1◇(X1◇(X1◇X1)))◇X1))) := ((c_0_9 X1 X2 X1).symm).symm
   _ = (X1◇((X1◇X3)◇X3)) := (c_0_9 X1 X3 X1).symm
 have c_0_32 : ∀ (X1 X2 : G), (((X1◇(X1◇(X2◇(X2◇X2))))◇X1)◇(X2◇X2)) = (X1◇(X1◇(X2◇(X2◇X2)))) := by
  intro X1 X2
  calc (((X1◇(X1◇(X2◇(X2◇X2))))◇X1)◇(X2◇X2))
   _ = (((X1◇(X1◇(X2◇(X2◇X2))))◇((X1◇(X1◇(X2◇(X2◇X2))))◇(X2◇((X2◇X1)◇X1))))◇(X2◇X2)) := congrArg (·◇(X2◇X2)) (congrArg ((X1◇(X1◇(X2◇(X2◇X2))))◇·) ((c_0_29 X1 X2 X2 X1).symm))
   _ = (X1◇(X1◇(X2◇(X2◇X2)))) := c_0_12 ((X1◇(X1◇(X2◇(X2◇X2))))) X2 X1
 have c_0_33 : ∀ (X1 X2 X3 : G), (X1◇(((X1◇(X1◇((X1◇X2)◇X2)))◇X3)◇X3)) = (X1◇(X1◇((X1◇X2)◇X2))) := by
  intro X1 X2 X3
  calc (X1◇(((X1◇(X1◇((X1◇X2)◇X2)))◇X3)◇X3))
   _ = (X1◇(((X1◇(X1◇((X1◇X2)◇X2)))◇X3)◇X3)) := congrArg (X1◇·) (congrArg (·◇X3) (congrArg (·◇X3) (congrArg (X1◇·) ((c_0_31 X1 X2 X2).symm))))
   _ = (X1◇(X1◇((X1◇X2)◇X2))) := c_0_30 X1 X2 X3
 have c_0_34 : ∀ (X1 X2 : G), (((X1◇(X1◇X1))◇((X1◇(X1◇X1))◇(((X1◇(X1◇X1))◇X2)◇X2)))◇(X1◇X1)) = (X1◇(X1◇X1)) := by
  intro X1 X2
  clear h c_0_3 c_0_4 c_0_5 c_0_6x c_0_6 c_0_7 c_0_8 c_0_9 c_0_10 c_0_11 c_0_12 c_0_13 c_0_14 c_0_15 c_0_16 c_0_17x c_0_17 c_0_18 c_0_20x c_0_20 c_0_21 c_0_22 c_0_23
  clear c_0_24 c_0_25 c_0_26 c_0_27 c_0_28 c_0_29 c_0_30 c_0_31 c_0_33
  grind
 have c_0_35 : ∀ (X1 X2 : G), ((X1◇(X1◇X1))◇((X1◇(X1◇X1))◇(((X1◇(X1◇X1))◇X2)◇X2))) = X1 := by
  intro X1 X2
  clear h c_0_4 c_0_5 c_0_6x c_0_6 c_0_7 c_0_8 c_0_9 c_0_10 c_0_11 c_0_12 c_0_13 c_0_14 c_0_15 c_0_16 c_0_17x c_0_17 c_0_18 c_0_19 c_0_20x c_0_20 c_0_21 c_0_22 c_0_23
  clear c_0_24 c_0_25 c_0_26 c_0_27 c_0_28 c_0_29 c_0_30 c_0_31 c_0_32
  grind
 have c_0_36 : ∀ (X1 X2 X3 : G), (X1◇(((((X1◇(X1◇X1))◇X2)◇X2)◇X3)◇X3)) = (X1◇(X1◇X1)) := by
  intro X1 X2 X3
  calc (X1◇(((((X1◇(X1◇X1))◇X2)◇X2)◇X3)◇X3))
   _ = (((X1◇(X1◇X1))◇((X1◇(X1◇X1))◇(((X1◇(X1◇X1))◇X2)◇X2)))◇(((((X1◇(X1◇X1))◇X2)◇X2)◇X3)◇X3)) := congrArg (·◇(((((X1◇(X1◇X1))◇X2)◇X2)◇X3)◇X3)) ((c_0_35 X1 X2).symm)
   _ = (X1◇(X1◇X1)) := (c_0_3 ((X1◇(X1◇X1))) ((((X1◇(X1◇X1))◇X2)◇X2)) X3).symm
 have c_0_37x : ∀ (X0 X1 X2 X3 : G), (X0◇(((((X0◇(X0◇X0))◇((X0◇(X0◇X0))◇(((X0◇(X0◇X0))◇X1)◇X1)))◇((((X0◇(X0◇X0))◇((X0◇(X0◇X0))◇(((X0◇(X0◇X0))◇X1)◇X1)))◇X2)◇X2))◇X3)◇X3)) = (X0◇(X0◇X0)) := by
  intro X0 X1 X2 X3
  calc (X0◇(((((X0◇(X0◇X0))◇((X0◇(X0◇X0))◇(((X0◇(X0◇X0))◇X1)◇X1)))◇((((X0◇(X0◇X0))◇((X0◇(X0◇X0))◇(((X0◇(X0◇X0))◇X1)◇X1)))◇X2)◇X2))◇X3)◇X3))
   _ = (X0◇(((((X0◇(X0◇X0))◇((((X0◇(X0◇X0))◇((X0◇(X0◇X0))◇(((X0◇(X0◇X0))◇X1)◇X1)))◇X2)◇X2))◇((((X0◇(X0◇X0))◇((X0◇(X0◇X0))◇(((X0◇(X0◇X0))◇X1)◇X1)))◇X2)◇X2))◇X3)◇X3)) := congrArg (X0◇·) (congrArg (·◇X3) (congrArg (·◇X3) (congrArg (·◇((((X0◇(X0◇X0))◇((X0◇(X0◇X0))◇(((X0◇(X0◇X0))◇X1)◇X1)))◇X2)◇X2)) ((c_0_33 ((X0◇(X0◇X0))) X1 X2).symm))))
   _ = (X0◇(X0◇X0)) := c_0_36 X0 (((((X0◇(X0◇X0))◇((X0◇(X0◇X0))◇(((X0◇(X0◇X0))◇X1)◇X1)))◇X2)◇X2)) X3
 have c_0_37 : ∀ (X1 X2 X3 : G), (X1◇(((X1◇((X1◇X2)◇X2))◇X3)◇X3)) = (X1◇(X1◇X1)) := by
  intro X1 X2 X3
  have strict_rw_4 := (c_0_37x X1 X1 X2 X3)
  rw [c_0_35] at strict_rw_4
  exact strict_rw_4
 have c_0_38 : ∀ (X1 X2 X3 X4 X5 : G), ((X1◇(X1◇(X2◇(X2◇((X2◇X3)◇X3)))))◇(X2◇((((X2◇X4)◇X4)◇X5)◇X5))) = X1 := by
  intro X1 X2 X3 X4 X5
  calc ((X1◇(X1◇(X2◇(X2◇((X2◇X3)◇X3)))))◇(X2◇((((X2◇X4)◇X4)◇X5)◇X5)))
   _ = ((X1◇(X1◇(X2◇(X2◇((X2◇X4)◇X4)))))◇(X2◇((((X2◇X4)◇X4)◇X5)◇X5))) := congrArg (·◇(X2◇((((X2◇X4)◇X4)◇X5)◇X5))) (congrArg (X1◇·) (congrArg (X1◇·) (congrArg (X2◇·) ((c_0_31 X2 X4 X3).symm))))
   _ = X1 := c_0_29 X1 X2 (((X2◇X4)◇X4)) X5
 have c_0_39 : ∀ (X1 X2 X3 esk1_0 : G), (X1◇((X1◇((X1◇X2)◇X2))◇((X1◇X3)◇X3))) = (X1◇((X1◇esk1_0)◇esk1_0)) := by
  intro X1 X2 X3 esk1_0
  calc (X1◇((X1◇((X1◇X2)◇X2))◇((X1◇X3)◇X3)))
   _ = (X1◇((X1◇((X1◇X3)◇X3))◇((X1◇X3)◇X3))) := congrArg (X1◇·) (congrArg (·◇((X1◇X3)◇X3)) ((c_0_31 X1 X3 X2).symm))
   _ = (X1◇((X1◇esk1_0)◇esk1_0)) := c_0_31 X1 (((X1◇X3)◇X3)) esk1_0
 have c_0_40 : ∀ (X1 X2 X3 X4 : G), ((X1◇(X1◇((X2◇(X2◇((X3◇(X3◇(X4◇X4)))◇(X3◇(X4◇X4)))))◇X2)))◇X2) = X1 := by
  intro X1 X2 X3 X4
  calc ((X1◇(X1◇((X2◇(X2◇((X3◇(X3◇(X4◇X4)))◇(X3◇(X4◇X4)))))◇X2)))◇X2)
   _ = ((X1◇(X1◇((X2◇(X2◇((X3◇(X3◇(X4◇X4)))◇(((X3◇(X3◇(X4◇X4)))◇(X4◇X4))◇(X4◇X4)))))◇X2)))◇X2) := congrArg (·◇X2) (congrArg (X1◇·) (congrArg (X1◇·) (congrArg (·◇X2) (congrArg (X2◇·) (congrArg (X2◇·) (congrArg ((X3◇(X3◇(X4◇X4)))◇·) (congrArg (·◇(X4◇X4)) ((c_0_4 X3 X4).symm))))))))
   _ = X1 := c_0_14 X1 X2 ((X3◇(X3◇(X4◇X4)))) ((X4◇X4))
 have c_0_41 : ∀ (X1 X2 X3 : G), (X1◇(X1◇((((X1◇(X1◇(X2◇X2)))◇X1)◇X3)◇X3))) = (X1◇(X1◇X1)) := by
  intro X1 X2 X3
  calc (X1◇(X1◇((((X1◇(X1◇(X2◇X2)))◇X1)◇X3)◇X3)))
   _ = (X1◇(((X1◇((X1◇X1)◇X1))◇((((X1◇(X1◇(X2◇X2)))◇X1)◇X3)◇X3))◇((((X1◇(X1◇(X2◇X2)))◇X1)◇X3)◇X3))) := congrArg (X1◇·) (congrArg (·◇((((X1◇(X1◇(X2◇X2)))◇X1)◇X3)◇X3)) ((c_0_18 X1 X1 X2 X3).symm))
   _ = (X1◇(X1◇X1)) := c_0_37 X1 X1 (((((X1◇(X1◇(X2◇X2)))◇X1)◇X3)◇X3))
 have c_0_42 : ∀ (X1 X2 X3 esk1_0 : G), (X1◇(X1◇((((X1◇X2)◇X2)◇X3)◇X3))) = (X1◇(X1◇((X1◇esk1_0)◇esk1_0))) := by
  intro X1 X2 X3 esk1_0
  calc (X1◇(X1◇((((X1◇X2)◇X2)◇X3)◇X3)))
   _ = (((X1◇(X1◇((X1◇esk1_0)◇esk1_0)))◇((X1◇(X1◇((X1◇esk1_0)◇esk1_0)))◇(X1◇(X1◇((X1◇esk1_0)◇esk1_0)))))◇(X1◇((((X1◇X2)◇X2)◇X3)◇X3))) := congrArg (·◇(X1◇((((X1◇X2)◇X2)◇X3)◇X3))) ((c_0_28 X1 esk1_0 esk1_0).symm)
   _ = (X1◇(X1◇((X1◇esk1_0)◇esk1_0))) := c_0_38 ((X1◇(X1◇((X1◇esk1_0)◇esk1_0)))) X1 esk1_0 X2 X3
 have c_0_43 : ∀ (X1 esk1_0 X2 X3 : G), ((X1◇((X1◇((X1◇esk1_0)◇esk1_0))◇((X1◇((X1◇X2)◇X2))◇((X1◇X3)◇X3))))◇X1) = X1 := by
  intro X1 esk1_0 X2 X3
  calc ((X1◇((X1◇((X1◇esk1_0)◇esk1_0))◇((X1◇((X1◇X2)◇X2))◇((X1◇X3)◇X3))))◇X1)
   _ = ((X1◇((X1◇((X1◇((X1◇X2)◇X2))◇((X1◇X3)◇X3)))◇((X1◇((X1◇X2)◇X2))◇((X1◇X3)◇X3))))◇X1) := congrArg (·◇X1) (congrArg (X1◇·) (congrArg (·◇((X1◇((X1◇X2)◇X2))◇((X1◇X3)◇X3))) ((c_0_39 X1 X2 X3 esk1_0).symm)))
   _ = X1 := c_0_19 X1 (((X1◇((X1◇X2)◇X2))◇((X1◇X3)◇X3)))
 have c_0_44 : ∀ (X1 X2 : G), ((X1◇(X1◇((X2◇(X2◇X2))◇X2)))◇X2) = X1 := by
  intro X1 X2
  calc ((X1◇(X1◇((X2◇(X2◇X2))◇X2)))◇X2)
   _ = ((X1◇(X1◇((X2◇(X2◇((((X2◇(X2◇(X1◇X1)))◇X2)◇(((X2◇(X2◇(X1◇X1)))◇X2)◇(X1◇X1)))◇(((X2◇(X2◇(X1◇X1)))◇X2)◇(X1◇X1)))))◇X2)))◇X2) := congrArg (·◇X2) (congrArg (X1◇·) (congrArg (X1◇·) (congrArg (·◇X2) ((c_0_41 X2 X1 ((((X2◇(X2◇(X1◇X1)))◇X2)◇(X1◇X1)))).symm))))
   _ = X1 := c_0_40 X1 X2 (((X2◇(X2◇(X1◇X1)))◇X2)) X1
 have c_0_45 : ∀ (X1 esk1_0 X2 X3 X4 : G), ((X1◇(X1◇((X1◇esk1_0)◇esk1_0)))◇((((((X1◇X2)◇X2)◇X3)◇X3)◇X4)◇X4)) = X1 := by
  intro X1 esk1_0 X2 X3 X4
  calc ((X1◇(X1◇((X1◇esk1_0)◇esk1_0)))◇((((((X1◇X2)◇X2)◇X3)◇X3)◇X4)◇X4))
   _ = ((X1◇(X1◇((((X1◇X2)◇X2)◇X3)◇X3)))◇((((((X1◇X2)◇X2)◇X3)◇X3)◇X4)◇X4)) := congrArg (·◇((((((X1◇X2)◇X2)◇X3)◇X3)◇X4)◇X4)) ((c_0_42 X1 X2 X3 esk1_0).symm)
   _ = X1 := (c_0_3 X1 (((((X1◇X2)◇X2)◇X3)◇X3)) X4).symm
 have c_0_46 : ∀ (X1 X2 X3 X4 : G), ((X1◇((X1◇((X1◇X2)◇X2))◇((X1◇((X1◇X3)◇X3))◇((X1◇X4)◇X4))))◇X1) = X1 := by
  intro X1 X2 X3 X4
  calc ((X1◇((X1◇((X1◇X2)◇X2))◇((X1◇((X1◇X3)◇X3))◇((X1◇X4)◇X4))))◇X1)
   _ = ((X1◇((X1◇((X1◇X1)◇X1))◇((X1◇((X1◇X3)◇X3))◇((X1◇X4)◇X4))))◇X1) := congrArg (·◇X1) (congrArg (X1◇·) (congrArg (·◇((X1◇((X1◇X3)◇X3))◇((X1◇X4)◇X4))) ((c_0_31 X1 X1 X2).symm)))
   _ = X1 := c_0_43 X1 X1 X3 X4
 have c_0_47 : ∀ (X1 X2 : G), (((X1◇(X1◇X1))◇X1)◇((((X1◇(X1◇X1))◇X1)◇X2)◇X2)) = (((X1◇(X1◇X1))◇X1)◇X1) := by
  intro X1 X2
  calc (((X1◇(X1◇X1))◇X1)◇((((X1◇(X1◇X1))◇X1)◇X2)◇X2))
   _ = (((((X1◇(X1◇X1))◇X1)◇((((X1◇(X1◇X1))◇X1)◇X2)◇X2))◇((((X1◇(X1◇X1))◇X1)◇((((X1◇(X1◇X1))◇X1)◇X2)◇X2))◇((X1◇(X1◇X1))◇X1)))◇X1) := (c_0_44 ((((X1◇(X1◇X1))◇X1)◇((((X1◇(X1◇X1))◇X1)◇X2)◇X2))) X1).symm
   _ = (((((X1◇(X1◇X1))◇X1)◇((((X1◇(X1◇X1))◇X1)◇X2)◇X2))◇((X1◇(X1◇X1))◇X1))◇X1) := congrArg (·◇X1) (congrArg ((((X1◇(X1◇X1))◇X1)◇((((X1◇(X1◇X1))◇X1)◇X2)◇X2))◇·) (c_0_19 (((X1◇(X1◇X1))◇X1)) X2))
   _ = (((X1◇(X1◇X1))◇X1)◇X1) := congrArg (·◇X1) (((c_0_19 (((X1◇(X1◇X1))◇X1)) X2).symm).symm)
 have c_0_48 : ∀ (X1 : G), ((X1◇X1)◇((X1◇X1)◇(X1◇X1))) = ((X1◇X1)◇(X1◇X1)) := by
  intro X1
  calc ((X1◇X1)◇((X1◇X1)◇(X1◇X1)))
   _ = ((((X1◇X1)◇((X1◇X1)◇(X1◇X1)))◇(X1◇X1))◇(X1◇X1)) := (c_0_5 ((X1◇X1)) X1).symm
   _ = ((X1◇X1)◇(X1◇X1)) := congrArg (·◇(X1◇X1)) (c_0_4 ((X1◇X1)) X1)
 have c_0_49 : ∀ (X1 X2 X3 X4 esk1_0 : G), (X1◇(X1◇((((((X1◇X2)◇X2)◇X3)◇X3)◇X4)◇X4))) = (X1◇(X1◇((X1◇esk1_0)◇esk1_0))) := by
  intro X1 X2 X3 X4 esk1_0
  calc (X1◇(X1◇((((((X1◇X2)◇X2)◇X3)◇X3)◇X4)◇X4)))
   _ = (X1◇(((X1◇(X1◇((X1◇esk1_0)◇esk1_0)))◇((((((X1◇X2)◇X2)◇X3)◇X3)◇X4)◇X4))◇((((((X1◇X2)◇X2)◇X3)◇X3)◇X4)◇X4))) := congrArg (X1◇·) (congrArg (·◇((((((X1◇X2)◇X2)◇X3)◇X3)◇X4)◇X4)) ((c_0_45 X1 esk1_0 X2 X3 X4).symm))
   _ = (X1◇(X1◇((X1◇esk1_0)◇esk1_0))) := c_0_33 X1 esk1_0 (((((((X1◇X2)◇X2)◇X3)◇X3)◇X4)◇X4))
 have c_0_50 : ∀ (X1 X2 X3 : G), ((X1◇(X1◇X2))◇((X2◇(X2◇X2))◇(((X2◇(X2◇X2))◇X3)◇X3))) = X1 := by
  intro X1 X2 X3
  calc ((X1◇(X1◇X2))◇((X2◇(X2◇X2))◇(((X2◇(X2◇X2))◇X3)◇X3)))
   _ = ((X1◇(X1◇((X2◇(X2◇X2))◇((X2◇(X2◇X2))◇(((X2◇(X2◇X2))◇X3)◇X3)))))◇((X2◇(X2◇X2))◇(((X2◇(X2◇X2))◇X3)◇X3))) := congrArg (·◇((X2◇(X2◇X2))◇(((X2◇(X2◇X2))◇X3)◇X3))) (congrArg (X1◇·) (congrArg (X1◇·) ((c_0_35 X2 X3).symm)))
   _ = X1 := c_0_20 X1 ((X2◇(X2◇X2))) X3
 have c_0_51 : ∀ (X1 : G), ((((X1◇(X1◇X1))◇X1)◇X1)◇((X1◇(X1◇X1))◇X1)) = ((X1◇(X1◇X1))◇X1) := by
  intro X1
  calc ((((X1◇(X1◇X1))◇X1)◇X1)◇((X1◇(X1◇X1))◇X1))
   _ = ((((X1◇(X1◇X1))◇X1)◇((((X1◇(X1◇X1))◇X1)◇((((X1◇(X1◇X1))◇X1)◇((((X1◇(X1◇X1))◇X1)◇X1)◇X1))◇((((X1◇(X1◇X1))◇X1)◇X1)◇X1)))◇((((X1◇(X1◇X1))◇X1)◇((((X1◇(X1◇X1))◇X1)◇X1)◇X1))◇((((X1◇(X1◇X1))◇X1)◇X1)◇X1))))◇((X1◇(X1◇X1))◇X1)) := congrArg (·◇((X1◇(X1◇X1))◇X1)) ((c_0_47 X1 (((((X1◇(X1◇X1))◇X1)◇((((X1◇(X1◇X1))◇X1)◇X1)◇X1))◇((((X1◇(X1◇X1))◇X1)◇X1)◇X1)))).symm)
   _ = ((X1◇(X1◇X1))◇X1) := c_0_46 (((X1◇(X1◇X1))◇X1)) (((((X1◇(X1◇X1))◇X1)◇X1)◇X1)) X1 X1
 have c_0_52 : ∀ (X1 : G), (((X1◇X1)◇(X1◇X1))◇(X1◇X1)) = (X1◇X1) := by
  intro X1
  calc (((X1◇X1)◇(X1◇X1))◇(X1◇X1))
   _ = (((X1◇X1)◇((X1◇X1)◇(X1◇X1)))◇(X1◇X1)) := congrArg (·◇(X1◇X1)) ((c_0_48 X1).symm)
   _ = (X1◇X1) := c_0_4 ((X1◇X1)) X1
 have c_0_53 : ∀ (X1 esk1_0 X2 X3 X4 X5 : G), ((X1◇(X1◇((X1◇esk1_0)◇esk1_0)))◇((((((((X1◇X2)◇X2)◇X3)◇X3)◇X4)◇X4)◇X5)◇X5)) = X1 := by
  intro X1 esk1_0 X2 X3 X4 X5
  calc ((X1◇(X1◇((X1◇esk1_0)◇esk1_0)))◇((((((((X1◇X2)◇X2)◇X3)◇X3)◇X4)◇X4)◇X5)◇X5))
   _ = ((X1◇(X1◇((((((X1◇X2)◇X2)◇X3)◇X3)◇X4)◇X4)))◇((((((((X1◇X2)◇X2)◇X3)◇X3)◇X4)◇X4)◇X5)◇X5)) := congrArg (·◇((((((((X1◇X2)◇X2)◇X3)◇X3)◇X4)◇X4)◇X5)◇X5)) ((c_0_49 X1 X2 X3 X4 esk1_0).symm)
   _ = X1 := (c_0_3 X1 (((((((X1◇X2)◇X2)◇X3)◇X3)◇X4)◇X4)) X5).symm
 have c_0_54x : ∀ (X0 X1 X2 X3 : G), ((X0◇(X0◇X1))◇((X1◇(X1◇X1))◇(((X1◇(X1◇X1))◇((X1◇(X1◇X1))◇(((X1◇(X1◇X1))◇X2)◇X2)))◇((((X1◇(X1◇X1))◇((X1◇(X1◇X1))◇(((X1◇(X1◇X1))◇X2)◇X2)))◇X3)◇X3)))) = X0 := by
  intro X0 X1 X2 X3
  calc ((X0◇(X0◇X1))◇((X1◇(X1◇X1))◇(((X1◇(X1◇X1))◇((X1◇(X1◇X1))◇(((X1◇(X1◇X1))◇X2)◇X2)))◇((((X1◇(X1◇X1))◇((X1◇(X1◇X1))◇(((X1◇(X1◇X1))◇X2)◇X2)))◇X3)◇X3))))
   _ = ((X0◇(X0◇X1))◇((X1◇(X1◇X1))◇(((X1◇(X1◇X1))◇((((X1◇(X1◇X1))◇((X1◇(X1◇X1))◇(((X1◇(X1◇X1))◇X2)◇X2)))◇X3)◇X3))◇((((X1◇(X1◇X1))◇((X1◇(X1◇X1))◇(((X1◇(X1◇X1))◇X2)◇X2)))◇X3)◇X3)))) := congrArg ((X0◇(X0◇X1))◇·) (congrArg ((X1◇(X1◇X1))◇·) (congrArg (·◇((((X1◇(X1◇X1))◇((X1◇(X1◇X1))◇(((X1◇(X1◇X1))◇X2)◇X2)))◇X3)◇X3)) ((c_0_33 ((X1◇(X1◇X1))) X2 X3).symm)))
   _ = X0 := c_0_50 X0 X1 (((((X1◇(X1◇X1))◇((X1◇(X1◇X1))◇(((X1◇(X1◇X1))◇X2)◇X2)))◇X3)◇X3))
 have c_0_54 : ∀ (X1 X2 X3 : G), ((X1◇(X1◇X2))◇((X2◇(X2◇X2))◇(X2◇((X2◇X3)◇X3)))) = X1 := by
  intro X1 X2 X3
  have strict_rw_5 := (c_0_54x X1 X2 X1 X3)
  rw [c_0_35] at strict_rw_5
  exact strict_rw_5
 have c_0_55 : ∀ (X1 : G), (X1◇(((X1◇(X1◇X1))◇X1)◇((X1◇(X1◇X1))◇X1))) = (X1◇(X1◇X1)) := by
  intro X1
  calc (X1◇(((X1◇(X1◇X1))◇X1)◇((X1◇(X1◇X1))◇X1)))
   _ = (X1◇(((((X1◇(X1◇X1))◇X1)◇X1)◇((X1◇(X1◇X1))◇X1))◇((X1◇(X1◇X1))◇X1))) := congrArg (X1◇·) (congrArg (·◇((X1◇(X1◇X1))◇X1)) ((c_0_51 X1).symm))
   _ = (X1◇(X1◇X1)) := c_0_36 X1 X1 (((X1◇(X1◇X1))◇X1))
 have c_0_56 : ∀ (X1 X2 : G), ((X1◇X1)◇(((X1◇X1)◇X2)◇X2)) = ((X1◇X1)◇(X1◇X1)) := by
  intro X1 X2
  clear h c_0_4 c_0_5 c_0_6x c_0_6 c_0_7 c_0_8 c_0_9 c_0_10 c_0_11 c_0_12 c_0_13 c_0_14 c_0_15 c_0_16 c_0_17x c_0_17 c_0_18 c_0_19 c_0_20x c_0_20 c_0_21 c_0_22 c_0_23
  clear c_0_24 c_0_25 c_0_26 c_0_27 c_0_28 c_0_29 c_0_30 c_0_31 c_0_32 c_0_33 c_0_34 c_0_35 c_0_36 c_0_37x c_0_37 c_0_38 c_0_39 c_0_40 c_0_41 c_0_42 c_0_43 c_0_44 c_0_45 c_0_46
  clear c_0_47 c_0_48 c_0_49 c_0_50 c_0_51 c_0_53 c_0_54x c_0_54 c_0_55
  grind
 have c_0_57 : ∀ (X1 : G), (((X1◇X1)◇(X1◇X1))◇((X1◇X1)◇(X1◇X1))) = (X1◇X1) := by
  intro X1
  calc (((X1◇X1)◇(X1◇X1))◇((X1◇X1)◇(X1◇X1)))
   _ = (((X1◇X1)◇((X1◇X1)◇(X1◇X1)))◇((X1◇X1)◇(X1◇X1))) := congrArg (·◇((X1◇X1)◇(X1◇X1))) ((c_0_48 X1).symm)
   _ = (((X1◇X1)◇((X1◇X1)◇((X1◇X1)◇(X1◇X1))))◇((X1◇X1)◇(X1◇X1))) := congrArg (·◇((X1◇X1)◇(X1◇X1))) (congrArg ((X1◇X1)◇·) ((c_0_48 X1).symm))
   _ = (X1◇X1) := c_0_4 ((X1◇X1)) ((X1◇X1))
 have c_0_58 : ∀ (X1 X2 X3 X4 X5 : G), (((X1◇(X1◇(X2◇(X2◇X3))))◇X1)◇(((X2◇((X3◇X4)◇X4))◇X5)◇X5)) = (X1◇(X1◇(X2◇(X2◇X3)))) := by
  intro X1 X2 X3 X4 X5
  calc (((X1◇(X1◇(X2◇(X2◇X3))))◇X1)◇(((X2◇((X3◇X4)◇X4))◇X5)◇X5))
   _ = (((X1◇(X1◇(X2◇(X2◇X3))))◇X1)◇(((((X2◇(X2◇X3))◇((X3◇X4)◇X4))◇((X3◇X4)◇X4))◇X5)◇X5)) := congrArg (((X1◇(X1◇(X2◇(X2◇X3))))◇X1)◇·) (congrArg (·◇X5) (congrArg (·◇X5) (congrArg (·◇((X3◇X4)◇X4)) (((c_0_3 X2 X3 X4).symm).symm))))
   _ = (X1◇(X1◇(X2◇(X2◇X3)))) := c_0_24 X1 ((X2◇(X2◇X3))) (((X3◇X4)◇X4)) X5
 have c_0_59 : ∀ (X1 X2 X3 : G), ((X1◇(X1◇((X2◇(X2◇X3))◇((X2◇(X2◇X3))◇X3))))◇X2) = X1 := by
  intro X1 X2 X3
  calc ((X1◇(X1◇((X2◇(X2◇X3))◇((X2◇(X2◇X3))◇X3))))◇X2)
   _ = ((X1◇(X1◇((X2◇(X2◇X3))◇((X2◇(X2◇X3))◇X3))))◇((X2◇(X2◇X3))◇((X3◇X1)◇X1))) := congrArg ((X1◇(X1◇((X2◇(X2◇X3))◇((X2◇(X2◇X3))◇X3))))◇·) (((c_0_3 X2 X3 X1).symm).symm)
   _ = X1 := c_0_29 X1 ((X2◇(X2◇X3))) X3 X1
 have c_0_60 : ∀ (X1 X2 X3 X4 : G), ((X1◇(X1◇(((X2◇((X2◇X3)◇X3))◇X4)◇X4)))◇(((X2◇((X2◇X3)◇X3))◇X4)◇X4)) = X1 := by
  intro X1 X2 X3 X4
  calc ((X1◇(X1◇(((X2◇((X2◇X3)◇X3))◇X4)◇X4)))◇(((X2◇((X2◇X3)◇X3))◇X4)◇X4))
   _ = ((X1◇(X1◇(((((X2◇((X2◇X3)◇X3))◇X4)◇X4)◇((((X2◇((X2◇X3)◇X3))◇X4)◇X4)◇(X2◇((X2◇X3)◇X3))))◇(((X2◇((X2◇X3)◇X3))◇X4)◇X4))))◇(((X2◇((X2◇X3)◇X3))◇X4)◇X4)) := congrArg (·◇(((X2◇((X2◇X3)◇X3))◇X4)◇X4)) (congrArg (X1◇·) (congrArg (X1◇·) (((c_0_3 ((((X2◇((X2◇X3)◇X3))◇X4)◇X4)) ((X2◇((X2◇X3)◇X3))) X4).symm).symm)))
   _ = X1 := c_0_14 X1 ((((X2◇((X2◇X3)◇X3))◇X4)◇X4)) X2 X3
 have c_0_61 : ∀ (X1 X2 X3 X4 X5 esk1_0 : G), (X1◇(X1◇((((((((X1◇X2)◇X2)◇X3)◇X3)◇X4)◇X4)◇X5)◇X5))) = (X1◇(X1◇((X1◇esk1_0)◇esk1_0))) := by
  intro X1 X2 X3 X4 X5 esk1_0
  calc (X1◇(X1◇((((((((X1◇X2)◇X2)◇X3)◇X3)◇X4)◇X4)◇X5)◇X5)))
   _ = (X1◇(((X1◇(X1◇((X1◇esk1_0)◇esk1_0)))◇((((((((X1◇X2)◇X2)◇X3)◇X3)◇X4)◇X4)◇X5)◇X5))◇((((((((X1◇X2)◇X2)◇X3)◇X3)◇X4)◇X4)◇X5)◇X5))) := congrArg (X1◇·) (congrArg (·◇((((((((X1◇X2)◇X2)◇X3)◇X3)◇X4)◇X4)◇X5)◇X5)) ((c_0_53 X1 esk1_0 X2 X3 X4 X5).symm))
   _ = (X1◇(X1◇((X1◇esk1_0)◇esk1_0))) := c_0_33 X1 esk1_0 (((((((((X1◇X2)◇X2)◇X3)◇X3)◇X4)◇X4)◇X5)◇X5))
 have c_0_62x : ∀ (X0 X1 : G), ((X0◇(X0◇(X0◇X0)))◇(((((X0◇(X0◇X0))◇X0)◇((X0◇(X0◇X0))◇X0))◇((((X0◇(X0◇X0))◇X0)◇((X0◇(X0◇X0))◇X0))◇(((X0◇(X0◇X0))◇X0)◇((X0◇(X0◇X0))◇X0))))◇((((X0◇(X0◇X0))◇X0)◇((X0◇(X0◇X0))◇X0))◇(((((X0◇(X0◇X0))◇X0)◇((X0◇(X0◇X0))◇X0))◇X1)◇X1)))) = X0 := by
  intro X0 X1
  calc ((X0◇(X0◇(X0◇X0)))◇(((((X0◇(X0◇X0))◇X0)◇((X0◇(X0◇X0))◇X0))◇((((X0◇(X0◇X0))◇X0)◇((X0◇(X0◇X0))◇X0))◇(((X0◇(X0◇X0))◇X0)◇((X0◇(X0◇X0))◇X0))))◇((((X0◇(X0◇X0))◇X0)◇((X0◇(X0◇X0))◇X0))◇(((((X0◇(X0◇X0))◇X0)◇((X0◇(X0◇X0))◇X0))◇X1)◇X1))))
   _ = ((X0◇(X0◇(((X0◇(X0◇X0))◇X0)◇((X0◇(X0◇X0))◇X0))))◇(((((X0◇(X0◇X0))◇X0)◇((X0◇(X0◇X0))◇X0))◇((((X0◇(X0◇X0))◇X0)◇((X0◇(X0◇X0))◇X0))◇(((X0◇(X0◇X0))◇X0)◇((X0◇(X0◇X0))◇X0))))◇((((X0◇(X0◇X0))◇X0)◇((X0◇(X0◇X0))◇X0))◇(((((X0◇(X0◇X0))◇X0)◇((X0◇(X0◇X0))◇X0))◇X1)◇X1)))) := congrArg (·◇(((((X0◇(X0◇X0))◇X0)◇((X0◇(X0◇X0))◇X0))◇((((X0◇(X0◇X0))◇X0)◇((X0◇(X0◇X0))◇X0))◇(((X0◇(X0◇X0))◇X0)◇((X0◇(X0◇X0))◇X0))))◇((((X0◇(X0◇X0))◇X0)◇((X0◇(X0◇X0))◇X0))◇(((((X0◇(X0◇X0))◇X0)◇((X0◇(X0◇X0))◇X0))◇X1)◇X1)))) (congrArg (X0◇·) ((c_0_55 X0).symm))
   _ = X0 := c_0_54 X0 ((((X0◇(X0◇X0))◇X0)◇((X0◇(X0◇X0))◇X0))) X1
 have c_0_62 : ∀ (X1 : G), ((X1◇(X1◇(X1◇X1)))◇(((X1◇(X1◇X1))◇X1)◇((X1◇(X1◇X1))◇X1))) = X1 := by
  intro X1
  have strict_rw_6 := (c_0_62x X1 X1)
  rw [c_0_48, c_0_56, c_0_57] at strict_rw_6
  exact strict_rw_6
 have c_0_63 : ∀ (X1 X2 X3 X4 : G), ((X1◇(X1◇(X1◇X1)))◇(((((((X1◇(X1◇X1))◇X2)◇X2)◇X3)◇X3)◇X4)◇X4)) = X1 := by
  intro X1 X2 X3 X4
  calc ((X1◇(X1◇(X1◇X1)))◇(((((((X1◇(X1◇X1))◇X2)◇X2)◇X3)◇X3)◇X4)◇X4))
   _ = ((X1◇(X1◇(((((X1◇(X1◇X1))◇X2)◇X2)◇X3)◇X3)))◇(((((((X1◇(X1◇X1))◇X2)◇X2)◇X3)◇X3)◇X4)◇X4)) := congrArg (·◇(((((((X1◇(X1◇X1))◇X2)◇X2)◇X3)◇X3)◇X4)◇X4)) (congrArg (X1◇·) ((c_0_36 X1 X2 X3).symm))
   _ = X1 := (c_0_3 X1 ((((((X1◇(X1◇X1))◇X2)◇X2)◇X3)◇X3)) X4).symm
 have c_0_64 : ∀ (X1 X2 X3 : G), ((X1◇(X1◇(X2◇X2)))◇(((X1◇(X1◇(X2◇X2)))◇X3)◇X3)) = ((X1◇(X1◇(X2◇X2)))◇(X1◇(X2◇X2))) := by
  intro X1 X2 X3
  calc ((X1◇(X1◇(X2◇X2)))◇(((X1◇(X1◇(X2◇X2)))◇X3)◇X3))
   _ = ((((X1◇(X1◇(X2◇X2)))◇(((X1◇(X1◇(X2◇X2)))◇X3)◇X3))◇(((X1◇(X1◇(X2◇X2)))◇(((X1◇(X1◇(X2◇X2)))◇X3)◇X3))◇(X1◇(X1◇(X2◇X2)))))◇(X1◇(X2◇X2))) := (c_0_11 (((X1◇(X1◇(X2◇X2)))◇(((X1◇(X1◇(X2◇X2)))◇X3)◇X3))) X1 X2).symm
   _ = ((((X1◇(X1◇(X2◇X2)))◇(((X1◇(X1◇(X2◇X2)))◇X3)◇X3))◇(X1◇(X1◇(X2◇X2))))◇(X1◇(X2◇X2))) := congrArg (·◇(X1◇(X2◇X2))) (congrArg (((X1◇(X1◇(X2◇X2)))◇(((X1◇(X1◇(X2◇X2)))◇X3)◇X3))◇·) (c_0_19 ((X1◇(X1◇(X2◇X2)))) X3))
   _ = ((X1◇(X1◇(X2◇X2)))◇(X1◇(X2◇X2))) := congrArg (·◇(X1◇(X2◇X2))) (((c_0_19 ((X1◇(X1◇(X2◇X2)))) X3).symm).symm)
 have c_0_65 : ∀ (X1 X2 X3 : G), (X1◇((X1◇X2)◇X2)) = (X1◇(X1◇((X1◇(X1◇X3))◇((X1◇(X1◇X3))◇X3)))) := by
  intro X1 X2 X3
  calc (X1◇((X1◇X2)◇X2))
   _ = (((X1◇(X1◇((X1◇(X1◇X3))◇((X1◇(X1◇X3))◇X3))))◇X1)◇((X1◇X2)◇X2)) := congrArg (·◇((X1◇X2)◇X2)) ((c_0_59 X1 X1 X3).symm)
   _ = (((X1◇(X1◇((X1◇(X1◇X3))◇((X1◇(X1◇X3))◇X3))))◇((X1◇(X1◇((X1◇(X1◇X3))◇((X1◇(X1◇X3))◇X3))))◇X1))◇((X1◇X2)◇X2)) := congrArg (·◇((X1◇X2)◇X2)) (congrArg ((X1◇(X1◇((X1◇(X1◇X3))◇((X1◇(X1◇X3))◇X3))))◇·) ((c_0_59 X1 X1 X3).symm))
   _ = (X1◇(X1◇((X1◇(X1◇X3))◇((X1◇(X1◇X3))◇X3)))) := (c_0_3 ((X1◇(X1◇((X1◇(X1◇X3))◇((X1◇(X1◇X3))◇X3))))) X1 X2).symm
 have c_0_66 : ∀ (X1 X2 X3 : G), ((X1◇(X1◇(X1◇X1)))◇(((X1◇((X1◇X2)◇X2))◇X3)◇X3)) = X1 := by
  intro X1 X2 X3
  calc ((X1◇(X1◇(X1◇X1)))◇(((X1◇((X1◇X2)◇X2))◇X3)◇X3))
   _ = ((X1◇(X1◇(((X1◇((X1◇X2)◇X2))◇X3)◇X3)))◇(((X1◇((X1◇X2)◇X2))◇X3)◇X3)) := congrArg (·◇(((X1◇((X1◇X2)◇X2))◇X3)◇X3)) (congrArg (X1◇·) ((c_0_37 X1 X2 X3).symm))
   _ = X1 := c_0_60 X1 X1 X2 X3
 have c_0_67x : ∀ (X0 X1 X2 X3 X4 : G), ((X0◇(X0◇(X0◇X0)))◇((X0◇(X0◇(X0◇X0)))◇(((((((X0◇(((X0◇(X0◇X0))◇X0)◇((X0◇(X0◇X0))◇X0)))◇X1)◇X1)◇X2)◇X2)◇X3)◇X3))) = ((X0◇(X0◇(X0◇X0)))◇((X0◇(X0◇(X0◇X0)))◇(((X0◇(X0◇(X0◇X0)))◇X4)◇X4))) := by
  intro X0 X1 X2 X3 X4
  calc ((X0◇(X0◇(X0◇X0)))◇((X0◇(X0◇(X0◇X0)))◇(((((((X0◇(((X0◇(X0◇X0))◇X0)◇((X0◇(X0◇X0))◇X0)))◇X1)◇X1)◇X2)◇X2)◇X3)◇X3)))
   _ = ((X0◇(X0◇(X0◇X0)))◇((X0◇(X0◇(X0◇X0)))◇(((((((((X0◇(X0◇(X0◇X0)))◇(((X0◇(X0◇X0))◇X0)◇((X0◇(X0◇X0))◇X0)))◇(((X0◇(X0◇X0))◇X0)◇((X0◇(X0◇X0))◇X0)))◇X1)◇X1)◇X2)◇X2)◇X3)◇X3))) := congrArg ((X0◇(X0◇(X0◇X0)))◇·) (congrArg ((X0◇(X0◇(X0◇X0)))◇·) (congrArg (·◇X3) (congrArg (·◇X3) (congrArg (·◇X2) (congrArg (·◇X2) (congrArg (·◇X1) (congrArg (·◇X1) (congrArg (·◇(((X0◇(X0◇X0))◇X0)◇((X0◇(X0◇X0))◇X0))) ((c_0_62 X0).symm)))))))))
   _ = ((X0◇(X0◇(X0◇X0)))◇((X0◇(X0◇(X0◇X0)))◇(((X0◇(X0◇(X0◇X0)))◇X4)◇X4))) := c_0_61 ((X0◇(X0◇(X0◇X0)))) ((((X0◇(X0◇X0))◇X0)◇((X0◇(X0◇X0))◇X0))) X1 X2 X3 X4
 have c_0_67 : ∀ (X1 : G), ((X1◇(X1◇(X1◇X1)))◇((X1◇(X1◇(X1◇X1)))◇(X1◇(X1◇X1)))) = ((X1◇(X1◇(X1◇X1)))◇X1) := by
  intro X1
  have strict_rw_7 := ((c_0_67x X1 X1 X1 X1 X1).symm)
  rw [c_0_55, c_0_63, c_0_64] at strict_rw_7
  exact strict_rw_7
 have c_0_68 : ∀ (X1 X2 esk1_0 : G), (X1◇((X1◇X2)◇X2)) = (X1◇(X1◇((X1◇(X1◇((X1◇esk1_0)◇esk1_0)))◇X1))) := by
  intro X1 X2 esk1_0
  clear h c_0_3 c_0_4 c_0_5 c_0_6x c_0_6 c_0_7 c_0_8 c_0_9 c_0_10 c_0_11 c_0_12 c_0_13 c_0_14 c_0_15 c_0_16 c_0_17x c_0_17 c_0_18 c_0_19 c_0_20x c_0_20 c_0_21 c_0_22
  clear c_0_23 c_0_24 c_0_25 c_0_27 c_0_28 c_0_29 c_0_30 c_0_31 c_0_32 c_0_33 c_0_34 c_0_35 c_0_36 c_0_37x c_0_37 c_0_38 c_0_39 c_0_40 c_0_41 c_0_43 c_0_44 c_0_45 c_0_46 c_0_47
  clear c_0_48 c_0_49 c_0_50 c_0_51 c_0_52 c_0_53 c_0_54x c_0_54 c_0_55 c_0_56 c_0_57 c_0_58 c_0_59 c_0_60 c_0_61 c_0_62x c_0_62 c_0_63 c_0_64 c_0_66 c_0_67x c_0_67
  let T : G := ((((X1◇X1)◇X1)◇X1)◇X1)
  let P : G := X1◇(X1◇T)
  let Q : G := X1◇(X1◇((X1◇esk1_0)◇esk1_0))
  have hpq : P = Q := by
   have strict_rw_8 := (c_0_42 X1 X1 X1 esk1_0)
   exact strict_rw_8
  have hqt : Q◇T = X1 := by
   have strict_rw_9 := (c_0_26 X1 esk1_0 X1 X1)
   exact strict_rw_9
  calc X1◇((X1◇X2)◇X2)
   _ = X1◇(X1◇(P◇(P◇T))) := by
    have strict_rw_10 := (c_0_65 X1 X2 T)
    exact strict_rw_10
   _ = X1◇(X1◇(P◇(Q◇T))) :=
    congrArg (fun u => X1◇(X1◇(P◇(u◇T)))) hpq
   _ = X1◇(X1◇(Q◇(Q◇T))) :=
    congrArg (fun u => X1◇(X1◇(u◇(Q◇T)))) hpq
   _ = X1◇(X1◇(Q◇X1)) :=
    congrArg (fun u => X1◇(X1◇(Q◇u))) hqt
   _ = X1◇(X1◇((X1◇(X1◇((X1◇esk1_0)◇esk1_0)))◇X1)) := by
    rfl
 have c_0_69 : ∀ (X1 X2 esk1_0 X3 : G), ((X1◇(X1◇(X2◇(X2◇((X2◇esk1_0)◇esk1_0)))))◇(X2◇((X2◇X3)◇X3))) = X1 := by
  intro X1 X2 esk1_0 X3
  grind
 have c_0_70 : ∀ (X1 X2 X3 : G), ((X1◇(X1◇(X1◇X1)))◇(X1◇((((X1◇(X1◇(X2◇X2)))◇X1)◇X3)◇X3))) = X1 := by
  intro X1 X2 X3
  calc ((X1◇(X1◇(X1◇X1)))◇(X1◇((((X1◇(X1◇(X2◇X2)))◇X1)◇X3)◇X3)))
   _ = ((X1◇(X1◇(X1◇X1)))◇(((X1◇((X1◇X1)◇X1))◇((((X1◇(X1◇(X2◇X2)))◇X1)◇X3)◇X3))◇((((X1◇(X1◇(X2◇X2)))◇X1)◇X3)◇X3))) := congrArg ((X1◇(X1◇(X1◇X1)))◇·) (congrArg (·◇((((X1◇(X1◇(X2◇X2)))◇X1)◇X3)◇X3)) ((c_0_18 X1 X1 X2 X3).symm))
   _ = X1 := c_0_66 X1 X1 (((((X1◇(X1◇(X2◇X2)))◇X1)◇X3)◇X3))
 have c_0_71 : ∀ (X1 X2 : G), (((X1◇(X1◇(X1◇X1)))◇X1)◇(X1◇((X1◇X2)◇X2))) = (X1◇(X1◇(X1◇X1))) := by
  intro X1 X2
  calc (((X1◇(X1◇(X1◇X1)))◇X1)◇(X1◇((X1◇X2)◇X2)))
   _ = (((X1◇(X1◇(X1◇X1)))◇((X1◇(X1◇(X1◇X1)))◇(X1◇(X1◇X1))))◇(X1◇((X1◇X2)◇X2))) := congrArg (·◇(X1◇((X1◇X2)◇X2))) ((c_0_67 X1).symm)
   _ = (X1◇(X1◇(X1◇X1))) := c_0_29 ((X1◇(X1◇(X1◇X1)))) X1 X1 X2
 have c_0_72 : ∀ (X1 X2 X3 : G), (X1◇((X1◇X2)◇X2)) = (X1◇(X1◇((X1◇(X1◇((X1◇X3)◇X3)))◇X1))) := by
  intro X1 X2 X3
  calc (X1◇((X1◇X2)◇X2))
   _ = (X1◇((X1◇X1)◇X1)) := (c_0_31 X1 X1 X2).symm
   _ = (X1◇(X1◇((X1◇(X1◇((X1◇X3)◇X3)))◇X1))) := c_0_68 X1 X1 X3
 have c_0_73 : ∀ (X1 X2 X3 X4 : G), ((X1◇(X1◇X1))◇((((((X1◇(X1◇(X2◇X2)))◇X1)◇X3)◇X3)◇X4)◇X4)) = X1 := by
  intro X1 X2 X3 X4
  calc ((X1◇(X1◇X1))◇((((((X1◇(X1◇(X2◇X2)))◇X1)◇X3)◇X3)◇X4)◇X4))
   _ = ((X1◇(X1◇((((X1◇(X1◇(X2◇X2)))◇X1)◇X3)◇X3)))◇((((((X1◇(X1◇(X2◇X2)))◇X1)◇X3)◇X3)◇X4)◇X4)) := congrArg (·◇((((((X1◇(X1◇(X2◇X2)))◇X1)◇X3)◇X3)◇X4)◇X4)) ((c_0_41 X1 X2 X3).symm)
   _ = X1 := (c_0_3 X1 (((((X1◇(X1◇(X2◇X2)))◇X1)◇X3)◇X3)) X4).symm
 have c_0_74x : ∀ (X0 X1 X2 X3 X4 : G), (X0◇((X0◇X1)◇X1)) = (((X0◇((X0◇X1)◇X1))◇X0)◇((((((X0◇(X0◇(X2◇X2)))◇X0)◇X3)◇X3)◇X4)◇X4)) := by
  intro X0 X1 X2 X3 X4
  calc (X0◇((X0◇X1)◇X1))
   _ = (((X0◇((X0◇X1)◇X1))◇((X0◇((X0◇X1)◇X1))◇((((X0◇(X0◇(X2◇X2)))◇X0)◇X3)◇X3)))◇((((((X0◇(X0◇(X2◇X2)))◇X0)◇X3)◇X3)◇X4)◇X4)) := c_0_3 ((X0◇((X0◇X1)◇X1))) (((((X0◇(X0◇(X2◇X2)))◇X0)◇X3)◇X3)) X4
   _ = (((X0◇((X0◇X1)◇X1))◇X0)◇((((((X0◇(X0◇(X2◇X2)))◇X0)◇X3)◇X3)◇X4)◇X4)) := congrArg (·◇((((((X0◇(X0◇(X2◇X2)))◇X0)◇X3)◇X3)◇X4)◇X4)) (congrArg ((X0◇((X0◇X1)◇X1))◇·) (c_0_18 X0 X1 X2 X3))
 have c_0_74 : ∀ (X1 X2 X3 X4 X5 : G), (X1◇((((((X1◇(X1◇(X2◇X2)))◇X1)◇X3)◇X3)◇X4)◇X4)) = (X1◇((X1◇X5)◇X5)) := by
  intro X1 X2 X3 X4 X5
  have strict_rw_11 := ((c_0_74x X1 X5 X2 X3 X4).symm)
  rw [c_0_19] at strict_rw_11
  exact strict_rw_11
 have c_0_75 : ∀ (X1 X2 X3 X4 : G), ((X1◇(X1◇(X2◇(X2◇((X2◇X3)◇X3)))))◇(X2◇((X2◇X4)◇X4))) = X1 := by
  intro X1 X2 X3 X4
  calc ((X1◇(X1◇(X2◇(X2◇((X2◇X3)◇X3)))))◇(X2◇((X2◇X4)◇X4)))
   _ = ((X1◇(X1◇(X2◇(X2◇((X2◇X1)◇X1)))))◇(X2◇((X2◇X4)◇X4))) := congrArg (·◇(X2◇((X2◇X4)◇X4))) (congrArg (X1◇·) (congrArg (X1◇·) (congrArg (X2◇·) ((c_0_31 X2 X1 X3).symm))))
   _ = X1 := c_0_69 X1 X2 X1 X4
 have c_0_76 : ∀ (X1 X2 : G), ((X1◇(X1◇(X1◇X1)))◇(X1◇((X1◇(X1◇(X1◇X1)))◇(X1◇((X1◇X2)◇X2))))) = X1 := by
  intro X1 X2
  calc ((X1◇(X1◇(X1◇X1)))◇(X1◇((X1◇(X1◇(X1◇X1)))◇(X1◇((X1◇X2)◇X2)))))
   _ = ((X1◇(X1◇(X1◇X1)))◇(X1◇((((X1◇(X1◇(X1◇X1)))◇X1)◇(X1◇((X1◇X2)◇X2)))◇(X1◇((X1◇X2)◇X2))))) := congrArg ((X1◇(X1◇(X1◇X1)))◇·) (congrArg (X1◇·) (congrArg (·◇(X1◇((X1◇X2)◇X2))) ((c_0_71 X1 X2).symm)))
   _ = X1 := c_0_70 X1 X1 ((X1◇((X1◇X2)◇X2)))
 have c_0_77 : ∀ (X1 X2 : G), (X1◇(X1◇((X1◇(X1◇(X1◇X1)))◇(X1◇((X1◇X2)◇X2))))) = (X1◇(X1◇X1)) := by
  intro X1 X2
  calc (X1◇(X1◇((X1◇(X1◇(X1◇X1)))◇(X1◇((X1◇X2)◇X2)))))
   _ = (X1◇(X1◇((((X1◇(X1◇(X1◇X1)))◇X1)◇(X1◇((X1◇X2)◇X2)))◇(X1◇((X1◇X2)◇X2))))) := congrArg (X1◇·) (congrArg (X1◇·) (congrArg (·◇(X1◇((X1◇X2)◇X2))) ((c_0_71 X1 X2).symm)))
   _ = (X1◇(X1◇X1)) := c_0_41 X1 X1 ((X1◇((X1◇X2)◇X2)))
 have c_0_78 : ∀ (X1 esk1_0 : G), ((X1◇(X1◇X1))◇((X1◇(X1◇X1))◇(X1◇(X1◇(X1◇X1))))) = ((X1◇(X1◇X1))◇(X1◇((X1◇esk1_0)◇esk1_0))) := by
  intro X1 esk1_0
  grind
 have c_0_79 : ∀ (X1 X2 : G), ((X1◇(X1◇X1))◇((X1◇(X1◇X1))◇(X1◇((X1◇X2)◇X2)))) = X1 := by
  intro X1 X2
  clear h c_0_3 c_0_4 c_0_5 c_0_6x c_0_6 c_0_7 c_0_8 c_0_9 c_0_10 c_0_11 c_0_12 c_0_13 c_0_14 c_0_15 c_0_16 c_0_17x c_0_17 c_0_18 c_0_19 c_0_20x c_0_20 c_0_21 c_0_22
  clear c_0_23 c_0_24 c_0_25 c_0_26 c_0_27 c_0_28 c_0_29 c_0_30 c_0_31 c_0_32 c_0_34 c_0_36 c_0_37x c_0_37 c_0_38 c_0_39 c_0_40 c_0_41 c_0_42 c_0_43 c_0_44 c_0_45 c_0_46 c_0_47
  clear c_0_48 c_0_49 c_0_50 c_0_51 c_0_52 c_0_53 c_0_54x c_0_54 c_0_55 c_0_56 c_0_57 c_0_58 c_0_59 c_0_60 c_0_61 c_0_62x c_0_62 c_0_63 c_0_64 c_0_65 c_0_66 c_0_67x c_0_67 c_0_68
  clear c_0_69 c_0_70 c_0_71 c_0_72 c_0_73 c_0_74x c_0_74 c_0_75 c_0_76 c_0_77 c_0_78
  grind
 have c_0_80 : ∀ (X1 X2 X3 : G), (((X1◇(X1◇((X2◇(X2◇X2))◇X2)))◇X1)◇((X2◇X3)◇X3)) = (X1◇(X1◇((X2◇(X2◇X2))◇X2))) := by
  intro X1 X2 X3
  calc (((X1◇(X1◇((X2◇(X2◇X2))◇X2)))◇X1)◇((X2◇X3)◇X3))
   _ = (((X1◇(X1◇((X2◇(X2◇X2))◇X2)))◇((X1◇(X1◇((X2◇(X2◇X2))◇X2)))◇X2))◇((X2◇X3)◇X3)) := congrArg (·◇((X2◇X3)◇X3)) (congrArg ((X1◇(X1◇((X2◇(X2◇X2))◇X2)))◇·) ((c_0_44 X1 X2).symm))
   _ = (X1◇(X1◇((X2◇(X2◇X2))◇X2))) := (c_0_3 ((X1◇(X1◇((X2◇(X2◇X2))◇X2)))) X2 X3).symm
 have c_0_81x : ∀ (X0 X1 X2 X3 : G), ((X0◇(X0◇((X1◇(X1◇(X1◇X1)))◇((X1◇(X1◇(X1◇X1)))◇(X1◇(X1◇((X1◇(X1◇(X1◇X1)))◇(X1◇((X1◇X2)◇X2)))))))))◇((X1◇(X1◇(X1◇X1)))◇(((X1◇(X1◇(X1◇X1)))◇X3)◇X3))) = X0 := by
  intro X0 X1 X2 X3
  calc ((X0◇(X0◇((X1◇(X1◇(X1◇X1)))◇((X1◇(X1◇(X1◇X1)))◇(X1◇(X1◇((X1◇(X1◇(X1◇X1)))◇(X1◇((X1◇X2)◇X2)))))))))◇((X1◇(X1◇(X1◇X1)))◇(((X1◇(X1◇(X1◇X1)))◇X3)◇X3)))
   _ = ((X0◇(X0◇((X1◇(X1◇(X1◇X1)))◇((X1◇(X1◇(X1◇X1)))◇(((X1◇(X1◇(X1◇X1)))◇(X1◇((X1◇(X1◇(X1◇X1)))◇(X1◇((X1◇X2)◇X2)))))◇(X1◇((X1◇(X1◇(X1◇X1)))◇(X1◇((X1◇X2)◇X2)))))))))◇((X1◇(X1◇(X1◇X1)))◇(((X1◇(X1◇(X1◇X1)))◇X3)◇X3))) := congrArg (·◇((X1◇(X1◇(X1◇X1)))◇(((X1◇(X1◇(X1◇X1)))◇X3)◇X3))) (congrArg (X0◇·) (congrArg (X0◇·) (congrArg ((X1◇(X1◇(X1◇X1)))◇·) (congrArg ((X1◇(X1◇(X1◇X1)))◇·) (congrArg (·◇(X1◇((X1◇(X1◇(X1◇X1)))◇(X1◇((X1◇X2)◇X2))))) ((c_0_76 X1 X2).symm))))))
   _ = X0 := c_0_75 X0 ((X1◇(X1◇(X1◇X1)))) ((X1◇((X1◇(X1◇(X1◇X1)))◇(X1◇((X1◇X2)◇X2))))) X3
 have c_0_81 : ∀ (X1 X2 : G), ((X1◇(X1◇((X2◇(X2◇(X2◇X2)))◇X2)))◇((X2◇(X2◇(X2◇X2)))◇(X2◇(X2◇X2)))) = X1 := by
  intro X1 X2
  have strict_rw_12 := (c_0_81x X1 X2 X1 X1)
  rw [c_0_77, c_0_67, c_0_64] at strict_rw_12
  exact strict_rw_12
 have c_0_82x : ∀ (X0 X1 X2 : G), (X0◇(X0◇X0)) = (((X0◇(X0◇X0))◇((X0◇(X0◇X0))◇(X0◇((X0◇X1)◇X1))))◇((((X0◇(X0◇X0))◇(X0◇(X0◇(X0◇X0))))◇X2)◇X2)) := by
  intro X0 X1 X2
  calc (X0◇(X0◇X0))
   _ = (((X0◇(X0◇X0))◇((X0◇(X0◇X0))◇((X0◇(X0◇X0))◇(X0◇(X0◇(X0◇X0))))))◇((((X0◇(X0◇X0))◇(X0◇(X0◇(X0◇X0))))◇X2)◇X2)) := c_0_3 ((X0◇(X0◇X0))) (((X0◇(X0◇X0))◇(X0◇(X0◇(X0◇X0))))) X2
   _ = (((X0◇(X0◇X0))◇((X0◇(X0◇X0))◇(X0◇((X0◇X1)◇X1))))◇((((X0◇(X0◇X0))◇(X0◇(X0◇(X0◇X0))))◇X2)◇X2)) := congrArg (·◇((((X0◇(X0◇X0))◇(X0◇(X0◇(X0◇X0))))◇X2)◇X2)) (congrArg ((X0◇(X0◇X0))◇·) (c_0_78 X0 X1))
 have c_0_82 : ∀ (X1 X2 : G), (X1◇((((X1◇(X1◇X1))◇(X1◇(X1◇(X1◇X1))))◇X2)◇X2)) = (X1◇(X1◇X1)) := by
  intro X1 X2
  have strict_rw_13 := ((c_0_82x X1 X1 X2).symm)
  rw [c_0_79] at strict_rw_13
  exact strict_rw_13
 have c_0_83 : ∀ (X1 X2 : G), (X1◇((X1◇X2)◇X2)) = (X1◇(X1◇((X1◇(X1◇X1))◇X1))) := by
  intro X1 X2
  calc (X1◇((X1◇X2)◇X2))
   _ = (((X1◇(X1◇((X1◇(X1◇X1))◇X1)))◇X1)◇((X1◇X2)◇X2)) := congrArg (·◇((X1◇X2)◇X2)) ((c_0_44 X1 X1).symm)
   _ = (X1◇(X1◇((X1◇(X1◇X1))◇X1))) := c_0_80 X1 X1 X2
 have c_0_84 : ∀ (X1 X2 : G), ((X1◇((X1◇X2)◇X2))◇((X1◇(X1◇(X1◇X1)))◇(X1◇(X1◇X1)))) = X1 := by
  intro X1 X2
  calc ((X1◇((X1◇X2)◇X2))◇((X1◇(X1◇(X1◇X1)))◇(X1◇(X1◇X1))))
   _ = ((X1◇(X1◇((X1◇(X1◇(X1◇X1)))◇X1)))◇((X1◇(X1◇(X1◇X1)))◇(X1◇(X1◇X1)))) := congrArg (·◇((X1◇(X1◇(X1◇X1)))◇(X1◇(X1◇X1)))) (((c_0_9 X1 X2 X1).symm).symm)
   _ = X1 := c_0_81 X1 X1
 have c_0_85 : ∀ (X1 esk1_0 X2 : G), ((X1◇(X1◇((X1◇esk1_0)◇esk1_0)))◇(((X1◇((X1◇(X1◇((X1◇esk1_0)◇esk1_0)))◇X1))◇X2)◇X2)) = X1 := by
  intro X1 esk1_0 X2
  grind
 have c_0_86 : ∀ (X1 X2 X3 : G), ((X1◇((X1◇X2)◇X2))◇((((X1◇(X1◇X1))◇X1)◇X3)◇X3)) = X1 := by
  intro X1 X2 X3
  calc ((X1◇((X1◇X2)◇X2))◇((((X1◇(X1◇X1))◇X1)◇X3)◇X3))
   _ = ((X1◇(X1◇((X1◇(X1◇X1))◇X1)))◇((((X1◇(X1◇X1))◇X1)◇X3)◇X3)) := congrArg (·◇((((X1◇(X1◇X1))◇X1)◇X3)◇X3)) (((c_0_83 X1 X2).symm).symm)
   _ = X1 := (c_0_3 X1 (((X1◇(X1◇X1))◇X1)) X3).symm
 have c_0_87 : ∀ (X1 X2 X3 X4 : G), ((X1◇(X1◇((X1◇X2)◇X2)))◇(((X1◇((X1◇(X1◇((X1◇X3)◇X3)))◇X1))◇X4)◇X4)) = X1 := by
  intro X1 X2 X3 X4
  calc ((X1◇(X1◇((X1◇X2)◇X2)))◇(((X1◇((X1◇(X1◇((X1◇X3)◇X3)))◇X1))◇X4)◇X4))
   _ = ((X1◇(X1◇(X1◇((X1◇(X1◇((X1◇X3)◇X3)))◇X1))))◇(((X1◇((X1◇(X1◇((X1◇X3)◇X3)))◇X1))◇X4)◇X4)) := congrArg (·◇(((X1◇((X1◇(X1◇((X1◇X3)◇X3)))◇X1))◇X4)◇X4)) (congrArg (X1◇·) (((c_0_72 X1 X2 X3).symm).symm))
   _ = X1 := (c_0_3 X1 ((X1◇((X1◇(X1◇((X1◇X3)◇X3)))◇X1))) X4).symm
 have c_0_88 : ∀ (X1 X2 : G), (X1◇((X1◇X2)◇X2)) = (X1◇X1) := by
  intro X1 X2
  calc (X1◇((X1◇X2)◇X2))
   _ = (X1◇((X1◇((X1◇(X1◇(X1◇X1)))◇(X1◇(X1◇X1))))◇((X1◇(X1◇(X1◇X1)))◇(X1◇(X1◇X1))))) := (c_0_31 X1 (((X1◇(X1◇(X1◇X1)))◇(X1◇(X1◇X1)))) X2).symm
   _ = (X1◇X1) := congrArg (X1◇·) (c_0_84 X1 ((X1◇(X1◇X1))))
 have c_0_89x : ∀ (X0 X1 X2 : G), ((X0◇(X0◇((X1◇((X1◇X2)◇X2))◇((X1◇((X1◇X2)◇X2))◇X1))))◇X1) = X0 := by
  intro X0 X1 X2
  calc ((X0◇(X0◇((X1◇((X1◇X2)◇X2))◇((X1◇((X1◇X2)◇X2))◇X1))))◇X1)
   _ = ((X0◇(X0◇((X1◇((X1◇X2)◇X2))◇((X1◇((X1◇X2)◇X2))◇X1))))◇((X1◇((X1◇X2)◇X2))◇((X1◇(X1◇(X1◇X1)))◇(X1◇(X1◇X1))))) := congrArg ((X0◇(X0◇((X1◇((X1◇X2)◇X2))◇((X1◇((X1◇X2)◇X2))◇X1))))◇·) ((c_0_84 X1 X2).symm)
   _ = X0 := c_0_29 X0 ((X1◇((X1◇X2)◇X2))) X1 ((X1◇(X1◇X1)))
 have c_0_89 : ∀ (X1 X2 : G), ((X1◇(X1◇X2))◇X2) = X1 := by
  intro X1 X2
  have strict_rw_14 := (c_0_89x X1 X2 X1)
  rw [c_0_19, c_0_19] at strict_rw_14
  exact strict_rw_14
 have c_0_90 : ∀ (X1 X2 : G), (((X1◇X1)◇(X1◇X1))◇(((X1◇X1)◇X2)◇X2)) = (X1◇X1) := by
  intro X1 X2
  calc (((X1◇X1)◇(X1◇X1))◇(((X1◇X1)◇X2)◇X2))
   _ = (((X1◇X1)◇((X1◇X1)◇(X1◇X1)))◇(((X1◇X1)◇X2)◇X2)) := congrArg (·◇(((X1◇X1)◇X2)◇X2)) ((c_0_48 X1).symm)
   _ = (X1◇X1) := (c_0_3 ((X1◇X1)) ((X1◇X1)) X2).symm
 have c_0_91 : ∀ (X1 esk1_0 X2 : G), (X1◇(X1◇(((X1◇((X1◇(X1◇((X1◇esk1_0)◇esk1_0)))◇X1))◇X2)◇X2))) = (X1◇(X1◇((X1◇esk1_0)◇esk1_0))) := by
  intro X1 esk1_0 X2
  calc (X1◇(X1◇(((X1◇((X1◇(X1◇((X1◇esk1_0)◇esk1_0)))◇X1))◇X2)◇X2)))
   _ = (X1◇(((X1◇(X1◇((X1◇esk1_0)◇esk1_0)))◇(((X1◇((X1◇(X1◇((X1◇esk1_0)◇esk1_0)))◇X1))◇X2)◇X2))◇(((X1◇((X1◇(X1◇((X1◇esk1_0)◇esk1_0)))◇X1))◇X2)◇X2))) := congrArg (X1◇·) (congrArg (·◇(((X1◇((X1◇(X1◇((X1◇esk1_0)◇esk1_0)))◇X1))◇X2)◇X2)) ((c_0_85 X1 esk1_0 X2).symm))
   _ = (X1◇(X1◇((X1◇esk1_0)◇esk1_0))) := c_0_33 X1 esk1_0 ((((X1◇((X1◇(X1◇((X1◇esk1_0)◇esk1_0)))◇X1))◇X2)◇X2))
 have c_0_92 : ∀ (X1 X2 : G), ((((X1◇(X1◇X1))◇X2)◇X2)◇((((X1◇(X1◇X1))◇X2)◇X2)◇(X1◇(X1◇X1)))) = ((((X1◇(X1◇X1))◇X2)◇X2)◇(X1◇X1)) := by
  intro X1 X2
  calc ((((X1◇(X1◇X1))◇X2)◇X2)◇((((X1◇(X1◇X1))◇X2)◇X2)◇(X1◇(X1◇X1))))
   _ = ((((((X1◇(X1◇X1))◇X2)◇X2)◇((((X1◇(X1◇X1))◇X2)◇X2)◇(X1◇(X1◇X1))))◇(((X1◇(X1◇X1))◇X2)◇X2))◇(X1◇X1)) := (c_0_32 ((((X1◇(X1◇X1))◇X2)◇X2)) X1).symm
   _ = ((((X1◇(X1◇X1))◇X2)◇X2)◇(X1◇X1)) := congrArg (·◇(X1◇X1)) ((c_0_3 ((((X1◇(X1◇X1))◇X2)◇X2)) ((X1◇(X1◇X1))) X2).symm)
 have c_0_93 : ∀ (X1 X2 : G), (X1◇(X1◇((((X1◇(X1◇X1))◇X1)◇X2)◇X2))) = (X1◇(X1◇X1)) := by
  intro X1 X2
  calc (X1◇(X1◇((((X1◇(X1◇X1))◇X1)◇X2)◇X2)))
   _ = (X1◇(((X1◇((X1◇X1)◇X1))◇((((X1◇(X1◇X1))◇X1)◇X2)◇X2))◇((((X1◇(X1◇X1))◇X1)◇X2)◇X2))) := congrArg (X1◇·) (congrArg (·◇((((X1◇(X1◇X1))◇X1)◇X2)◇X2)) ((c_0_86 X1 X1 X2).symm))
   _ = (X1◇(X1◇X1)) := c_0_37 X1 X1 (((((X1◇(X1◇X1))◇X1)◇X2)◇X2))
 have c_0_94 : ∀ (X1 : G), ((X1◇(X1◇X1))◇(X1◇X1)) = X1 := by
  intro X1
  clear h c_0_3 c_0_4 c_0_5 c_0_6x c_0_6 c_0_7 c_0_8 c_0_9 c_0_10 c_0_11 c_0_12 c_0_13 c_0_14 c_0_15 c_0_16 c_0_17x c_0_17 c_0_18 c_0_19 c_0_20x c_0_20 c_0_21 c_0_22
  clear c_0_23 c_0_24 c_0_25 c_0_26 c_0_27 c_0_28 c_0_29 c_0_30 c_0_31 c_0_32 c_0_33 c_0_34 c_0_35 c_0_36 c_0_37x c_0_37 c_0_38 c_0_39 c_0_40 c_0_41 c_0_42 c_0_43 c_0_44 c_0_45
  clear c_0_46 c_0_47 c_0_48 c_0_49 c_0_50 c_0_51 c_0_52 c_0_53 c_0_54x c_0_54 c_0_55 c_0_56 c_0_57 c_0_58 c_0_59 c_0_60 c_0_61 c_0_62x c_0_62 c_0_63 c_0_64 c_0_65 c_0_66 c_0_67x
  clear c_0_67 c_0_68 c_0_69 c_0_70 c_0_71 c_0_72 c_0_73 c_0_74x c_0_74 c_0_75 c_0_76 c_0_77 c_0_78 c_0_79 c_0_80 c_0_81x c_0_81 c_0_82x c_0_82 c_0_83 c_0_84 c_0_85 c_0_86 c_0_89x
  clear c_0_91 c_0_92 c_0_93
  grind
 have c_0_95 : ∀ (X1 X2 X3 : G), (X1◇(X1◇(((X1◇((X1◇(X1◇((X1◇X2)◇X2)))◇X1))◇X3)◇X3))) = (X1◇(X1◇((X1◇X2)◇X2))) := by
  intro X1 X2 X3
  calc (X1◇(X1◇(((X1◇((X1◇(X1◇((X1◇X2)◇X2)))◇X1))◇X3)◇X3)))
   _ = (X1◇(X1◇(((X1◇((X1◇(X1◇((X1◇X2)◇X2)))◇X1))◇X3)◇X3))) := congrArg (X1◇·) (congrArg (X1◇·) (congrArg (·◇X3) (congrArg (·◇X3) (congrArg (X1◇·) (congrArg (·◇X1) (congrArg (X1◇·) ((c_0_31 X1 X2 X2).symm)))))))
   _ = (X1◇(X1◇((X1◇X2)◇X2))) := c_0_91 X1 X2 X3
 have c_0_96 : ∀ (X1 X2 X3 : G), (((((X1◇(X1◇X1))◇X2)◇X2)◇(X1◇X1))◇(((X1◇(X1◇X1))◇X3)◇X3)) = (((X1◇(X1◇X1))◇X2)◇X2) := by
  intro X1 X2 X3
  calc (((((X1◇(X1◇X1))◇X2)◇X2)◇(X1◇X1))◇(((X1◇(X1◇X1))◇X3)◇X3))
   _ = (((((X1◇(X1◇X1))◇X2)◇X2)◇((((X1◇(X1◇X1))◇X2)◇X2)◇(X1◇(X1◇X1))))◇(((X1◇(X1◇X1))◇X3)◇X3)) := congrArg (·◇(((X1◇(X1◇X1))◇X3)◇X3)) ((c_0_92 X1 X2).symm)
   _ = (((X1◇(X1◇X1))◇X2)◇X2) := (c_0_3 ((((X1◇(X1◇X1))◇X2)◇X2)) ((X1◇(X1◇X1))) X3).symm
 have c_0_97 : ∀ (X1 X2 X3 : G), ((X1◇(X1◇X1))◇((((X1◇(X1◇(X1◇X1)))◇(X1◇((X1◇X2)◇X2)))◇X3)◇X3)) = X1 := by
  intro X1 X2 X3
  calc ((X1◇(X1◇X1))◇((((X1◇(X1◇(X1◇X1)))◇(X1◇((X1◇X2)◇X2)))◇X3)◇X3))
   _ = ((X1◇(X1◇X1))◇((((((X1◇(X1◇(X1◇X1)))◇X1)◇(X1◇((X1◇X2)◇X2)))◇(X1◇((X1◇X2)◇X2)))◇X3)◇X3)) := congrArg ((X1◇(X1◇X1))◇·) (congrArg (·◇X3) (congrArg (·◇X3) (congrArg (·◇(X1◇((X1◇X2)◇X2))) ((c_0_71 X1 X2).symm))))
   _ = X1 := c_0_73 X1 X1 ((X1◇((X1◇X2)◇X2))) X3
 have c_0_98 : ∀ (X1 : G), (X1◇(X1◇X1)) = (X1◇X1) := by
  intro X1
  clear h c_0_3 c_0_4 c_0_5 c_0_6x c_0_6 c_0_7 c_0_8 c_0_9 c_0_10 c_0_11 c_0_12 c_0_13 c_0_14 c_0_15 c_0_16 c_0_17x c_0_17 c_0_18 c_0_19 c_0_20x c_0_20 c_0_21 c_0_22
  clear c_0_23 c_0_24 c_0_25 c_0_26 c_0_27 c_0_28 c_0_29 c_0_30 c_0_31 c_0_32 c_0_33 c_0_34 c_0_35 c_0_36 c_0_37x c_0_37 c_0_38 c_0_39 c_0_40 c_0_41 c_0_42 c_0_43 c_0_44 c_0_45
  clear c_0_46 c_0_47 c_0_48 c_0_49 c_0_50 c_0_51 c_0_52 c_0_53 c_0_54x c_0_54 c_0_55 c_0_56 c_0_57 c_0_58 c_0_59 c_0_60 c_0_61 c_0_62x c_0_62 c_0_63 c_0_64 c_0_65 c_0_66 c_0_67x
  clear c_0_67 c_0_68 c_0_69 c_0_70 c_0_71 c_0_72 c_0_73 c_0_74x c_0_74 c_0_75 c_0_76 c_0_77 c_0_78 c_0_79 c_0_80 c_0_81x c_0_81 c_0_82x c_0_82 c_0_84 c_0_85 c_0_86 c_0_87 c_0_89x
  clear c_0_89 c_0_90 c_0_91 c_0_92 c_0_95 c_0_96 c_0_97
  grind
 have c_0_99 : ∀ (X1 : G), (X1◇(X1◇(X1◇X1))) = (X1◇(X1◇X1)) := by
  intro X1
  calc (X1◇(X1◇(X1◇X1)))
   _ = (X1◇(((X1◇(X1◇X1))◇((X1◇(X1◇X1))◇X1))◇X1)) := congrArg (X1◇·) ((c_0_89 ((X1◇(X1◇X1))) X1).symm)
   _ = (X1◇(((X1◇(X1◇X1))◇X1)◇X1)) := congrArg (X1◇·) (congrArg (·◇X1) (congrArg ((X1◇(X1◇X1))◇·) (c_0_89 X1 X1)))
   _ = (X1◇(X1◇X1)) := congrArg (X1◇·) (congrArg (·◇X1) (((c_0_89 X1 X1).symm).symm))
 have c_0_100 : ∀ (X1 X2 X3 X4 : G), ((((X1◇(X1◇X1))◇X2)◇X2)◇(((((X1◇(X1◇X1))◇X3)◇X3)◇X4)◇X4)) = ((((X1◇(X1◇X1))◇X2)◇X2)◇(X1◇X1)) := by
  intro X1 X2 X3 X4
  clear h c_0_4 c_0_5 c_0_6x c_0_6 c_0_7 c_0_8 c_0_9 c_0_10 c_0_11 c_0_12 c_0_13 c_0_14 c_0_15 c_0_16 c_0_17x c_0_17 c_0_18 c_0_19 c_0_20x c_0_20 c_0_21 c_0_22 c_0_23
  clear c_0_24 c_0_25 c_0_26 c_0_27 c_0_28 c_0_29 c_0_30 c_0_31 c_0_32 c_0_33 c_0_34 c_0_35 c_0_36 c_0_37x c_0_37 c_0_38 c_0_39 c_0_40 c_0_41 c_0_42 c_0_43 c_0_44 c_0_45 c_0_46
  clear c_0_47 c_0_48 c_0_49 c_0_50 c_0_51 c_0_52 c_0_53 c_0_54x c_0_54 c_0_55 c_0_56 c_0_57 c_0_58 c_0_59 c_0_60 c_0_61 c_0_62x c_0_62 c_0_63 c_0_64 c_0_65 c_0_66 c_0_67x c_0_67
  clear c_0_68 c_0_69 c_0_70 c_0_71 c_0_72 c_0_73 c_0_74x c_0_74 c_0_75 c_0_76 c_0_77 c_0_78 c_0_79 c_0_80 c_0_81x c_0_81 c_0_82x c_0_82 c_0_83 c_0_84 c_0_85 c_0_86 c_0_87 c_0_88
  clear c_0_89x c_0_89 c_0_90 c_0_91 c_0_92 c_0_93 c_0_94 c_0_95 c_0_97 c_0_98 c_0_99
  let A : G := (((X1◇(X1◇X1))◇X2)◇X2)
  let B : G := (((X1◇(X1◇X1))◇X3)◇X3)
  let C : G := X1◇X1
  have haa : (A◇C)◇A = A := by
   have strict_rw_15 := (c_0_96 X1 X2 X2)
   change (A◇C)◇A = A at strict_rw_15
   exact strict_rw_15
  have hab : (A◇C)◇B = A := by
   have strict_rw_16 := (c_0_96 X1 X2 X3)
   change (A◇C)◇B = A at strict_rw_16
   exact strict_rw_16
  calc A◇((B◇X4)◇X4)
   _ = ((A◇C)◇A)◇((B◇X4)◇X4) :=
    congrArg (·◇((B◇X4)◇X4)) haa.symm
   _ = ((A◇C)◇((A◇C)◇B))◇((B◇X4)◇X4) :=
    congrArg (·◇((B◇X4)◇X4))
     (congrArg ((A◇C)◇·) hab.symm)
   _ = A◇C := (c_0_3 (A◇C) B X4).symm
   _ = ((((X1◇(X1◇X1))◇X2)◇X2)◇(X1◇X1)) := by
    rfl
 have c_0_101 : ∀ (X1 esk1_0 : G), ((X1◇((X1◇(X1◇X1))◇(((X1◇(X1◇X1))◇esk1_0)◇esk1_0)))◇X1) = X1 := by
  intro X1 esk1_0
  clear h c_0_3 c_0_4 c_0_5 c_0_6x c_0_6 c_0_7 c_0_8 c_0_9 c_0_10 c_0_11 c_0_12 c_0_13 c_0_14 c_0_15 c_0_16 c_0_17x c_0_17 c_0_18 c_0_19 c_0_20x c_0_20 c_0_21 c_0_22
  clear c_0_23 c_0_24 c_0_25 c_0_26 c_0_28 c_0_29 c_0_30 c_0_31 c_0_32 c_0_33 c_0_34 c_0_36 c_0_37x c_0_37 c_0_38 c_0_39 c_0_40 c_0_41 c_0_42 c_0_43 c_0_44 c_0_45 c_0_46 c_0_47
  clear c_0_48 c_0_49 c_0_50 c_0_51 c_0_52 c_0_53 c_0_54x c_0_54 c_0_55 c_0_56 c_0_57 c_0_58 c_0_59 c_0_60 c_0_61 c_0_62x c_0_62 c_0_63 c_0_64 c_0_65 c_0_66 c_0_67x c_0_67 c_0_68
  clear c_0_69 c_0_70 c_0_71 c_0_72 c_0_73 c_0_74x c_0_74 c_0_75 c_0_76 c_0_77 c_0_78 c_0_79 c_0_80 c_0_81x c_0_81 c_0_82x c_0_82 c_0_83 c_0_84 c_0_85 c_0_86 c_0_87 c_0_88 c_0_89x
  clear c_0_89 c_0_90 c_0_91 c_0_92 c_0_93 c_0_94 c_0_95 c_0_96 c_0_97 c_0_98 c_0_99 c_0_100
  grind
 have c_0_102 : ∀ (X1 X2 : G), ((((X1◇X1)◇X2)◇X2)◇((((X1◇X1)◇X2)◇X2)◇(X1◇X1))) = ((((X1◇X1)◇X2)◇X2)◇(X1◇X1)) := by
  intro X1 X2
  calc ((((X1◇X1)◇X2)◇X2)◇((((X1◇X1)◇X2)◇X2)◇(X1◇X1)))
   _ = ((((((X1◇X1)◇X2)◇X2)◇((((X1◇X1)◇X2)◇X2)◇(X1◇X1)))◇(((X1◇X1)◇X2)◇X2))◇(X1◇X1)) := (c_0_5 ((((X1◇X1)◇X2)◇X2)) X1).symm
   _ = ((((X1◇X1)◇X2)◇X2)◇(X1◇X1)) := congrArg (·◇(X1◇X1)) ((c_0_3 ((((X1◇X1)◇X2)◇X2)) ((X1◇X1)) X2).symm)
 have c_0_103x : ∀ (X0 X1 X2 : G), ((X0◇X0)◇(X0◇X0)) = ((((X0◇X0)◇(X0◇X0))◇(X0◇X0))◇(((((X0◇X0)◇X1)◇X1)◇X2)◇X2)) := by
  intro X0 X1 X2
  calc ((X0◇X0)◇(X0◇X0))
   _ = ((((X0◇X0)◇(X0◇X0))◇(((X0◇X0)◇(X0◇X0))◇(((X0◇X0)◇X1)◇X1)))◇(((((X0◇X0)◇X1)◇X1)◇X2)◇X2)) := c_0_3 (((X0◇X0)◇(X0◇X0))) ((((X0◇X0)◇X1)◇X1)) X2
   _ = ((((X0◇X0)◇(X0◇X0))◇(X0◇X0))◇(((((X0◇X0)◇X1)◇X1)◇X2)◇X2)) := congrArg (·◇(((((X0◇X0)◇X1)◇X1)◇X2)◇X2)) (congrArg (((X0◇X0)◇(X0◇X0))◇·) (c_0_90 X0 X1))
 have c_0_103 : ∀ (X1 X2 X3 : G), ((X1◇X1)◇(((((X1◇X1)◇X2)◇X2)◇X3)◇X3)) = ((X1◇X1)◇(X1◇X1)) := by
  intro X1 X2 X3
  have strict_rw_17 := ((c_0_103x X1 X2 X3).symm)
  rw [c_0_52] at strict_rw_17
  exact strict_rw_17
 have c_0_104 : ∀ (X1 : G), ((X1◇X1)◇(X1◇X1)) = X1 := by
  intro X1
  clear h c_0_3 c_0_4 c_0_5 c_0_6x c_0_6 c_0_7 c_0_8 c_0_9 c_0_11 c_0_12 c_0_13 c_0_14 c_0_15 c_0_16 c_0_17x c_0_17 c_0_18 c_0_19 c_0_20x c_0_20 c_0_21 c_0_22 c_0_23
  clear c_0_24 c_0_25 c_0_26 c_0_27 c_0_28 c_0_29 c_0_30 c_0_31 c_0_32 c_0_33 c_0_34 c_0_35 c_0_36 c_0_37x c_0_37 c_0_38 c_0_39 c_0_40 c_0_41 c_0_42 c_0_43 c_0_44 c_0_45 c_0_46
  clear c_0_47 c_0_48 c_0_49 c_0_50 c_0_51 c_0_52 c_0_53 c_0_54x c_0_54 c_0_55 c_0_56 c_0_57 c_0_58 c_0_59 c_0_60 c_0_61 c_0_62x c_0_62 c_0_63 c_0_64 c_0_65 c_0_66 c_0_67x c_0_67
  clear c_0_68 c_0_69 c_0_70 c_0_71 c_0_72 c_0_73 c_0_74x c_0_74 c_0_75 c_0_76 c_0_77 c_0_78 c_0_79 c_0_80 c_0_81x c_0_81 c_0_82x c_0_82 c_0_83 c_0_84 c_0_85 c_0_86 c_0_87 c_0_89x
  clear c_0_89 c_0_90 c_0_91 c_0_92 c_0_93 c_0_94 c_0_95 c_0_96 c_0_100 c_0_101 c_0_102 c_0_103x c_0_103
  grind
 have c_0_105 : ∀ (X1 X2 : G), ((X1◇X1)◇((X1◇X2)◇X2)) = X1 := by
  intro X1 X2
  calc ((X1◇X1)◇((X1◇X2)◇X2))
   _ = ((X1◇((X1◇X1)◇X1))◇((X1◇X2)◇X2)) := congrArg (·◇((X1◇X2)◇X2)) ((c_0_88 X1 X1).symm)
   _ = ((X1◇((X1◇X1)◇X1))◇((((X1◇(X1◇X1))◇X1)◇X2)◇X2)) := congrArg ((X1◇((X1◇X1)◇X1))◇·) (congrArg (·◇X2) (congrArg (·◇X2) ((c_0_89 X1 X1).symm)))
   _ = X1 := ((c_0_86 X1 X1 X2).symm).symm
 have c_0_106 : ∀ (X1 : G), ((X1◇X1)◇X1) = X1 := by
  intro X1
  calc ((X1◇X1)◇X1)
   _ = ((X1◇((X1◇((X1◇(X1◇(X1◇X1)))◇(X1◇(X1◇X1))))◇((X1◇(X1◇(X1◇X1)))◇(X1◇(X1◇X1)))))◇X1) := congrArg (·◇X1) (congrArg (X1◇·) ((c_0_84 X1 ((X1◇(X1◇X1)))).symm))
   _ = X1 := c_0_19 X1 (((X1◇(X1◇(X1◇X1)))◇(X1◇(X1◇X1))))
 have c_0_107x : ∀ (X0 X1 X2 X3 X4 : G), ((((X0◇(X0◇X0))◇X1)◇X1)◇(((((X0◇(X0◇X0))◇((X0◇(X0◇X0))◇(((X0◇(X0◇X0))◇X2)◇X2)))◇((((X0◇(X0◇X0))◇((X0◇(X0◇X0))◇(((X0◇(X0◇X0))◇X2)◇X2)))◇X3)◇X3))◇X4)◇X4)) = ((((X0◇(X0◇X0))◇X1)◇X1)◇(X0◇X0)) := by
  intro X0 X1 X2 X3 X4
  calc ((((X0◇(X0◇X0))◇X1)◇X1)◇(((((X0◇(X0◇X0))◇((X0◇(X0◇X0))◇(((X0◇(X0◇X0))◇X2)◇X2)))◇((((X0◇(X0◇X0))◇((X0◇(X0◇X0))◇(((X0◇(X0◇X0))◇X2)◇X2)))◇X3)◇X3))◇X4)◇X4))
   _ = ((((X0◇(X0◇X0))◇X1)◇X1)◇(((((X0◇(X0◇X0))◇((((X0◇(X0◇X0))◇((X0◇(X0◇X0))◇(((X0◇(X0◇X0))◇X2)◇X2)))◇X3)◇X3))◇((((X0◇(X0◇X0))◇((X0◇(X0◇X0))◇(((X0◇(X0◇X0))◇X2)◇X2)))◇X3)◇X3))◇X4)◇X4)) := congrArg ((((X0◇(X0◇X0))◇X1)◇X1)◇·) (congrArg (·◇X4) (congrArg (·◇X4) (congrArg (·◇((((X0◇(X0◇X0))◇((X0◇(X0◇X0))◇(((X0◇(X0◇X0))◇X2)◇X2)))◇X3)◇X3)) ((c_0_33 ((X0◇(X0◇X0))) X2 X3).symm))))
   _ = ((((X0◇(X0◇X0))◇X1)◇X1)◇(X0◇X0)) := c_0_100 X0 X1 (((((X0◇(X0◇X0))◇((X0◇(X0◇X0))◇(((X0◇(X0◇X0))◇X2)◇X2)))◇X3)◇X3)) X4
 have c_0_107 : ∀ (X1 X2 X3 X4 : G), ((((X1◇(X1◇X1))◇X2)◇X2)◇(((X1◇((X1◇X3)◇X3))◇X4)◇X4)) = ((((X1◇(X1◇X1))◇X2)◇X2)◇(X1◇X1)) := by
  intro X1 X2 X3 X4
  have strict_rw_18 := (c_0_107x X1 X2 X1 X3 X4)
  rw [c_0_35] at strict_rw_18
  exact strict_rw_18
 have c_0_108 : ∀ (X1 X2 : G), ((X1◇((X1◇(X1◇X1))◇(((X1◇(X1◇X1))◇X2)◇X2)))◇X1) = X1 := by
  intro X1 X2
  calc ((X1◇((X1◇(X1◇X1))◇(((X1◇(X1◇X1))◇X2)◇X2)))◇X1)
   _ = ((X1◇((X1◇(X1◇X1))◇(((X1◇(X1◇X1))◇X1)◇X1)))◇X1) := congrArg (·◇X1) (congrArg (X1◇·) ((c_0_31 ((X1◇(X1◇X1))) X1 X2).symm))
   _ = X1 := c_0_101 X1 X1
 have c_0_109x : ∀ (X0 X1 X2 : G), (((((X0◇X0)◇X1)◇X1)◇(X0◇X0))◇(((X0◇X0)◇((X0◇X0)◇(X0◇X0)))◇((((X0◇X0)◇(X0◇X0))◇X2)◇X2))) = (((X0◇X0)◇X1)◇X1) := by
  intro X0 X1 X2
  calc (((((X0◇X0)◇X1)◇X1)◇(X0◇X0))◇(((X0◇X0)◇((X0◇X0)◇(X0◇X0)))◇((((X0◇X0)◇(X0◇X0))◇X2)◇X2)))
   _ = (((((X0◇X0)◇X1)◇X1)◇((((X0◇X0)◇X1)◇X1)◇(X0◇X0)))◇(((X0◇X0)◇((X0◇X0)◇(X0◇X0)))◇((((X0◇X0)◇(X0◇X0))◇X2)◇X2))) := congrArg (·◇(((X0◇X0)◇((X0◇X0)◇(X0◇X0)))◇((((X0◇X0)◇(X0◇X0))◇X2)◇X2))) ((c_0_102 X0 X1).symm)
   _ = (((X0◇X0)◇X1)◇X1) := c_0_13 ((((X0◇X0)◇X1)◇X1)) ((X0◇X0)) X2
 have c_0_109 : ∀ (X1 X2 : G), (((((X1◇X1)◇X2)◇X2)◇(X1◇X1))◇(X1◇X1)) = (((X1◇X1)◇X2)◇X2) := by
  intro X1 X2
  have strict_rw_19 := (c_0_109x X1 X2 X1)
  rw [c_0_48, c_0_56, c_0_57] at strict_rw_19
  exact strict_rw_19
 have c_0_110 : ∀ (X1 X2 X3 : G), ((X1◇X1)◇(((((X1◇X1)◇X2)◇X2)◇X3)◇X3)) = X1 := by
  intro X1 X2 X3
  calc ((X1◇X1)◇(((((X1◇X1)◇X2)◇X2)◇X3)◇X3))
   _ = ((X1◇X1)◇(X1◇X1)) := ((c_0_103 X1 X2 X3).symm).symm
   _ = X1 := c_0_104 X1
 have c_0_111 : ∀ (X1 X2 : G), ((X1◇(X1◇X2))◇(X1◇(X1◇X2))) = ((X1◇(X1◇X2))◇(X1◇X2)) := by
  intro X1 X2
  calc ((X1◇(X1◇X2))◇(X1◇(X1◇X2)))
   _ = ((X1◇(X1◇X2))◇(((X1◇(X1◇X2))◇X2)◇X2)) := (c_0_88 ((X1◇(X1◇X2))) X2).symm
   _ = ((X1◇(X1◇X2))◇(X1◇X2)) := congrArg ((X1◇(X1◇X2))◇·) (congrArg (·◇X2) (c_0_89 X1 X2))
 have c_0_112x : ∀ (X0 X1 X2 : G), (X0◇X0) = (((X0◇X0)◇X0)◇((((X0◇X1)◇X1)◇X2)◇X2)) := by
  intro X0 X1 X2
  calc (X0◇X0)
   _ = (((X0◇X0)◇((X0◇X0)◇((X0◇X1)◇X1)))◇((((X0◇X1)◇X1)◇X2)◇X2)) := c_0_3 ((X0◇X0)) (((X0◇X1)◇X1)) X2
   _ = (((X0◇X0)◇X0)◇((((X0◇X1)◇X1)◇X2)◇X2)) := congrArg (·◇((((X0◇X1)◇X1)◇X2)◇X2)) (congrArg ((X0◇X0)◇·) (c_0_105 X0 X1))
 have c_0_112 : ∀ (X1 X2 X3 : G), (X1◇((((X1◇X2)◇X2)◇X3)◇X3)) = (X1◇X1) := by
  intro X1 X2 X3
  have strict_rw_20 := ((c_0_112x X1 X2 X3).symm)
  rw [c_0_106] at strict_rw_20
  exact strict_rw_20
 have c_0_113 : ∀ (X1 X2 X3 : G), (((X1◇X2)◇X2)◇((X1◇X3)◇X3)) = (((X1◇X2)◇X2)◇X1) := by
  intro X1 X2 X3
  clear h c_0_3 c_0_4 c_0_5 c_0_6x c_0_6 c_0_7 c_0_8 c_0_9 c_0_10 c_0_11 c_0_12 c_0_13 c_0_14 c_0_15 c_0_16 c_0_17x c_0_17 c_0_18 c_0_19 c_0_20x c_0_20 c_0_21 c_0_22
  clear c_0_23 c_0_24 c_0_25 c_0_26 c_0_27 c_0_28 c_0_29 c_0_30 c_0_31 c_0_32 c_0_33 c_0_34 c_0_35 c_0_36 c_0_37x c_0_37 c_0_38 c_0_39 c_0_40 c_0_41 c_0_42 c_0_43 c_0_44 c_0_45
  clear c_0_46 c_0_47 c_0_48 c_0_49 c_0_50 c_0_51 c_0_52 c_0_53 c_0_54x c_0_54 c_0_55 c_0_56 c_0_57 c_0_58 c_0_59 c_0_60 c_0_61 c_0_62x c_0_62 c_0_63 c_0_64 c_0_65 c_0_66 c_0_67x
  clear c_0_67 c_0_68 c_0_69 c_0_70 c_0_71 c_0_72 c_0_73 c_0_74x c_0_74 c_0_75 c_0_76 c_0_77 c_0_78 c_0_79 c_0_80 c_0_81x c_0_81 c_0_82x c_0_82 c_0_83 c_0_84 c_0_85 c_0_86 c_0_87
  clear c_0_88 c_0_89x c_0_89 c_0_90 c_0_91 c_0_92 c_0_93 c_0_94 c_0_95 c_0_96 c_0_97 c_0_99 c_0_100 c_0_101 c_0_102 c_0_103x c_0_103 c_0_105 c_0_106 c_0_107x c_0_108 c_0_109x c_0_109 c_0_110
  clear c_0_111 c_0_112x c_0_112
  let U : G := X1◇X1
  have hx := c_0_107 U X2 X1 X3
  rw [c_0_98] at hx
  have huu : U◇U = X1 := by
   have strict_rw_21 := (c_0_104 X1)
   exact strict_rw_21
  have hux : U◇X1 = X1 := by
   calc U◇X1
    _ = U◇(U◇U) := congrArg (U◇·) huu.symm
    _ = U◇U := c_0_98 U
    _ = X1 := huu
  have hk : U◇((U◇X1)◇X1) = X1 := by
   calc U◇((U◇X1)◇X1)
    _ = U◇(X1◇X1) := congrArg (U◇·) (congrArg (·◇X1) hux)
    _ = U◇U := by rfl
    _ = X1 := huu
  have strict_rw_22 := hx
  rw [hk, huu] at strict_rw_22
  exact strict_rw_22
 have c_0_114 : ∀ (X1 X2 esk1_0 : G), (X1◇((X1◇(X1◇X1))◇(((X1◇(X1◇X1))◇X2)◇X2))) = (X1◇((X1◇esk1_0)◇esk1_0)) := by
  intro X1 X2 esk1_0
  grind
 have c_0_115 : ∀ (X1 X2 : G), ((((X1◇X2)◇X2)◇X1)◇X1) = ((X1◇X2)◇X2) := by
  intro X1 X2
  calc ((((X1◇X2)◇X2)◇X1)◇X1)
   _ = ((((((X1◇X1)◇(X1◇X1))◇X2)◇X2)◇X1)◇X1) := congrArg (·◇X1) (congrArg (·◇X1) (congrArg (·◇X2) (congrArg (·◇X2) ((c_0_104 X1).symm))))
   _ = ((((((X1◇X1)◇(X1◇X1))◇X2)◇X2)◇((X1◇X1)◇(X1◇X1)))◇X1) := congrArg (·◇X1) (congrArg (((((X1◇X1)◇(X1◇X1))◇X2)◇X2)◇·) ((c_0_104 X1).symm))
   _ = ((((((X1◇X1)◇(X1◇X1))◇X2)◇X2)◇((X1◇X1)◇(X1◇X1)))◇((X1◇X1)◇(X1◇X1))) := congrArg ((((((X1◇X1)◇(X1◇X1))◇X2)◇X2)◇((X1◇X1)◇(X1◇X1)))◇·) ((c_0_104 X1).symm)
   _ = ((((X1◇X1)◇(X1◇X1))◇X2)◇X2) := ((c_0_109 ((X1◇X1)) X2).symm).symm
   _ = ((X1◇X2)◇X2) := congrArg (·◇X2) (congrArg (·◇X2) (((c_0_104 X1).symm).symm))
 have c_0_116 : ∀ (X1 X2 : G), (((X1◇(X1◇X2))◇(X1◇X2))◇X1) = (X1◇(X1◇X2)) := by
  intro X1 X2
  grind
 have c_0_117 : ∀ (X1 esk1_0 : G), ((X1◇(X1◇((X1◇esk1_0)◇esk1_0)))◇((X1◇(X1◇X1))◇(X1◇(X1◇X1)))) = X1 := by
  intro X1 esk1_0
  calc ((X1◇(X1◇((X1◇esk1_0)◇esk1_0)))◇((X1◇(X1◇X1))◇(X1◇(X1◇X1))))
   _ = ((X1◇(X1◇((X1◇(X1◇X1))◇(((X1◇(X1◇X1))◇X1)◇X1))))◇((X1◇(X1◇X1))◇(X1◇(X1◇X1)))) := congrArg (·◇((X1◇(X1◇X1))◇(X1◇(X1◇X1)))) (congrArg (X1◇·) ((c_0_114 X1 X1 esk1_0).symm))
   _ = X1 := c_0_12 X1 ((X1◇(X1◇X1))) X1
 have c_0_118 : ∀ (X1 X2 X3 esk1_0 : G), ((X1◇(X1◇X1))◇(((((X1◇(X1◇(X1◇X1)))◇X2)◇X2)◇X3)◇X3)) = ((X1◇(X1◇X1))◇(X1◇((X1◇esk1_0)◇esk1_0))) := by
  intro X1 X2 X3 esk1_0
  calc ((X1◇(X1◇X1))◇(((((X1◇(X1◇(X1◇X1)))◇X2)◇X2)◇X3)◇X3))
   _ = ((((X1◇(X1◇X1))◇(X1◇((X1◇X1)◇X1)))◇(X1◇(X1◇X1)))◇(((((X1◇(X1◇(X1◇X1)))◇X2)◇X2)◇X3)◇X3)) := congrArg (·◇(((((X1◇(X1◇(X1◇X1)))◇X2)◇X2)◇X3)◇X3)) ((c_0_21 X1 X1 X1).symm)
   _ = ((((X1◇(X1◇X1))◇((X1◇(X1◇X1))◇(X1◇(X1◇(X1◇X1)))))◇(X1◇(X1◇X1)))◇(((((X1◇(X1◇(X1◇X1)))◇X2)◇X2)◇X3)◇X3)) := congrArg (·◇(((((X1◇(X1◇(X1◇X1)))◇X2)◇X2)◇X3)◇X3)) (congrArg (·◇(X1◇(X1◇X1))) ((c_0_78 X1 X1).symm))
   _ = ((X1◇(X1◇X1))◇((X1◇(X1◇X1))◇(X1◇(X1◇(X1◇X1))))) := ((c_0_24 ((X1◇(X1◇X1))) ((X1◇(X1◇(X1◇X1)))) X2 X3).symm).symm
   _ = ((X1◇(X1◇X1))◇(X1◇((X1◇esk1_0)◇esk1_0))) := ((c_0_78 X1 esk1_0).symm).symm
 have c_0_119 : ∀ (X1 X2 X3 X4 : G), ((X1◇(X1◇X2))◇((X2◇((X2◇X3)◇X3))◇(X2◇((X2◇(X2◇((X2◇X4)◇X4)))◇X2)))) = X1 := by
  intro X1 X2 X3 X4
  calc ((X1◇(X1◇X2))◇((X2◇((X2◇X3)◇X3))◇(X2◇((X2◇(X2◇((X2◇X4)◇X4)))◇X2))))
   _ = ((X1◇(X1◇X2))◇((X2◇(X2◇((X2◇(X2◇((X2◇X4)◇X4)))◇X2)))◇(X2◇((X2◇(X2◇((X2◇X4)◇X4)))◇X2)))) := congrArg ((X1◇(X1◇X2))◇·) (congrArg (·◇(X2◇((X2◇(X2◇((X2◇X4)◇X4)))◇X2))) (((c_0_72 X2 X3 X4).symm).symm))
   _ = X1 := (c_0_3 X1 X2 ((X2◇((X2◇(X2◇((X2◇X4)◇X4)))◇X2)))).symm
 have c_0_120 : ∀ (X1 X2 : G), ((X1◇(X1◇X2))◇(X1◇X2)) = ((X1◇(X1◇X2))◇X1) := by
  intro X1 X2
  calc ((X1◇(X1◇X2))◇(X1◇X2))
   _ = ((((X1◇(X1◇X2))◇(X1◇X2))◇X1)◇X1) := (c_0_115 X1 ((X1◇X2))).symm
   _ = ((X1◇(X1◇X2))◇X1) := congrArg (·◇X1) (c_0_116 X1 X2)
 have c_0_121 : ∀ (X1 esk1_0 : G), (X1◇(X1◇((X1◇(X1◇X1))◇(X1◇(X1◇X1))))) = (X1◇(X1◇((X1◇esk1_0)◇esk1_0))) := by
  intro X1 esk1_0
  calc (X1◇(X1◇((X1◇(X1◇X1))◇(X1◇(X1◇X1)))))
   _ = (X1◇(((X1◇(X1◇((X1◇esk1_0)◇esk1_0)))◇((X1◇(X1◇X1))◇(X1◇(X1◇X1))))◇((X1◇(X1◇X1))◇(X1◇(X1◇X1))))) := congrArg (X1◇·) (congrArg (·◇((X1◇(X1◇X1))◇(X1◇(X1◇X1)))) ((c_0_117 X1 esk1_0).symm))
   _ = (X1◇(X1◇((X1◇esk1_0)◇esk1_0))) := c_0_33 X1 esk1_0 (((X1◇(X1◇X1))◇(X1◇(X1◇X1))))
 have c_0_122x : ∀ (X0 X1 X2 X3 X4 : G), (X0◇(X0◇X0)) = (((X0◇(X0◇X0))◇((X0◇(X0◇X0))◇(X0◇((X0◇X1)◇X1))))◇(((((((X0◇(X0◇(X0◇X0)))◇X2)◇X2)◇X3)◇X3)◇X4)◇X4)) := by
  intro X0 X1 X2 X3 X4
  calc (X0◇(X0◇X0))
   _ = (((X0◇(X0◇X0))◇((X0◇(X0◇X0))◇(((((X0◇(X0◇(X0◇X0)))◇X2)◇X2)◇X3)◇X3)))◇(((((((X0◇(X0◇(X0◇X0)))◇X2)◇X2)◇X3)◇X3)◇X4)◇X4)) := c_0_3 ((X0◇(X0◇X0))) ((((((X0◇(X0◇(X0◇X0)))◇X2)◇X2)◇X3)◇X3)) X4
   _ = (((X0◇(X0◇X0))◇((X0◇(X0◇X0))◇(X0◇((X0◇X1)◇X1))))◇(((((((X0◇(X0◇(X0◇X0)))◇X2)◇X2)◇X3)◇X3)◇X4)◇X4)) := congrArg (·◇(((((((X0◇(X0◇(X0◇X0)))◇X2)◇X2)◇X3)◇X3)◇X4)◇X4)) (congrArg ((X0◇(X0◇X0))◇·) (c_0_118 X0 X2 X3 X1))
 have c_0_122 : ∀ (X1 X2 X3 X4 : G), (X1◇(((((((X1◇(X1◇(X1◇X1)))◇X2)◇X2)◇X3)◇X3)◇X4)◇X4)) = (X1◇(X1◇X1)) := by
  intro X1 X2 X3 X4
  have strict_rw_23 := ((c_0_122x X1 X1 X2 X3 X4).symm)
  rw [c_0_79] at strict_rw_23
  exact strict_rw_23
 have c_0_123x : ∀ (X0 X1 X2 X3 X4 : G), ((X0◇(X0◇X1))◇(((X0◇((X1◇((X1◇X2)◇X2))◇(X1◇((X1◇(X1◇((X1◇X3)◇X3)))◇X1))))◇X4)◇X4)) = ((X0◇(X0◇X1))◇(X0◇(X0◇X1))) := by
  intro X0 X1 X2 X3 X4
  calc ((X0◇(X0◇X1))◇(((X0◇((X1◇((X1◇X2)◇X2))◇(X1◇((X1◇(X1◇((X1◇X3)◇X3)))◇X1))))◇X4)◇X4))
   _ = ((X0◇(X0◇X1))◇(((((X0◇(X0◇X1))◇((X1◇((X1◇X2)◇X2))◇(X1◇((X1◇(X1◇((X1◇X3)◇X3)))◇X1))))◇((X1◇((X1◇X2)◇X2))◇(X1◇((X1◇(X1◇((X1◇X3)◇X3)))◇X1))))◇X4)◇X4)) := congrArg ((X0◇(X0◇X1))◇·) (congrArg (·◇X4) (congrArg (·◇X4) (congrArg (·◇((X1◇((X1◇X2)◇X2))◇(X1◇((X1◇(X1◇((X1◇X3)◇X3)))◇X1)))) ((c_0_119 X0 X1 X2 X3).symm))))
   _ = ((X0◇(X0◇X1))◇(X0◇(X0◇X1))) := c_0_112 ((X0◇(X0◇X1))) (((X1◇((X1◇X2)◇X2))◇(X1◇((X1◇(X1◇((X1◇X3)◇X3)))◇X1)))) X4
 have c_0_123 : ∀ (X1 X2 X3 : G), ((X1◇(X1◇X2))◇(((X1◇X2)◇X3)◇X3)) = ((X1◇(X1◇X2))◇X1) := by
  intro X1 X2 X3
  have strict_rw_24 := (c_0_123x X1 X2 X1 X1 X3)
  rw [c_0_88, c_0_98, c_0_106, c_0_104, c_0_111, c_0_120] at strict_rw_24
  exact strict_rw_24
 have c_0_124 : ∀ (X1 esk1_0 X2 : G), (X1◇(X1◇((((X1◇(X1◇((X1◇esk1_0)◇esk1_0)))◇X1)◇X2)◇X2))) = (X1◇(X1◇X1)) := by
  intro X1 esk1_0 X2
  calc (X1◇(X1◇((((X1◇(X1◇((X1◇esk1_0)◇esk1_0)))◇X1)◇X2)◇X2)))
   _ = (X1◇(X1◇((((X1◇(X1◇((X1◇(X1◇X1))◇(X1◇(X1◇X1)))))◇X1)◇X2)◇X2))) := congrArg (X1◇·) (congrArg (X1◇·) (congrArg (·◇X2) (congrArg (·◇X2) (congrArg (·◇X1) ((c_0_121 X1 esk1_0).symm)))))
   _ = (X1◇(X1◇X1)) := c_0_41 X1 ((X1◇(X1◇X1))) X2
 have c_0_125 : ∀ (X1 X2 : G), ((X1◇(X1◇((X2◇(X2◇(X2◇X2)))◇((X2◇(X2◇(X2◇X2)))◇(X2◇(X2◇X2))))))◇X2) = X1 := by
  intro X1 X2
  grind
 have c_0_126 : ∀ (X1 X2 : G), ((X1◇(X1◇(X1◇X2)))◇X1) = X1 := by
  intro X1 X2
  calc ((X1◇(X1◇(X1◇X2)))◇X1)
   _ = ((X1◇(X1◇(X1◇X2)))◇(((X1◇(X1◇X2))◇X2)◇X2)) := (c_0_123 X1 ((X1◇X2)) X2).symm
   _ = ((X1◇(X1◇(((X1◇(X1◇X2))◇X2)◇X2)))◇(((X1◇(X1◇X2))◇X2)◇X2)) := congrArg (·◇(((X1◇(X1◇X2))◇X2)◇X2)) (congrArg (X1◇·) (congrArg (X1◇·) (congrArg (·◇X2) ((c_0_89 X1 X2).symm))))
   _ = X1 := c_0_89 X1 ((((X1◇(X1◇X2))◇X2)◇X2))
 have c_0_127 : ∀ (X1 X2 X3 : G), (X1◇(X1◇((((X1◇(X1◇((X1◇X2)◇X2)))◇X1)◇X3)◇X3))) = (X1◇(X1◇X1)) := by
  intro X1 X2 X3
  calc (X1◇(X1◇((((X1◇(X1◇((X1◇X2)◇X2)))◇X1)◇X3)◇X3)))
   _ = (X1◇(X1◇((((X1◇(X1◇((X1◇X1)◇X1)))◇X1)◇X3)◇X3))) := congrArg (X1◇·) (congrArg (X1◇·) (congrArg (·◇X3) (congrArg (·◇X3) (congrArg (·◇X1) (congrArg (X1◇·) ((c_0_31 X1 X1 X2).symm))))))
   _ = (X1◇(X1◇X1)) := c_0_124 X1 X1 X3
 have c_0_129 : ∀ (X1 X2 X3 X4 X5 : G), ((X1◇(X1◇(X2◇(X2◇X3))))◇(X2◇((X3◇((X3◇X4)◇X4))◇((X3◇X5)◇X5)))) = X1 := by
  intro X1 X2 X3 X4 X5
  calc ((X1◇(X1◇(X2◇(X2◇X3))))◇(X2◇((X3◇((X3◇X4)◇X4))◇((X3◇X5)◇X5))))
   _ = ((X1◇(X1◇(X2◇(X2◇X3))))◇(X2◇((X3◇((X3◇X5)◇X5))◇((X3◇X5)◇X5)))) := congrArg ((X1◇(X1◇(X2◇(X2◇X3))))◇·) (congrArg (X2◇·) (congrArg (·◇((X3◇X5)◇X5)) ((c_0_31 X3 X5 X4).symm)))
   _ = X1 := c_0_29 X1 X2 X3 (((X3◇X5)◇X5))
 have c_0_130 : ∀ (X1 X2 : G), (((X1◇(X1◇X2))◇X1)◇X2) = (X1◇(X1◇X2)) := by
  intro X1 X2
  calc (((X1◇(X1◇X2))◇X1)◇X2)
   _ = (((X1◇(X1◇X2))◇((X1◇(X1◇X2))◇X2))◇X2) := congrArg (·◇X2) (congrArg ((X1◇(X1◇X2))◇·) ((c_0_89 X1 X2).symm))
   _ = (X1◇(X1◇X2)) := c_0_89 ((X1◇(X1◇X2))) X2
 have c_0_131 : ∀ (X1 X2 : G), (X1◇(X1◇(X1◇X2))) = (X1◇X1) := by
  intro X1 X2
  clear h c_0_3 c_0_4 c_0_5 c_0_6x c_0_6 c_0_7 c_0_8 c_0_9 c_0_10 c_0_11 c_0_12 c_0_13 c_0_14 c_0_15 c_0_16 c_0_17x c_0_17 c_0_18 c_0_19 c_0_20x c_0_20 c_0_21 c_0_22
  clear c_0_23 c_0_24 c_0_25 c_0_26 c_0_27 c_0_28 c_0_29 c_0_30 c_0_31 c_0_32 c_0_33 c_0_34 c_0_35 c_0_36 c_0_37x c_0_37 c_0_38 c_0_39 c_0_40 c_0_41 c_0_42 c_0_43 c_0_44 c_0_45
  clear c_0_46 c_0_47 c_0_48 c_0_49 c_0_50 c_0_51 c_0_52 c_0_53 c_0_54x c_0_54 c_0_55 c_0_56 c_0_57 c_0_58 c_0_59 c_0_60 c_0_61 c_0_62x c_0_62 c_0_63 c_0_64 c_0_65 c_0_66 c_0_67x
  clear c_0_67 c_0_68 c_0_69 c_0_70 c_0_71 c_0_72 c_0_73 c_0_74x c_0_74 c_0_75 c_0_76 c_0_77 c_0_78 c_0_79 c_0_80 c_0_81x c_0_81 c_0_82x c_0_82 c_0_83 c_0_84 c_0_85 c_0_86 c_0_87
  clear c_0_88 c_0_89x c_0_89 c_0_90 c_0_91 c_0_92 c_0_93 c_0_94 c_0_95 c_0_96 c_0_97 c_0_99 c_0_100 c_0_101 c_0_102 c_0_103x c_0_103 c_0_105 c_0_107x c_0_107 c_0_108 c_0_109x c_0_109 c_0_110
  clear c_0_111 c_0_112x c_0_112 c_0_113 c_0_114 c_0_115 c_0_116 c_0_117 c_0_118 c_0_119 c_0_120 c_0_121 c_0_122x c_0_122 c_0_123x c_0_123 c_0_124 c_0_127 c_0_129 c_0_130
  grind
 have c_0_132 : ∀ (X1 X2 X3 X4 : G), ((X1◇(X1◇X1))◇((((((X1◇(X1◇((X1◇X2)◇X2)))◇X1)◇X3)◇X3)◇X4)◇X4)) = X1 := by
  intro X1 X2 X3 X4
  calc ((X1◇(X1◇X1))◇((((((X1◇(X1◇((X1◇X2)◇X2)))◇X1)◇X3)◇X3)◇X4)◇X4))
   _ = ((X1◇(X1◇((((X1◇(X1◇((X1◇X2)◇X2)))◇X1)◇X3)◇X3)))◇((((((X1◇(X1◇((X1◇X2)◇X2)))◇X1)◇X3)◇X3)◇X4)◇X4)) := congrArg (·◇((((((X1◇(X1◇((X1◇X2)◇X2)))◇X1)◇X3)◇X3)◇X4)◇X4)) ((c_0_127 X1 X2 X3).symm)
   _ = X1 := (c_0_3 X1 (((((X1◇(X1◇((X1◇X2)◇X2)))◇X1)◇X3)◇X3)) X4).symm
 have c_0_134 : ∀ (X1 X2 X3 X4 X5 : G), (((X1◇(X1◇X2))◇X1)◇((X2◇((X2◇X3)◇X3))◇((((X2◇X4)◇X4)◇X5)◇X5))) = (X1◇(X1◇X2)) := by
  intro X1 X2 X3 X4 X5
  grind
 have c_0_135 : ∀ (X1 X2 : G), (X1◇(X1◇X2)) = (X1◇X1) := by
  intro X1 X2
  calc (X1◇(X1◇X2))
   _ = (((X1◇X1)◇X1)◇(X1◇X2)) := congrArg (·◇(X1◇X2)) ((c_0_106 X1).symm)
   _ = (((X1◇(X1◇(X1◇X2)))◇X1)◇(X1◇X2)) := congrArg (·◇(X1◇X2)) (congrArg (·◇X1) ((c_0_131 X1 X2).symm))
   _ = (X1◇(X1◇(X1◇X2))) := ((c_0_130 X1 ((X1◇X2))).symm).symm
   _ = (X1◇X1) := ((c_0_131 X1 X2).symm).symm
 have c_0_136 : ∀ (X1 X2 X3 : G), ((X1◇X1)◇((((X1◇X2)◇X2)◇X3)◇X3)) = X1 := by
  intro X1 X2 X3
  clear h c_0_3 c_0_4 c_0_5 c_0_6x c_0_6 c_0_7 c_0_8 c_0_9 c_0_10 c_0_11 c_0_12 c_0_13 c_0_14 c_0_15 c_0_16 c_0_17x c_0_17 c_0_18 c_0_19 c_0_20x c_0_20 c_0_21 c_0_22
  clear c_0_23 c_0_24 c_0_25 c_0_26 c_0_27 c_0_28 c_0_29 c_0_30 c_0_31 c_0_32 c_0_33 c_0_34 c_0_35 c_0_36 c_0_37x c_0_37 c_0_38 c_0_39 c_0_40 c_0_41 c_0_42 c_0_43 c_0_44 c_0_45
  clear c_0_46 c_0_47 c_0_48 c_0_49 c_0_50 c_0_51 c_0_52 c_0_53 c_0_54x c_0_54 c_0_55 c_0_56 c_0_57 c_0_58 c_0_59 c_0_60 c_0_61 c_0_62x c_0_62 c_0_63 c_0_64 c_0_65 c_0_66 c_0_67x
  clear c_0_67 c_0_68 c_0_69 c_0_70 c_0_71 c_0_72 c_0_73 c_0_74x c_0_74 c_0_75 c_0_76 c_0_77 c_0_78 c_0_79 c_0_80 c_0_81x c_0_81 c_0_82x c_0_82 c_0_83 c_0_84 c_0_85 c_0_86 c_0_87
  clear c_0_89x c_0_89 c_0_90 c_0_91 c_0_92 c_0_93 c_0_94 c_0_95 c_0_96 c_0_97 c_0_99 c_0_100 c_0_101 c_0_102 c_0_103x c_0_103 c_0_104 c_0_105 c_0_107x c_0_107 c_0_108 c_0_109x c_0_109 c_0_110
  clear c_0_111 c_0_112x c_0_112 c_0_113 c_0_114 c_0_115 c_0_116 c_0_117 c_0_118 c_0_119 c_0_120 c_0_121 c_0_122x c_0_122 c_0_123x c_0_123 c_0_124 c_0_125 c_0_126 c_0_127 c_0_129 c_0_130 c_0_131 c_0_134
  clear c_0_135
  grind
 have c_0_138 : ∀ (X1 X2 : G), (X1◇X2) = (X1◇X1) := by
  intro X1 X2
  grind
 calc x
  _ = (x◇(x◇x))◇((x◇x)◇x) := h x x x
  _ = (x◇(y◇z))◇((x◇x)◇x) := by
   apply congrArg (·◇((x◇x)◇x))
   calc x◇(x◇x)
    _ = x◇x := c_0_138 x (x◇x)
    _ = x◇(y◇z) := (c_0_138 x (y◇z)).symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_22268_to_22361 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_22268_to_22361
