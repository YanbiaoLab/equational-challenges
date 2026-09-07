-- Equation55122 → Equation55048
-- Recorded verdict: true
-- Premise: x ◇ (y ◇ y) = z ◇ ((x ◇ z) ◇ z)
-- Conclusion: x ◇ (y ◇ y) = x ◇ ((y ◇ x) ◇ x)
-- Original submission SHA-256: 5ee281483b7d63e9d17624266a53c2e5cc4e5598f28fdf1c97299680a9eb6d81
-- Aurora-accepted correction SHA-256: 46abab351f64c631c6a6350d1a78a174ada25fa145c2acd0fc000f78e33fdb32
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ y) = z ◇ ((x ◇ z) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ (y ◇ y) = x ◇ ((y ◇ x) ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Aurora-accepted corrected submission body
                   

namespace submission

section
                       

namespace Equation55122Kernel

class Law (G : Type) [Magma G] : Prop where
  source : ∀ (x y z : G), x ◇ (y ◇ y) = z ◇ ((x ◇ z) ◇ z)

variable {G : Type} [Magma G] [Law G]

                                         

set_option linter.unusedVariables false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000


theorem f7 : ∀ (X0 X1 X2 : G), (X0 ◇ (X1 ◇ X1)) = (X2 ◇ ((X0 ◇ X2) ◇ X2)) := by
  intro X0 X1 X2
  exact (Law.source (G := G)) X0 X1 X2

theorem f18 : ∀ (X2 X3 X0 X1 : G), (X2 ◇ (X3 ◇ X3)) = (((X0 ◇ X2) ◇ X2) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X2) ◇ X2))) := by
  intro X2 X3 X0 X1
  calc (X2 ◇ (X3 ◇ X3))
    _ = (((X0 ◇ X2) ◇ X2) ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X2)) ◇ ((X0 ◇ X2) ◇ X2))) := ((f7 X2 X3 (((X0 ◇ X2) ◇ X2))).symm).symm
    _ = (((X0 ◇ X2) ◇ X2) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X2) ◇ X2))) := congrArg (((X0 ◇ X2) ◇ X2) ◇ ·) (congrArg (· ◇ ((X0 ◇ X2) ◇ X2)) ((f7 X0 X1 X2).symm))

theorem f25 : ∀ (X0 X1 X2 : G), (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X2 ◇ X2)) := by
  intro X0 X1 X2
  calc (X0 ◇ (X1 ◇ X1))
    _ = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := ((f7 X0 X1 X0).symm).symm
    _ = (X0 ◇ (X2 ◇ X2)) := (f7 X0 X2 X0).symm

theorem f9 : ∀ (K1 : G), (K1 ◇ K1) = (K1 ◇ K1) := by
  intro K1
  rfl

theorem f117 : ∀ (X0 X1 K1 : G), (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (K1 ◇ K1)) := by
  intro X0 X1 K1
  calc (X0 ◇ (X1 ◇ X1))
    _ = (X0 ◇ (X0 ◇ X0)) := (f25 X0 X0 X1).symm
    _ = (X0 ◇ (K1 ◇ K1)) := f25 X0 X0 K1

theorem f196 : ∀ (X2 X0 K1 : G), (X2 ◇ ((X0 ◇ X2) ◇ X2)) = (X0 ◇ (K1 ◇ K1)) := by
  intro X2 X0 K1
  exact ((Law.source (G := G)) X0 K1 X2).symm

theorem f412 : ∀ (X1 K1 X0 : G), (X1 ◇ (K1 ◇ K1)) = (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ (K1 ◇ K1)) ◇ ((X0 ◇ X1) ◇ X1))) := by
  intro X1 K1 X0
  calc (X1 ◇ (K1 ◇ K1))
    _ = (((X0 ◇ X1) ◇ X1) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1))) := (f196 (((X0 ◇ X1) ◇ X1)) X1 K1).symm
    _ = (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ (K1 ◇ K1)) ◇ ((X0 ◇ X1) ◇ X1))) := congrArg (((X0 ◇ X1) ◇ X1) ◇ ·) (congrArg (· ◇ ((X0 ◇ X1) ◇ X1)) (f196 X1 X0 K1))

theorem f9963 : ∀ (X0 K1 : G), ((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) = (((X0 ◇ (X0 ◇ (K1 ◇ K1))) ◇ (X0 ◇ (K1 ◇ K1))) ◇ (X0 ◇ (K1 ◇ K1))) := by
  intro X0 K1
  calc ((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))
    _ = (((X0 ◇ (X0 ◇ (K1 ◇ K1))) ◇ (X0 ◇ (K1 ◇ K1))) ◇ ((X0 ◇ (K1 ◇ K1)) ◇ ((X0 ◇ (X0 ◇ (K1 ◇ K1))) ◇ (X0 ◇ (K1 ◇ K1))))) := ((f412 ((X0 ◇ (K1 ◇ K1))) K1 X0).symm).symm
    _ = (((X0 ◇ (X0 ◇ (K1 ◇ K1))) ◇ (X0 ◇ (K1 ◇ K1))) ◇ (X0 ◇ (K1 ◇ K1))) := congrArg (((X0 ◇ (X0 ◇ (K1 ◇ K1))) ◇ (X0 ◇ (K1 ◇ K1))) ◇ ·) (f196 ((X0 ◇ (K1 ◇ K1))) X0 K1)

theorem f10 : ∀ (K0 K1 : G), (K0 ◇ (K1 ◇ K1)) = (K0 ◇ (K1 ◇ K1)) := by
  intro K0 K1
  rfl

theorem f19 : ∀ (K0 X0 K1 : G), (K0 ◇ (X0 ◇ X0)) = ((K1 ◇ K1) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) := by
  intro K0 X0 K1
  exact (Law.source (G := G)) K0 X0 ((K1 ◇ K1))

theorem f58 : ∀ (K1 K0 X1 : G), ((K1 ◇ K1) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) = (X1 ◇ ((K0 ◇ X1) ◇ X1)) := by
  intro K1 K0 X1
  calc ((K1 ◇ K1) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)))
    _ = (K0 ◇ (K1 ◇ K1)) := (f19 K0 K1 K1).symm
    _ = (X1 ◇ ((K0 ◇ X1) ◇ X1)) := f7 K0 K1 X1

theorem f1079 : ∀ (X0 K1 K0 : G), (X0 ◇ (K1 ◇ K1)) = (((K0 ◇ X0) ◇ X0) ◇ (((K1 ◇ K1) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) ◇ ((K0 ◇ X0) ◇ X0))) := by
  intro X0 K1 K0
  calc (X0 ◇ (K1 ◇ K1))
    _ = (((K0 ◇ X0) ◇ X0) ◇ ((X0 ◇ ((K0 ◇ X0) ◇ X0)) ◇ ((K0 ◇ X0) ◇ X0))) := (f196 (((K0 ◇ X0) ◇ X0)) X0 K1).symm
    _ = (((K0 ◇ X0) ◇ X0) ◇ (((K1 ◇ K1) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) ◇ ((K0 ◇ X0) ◇ X0))) := congrArg (((K0 ◇ X0) ◇ X0) ◇ ·) (congrArg (· ◇ ((K0 ◇ X0) ◇ X0)) ((f58 K1 K0 X0).symm))

theorem f209 : ∀ (K0 K1 : G), (K0 ◇ (K1 ◇ K1)) = ((K1 ◇ K1) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) := by
  intro K0 K1
  exact (Law.source (G := G)) K0 K1 ((K1 ◇ K1))

theorem f216 : ∀ (K0 K1 : G), (K0 ◇ (K1 ◇ K1)) = ((K1 ◇ K1) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) := by
  intro K0 K1
  exact (Law.source (G := G)) K0 K1 ((K1 ◇ K1))

theorem f1086 : ∀ (X0 K1 K0 : G), (X0 ◇ (K1 ◇ K1)) = (((K0 ◇ X0) ◇ X0) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ ((K0 ◇ X0) ◇ X0))) := by
  intro X0 K1 K0
  calc (X0 ◇ (K1 ◇ K1))
    _ = (((K0 ◇ X0) ◇ X0) ◇ (((K1 ◇ K1) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) ◇ ((K0 ◇ X0) ◇ X0))) := ((f1079 X0 K1 K0).symm).symm
    _ = (((K0 ◇ X0) ◇ X0) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ ((K0 ◇ X0) ◇ X0))) := congrArg (((K0 ◇ X0) ◇ X0) ◇ ·) (congrArg (· ◇ ((K0 ◇ X0) ◇ X0)) ((f216 K0 K1).symm))

theorem f5227 : ∀ (K0 K1 : G), ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) = (((K0 ◇ (K0 ◇ (K1 ◇ K1))) ◇ (K0 ◇ (K1 ◇ K1))) ◇ (K0 ◇ (K1 ◇ K1))) := by
  intro K0 K1
  calc ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))
    _ = (((K0 ◇ (K0 ◇ (K1 ◇ K1))) ◇ (K0 ◇ (K1 ◇ K1))) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ ((K0 ◇ (K0 ◇ (K1 ◇ K1))) ◇ (K0 ◇ (K1 ◇ K1))))) := ((f1086 ((K0 ◇ (K1 ◇ K1))) K1 K0).symm).symm
    _ = (((K0 ◇ (K0 ◇ (K1 ◇ K1))) ◇ (K0 ◇ (K1 ◇ K1))) ◇ (K0 ◇ (K1 ◇ K1))) := congrArg (((K0 ◇ (K0 ◇ (K1 ◇ K1))) ◇ (K0 ◇ (K1 ◇ K1))) ◇ ·) (f196 ((K0 ◇ (K1 ◇ K1))) K0 K1)

theorem f5243 : ∀ (K0 K1 : G), ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) = (((K0 ◇ (K0 ◇ (K1 ◇ K1))) ◇ (K0 ◇ (K1 ◇ K1))) ◇ (K0 ◇ (K1 ◇ K1))) := by
  intro K0 K1
  calc ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))
    _ = ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) := (f10 ((K0 ◇ (K1 ◇ K1))) K1).symm
    _ = (((K0 ◇ (K0 ◇ (K1 ◇ K1))) ◇ (K0 ◇ (K1 ◇ K1))) ◇ (K0 ◇ (K1 ◇ K1))) := f5227 K0 K1

theorem f5360 : ∀ (K0 K1 : G), ((K0 ◇ (K1 ◇ K1)) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) = ((K0 ◇ (K0 ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1)) := by
  intro K0 K1
  calc ((K0 ◇ (K1 ◇ K1)) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)))
    _ = ((K0 ◇ (K1 ◇ K1)) ◇ (((K0 ◇ (K0 ◇ (K1 ◇ K1))) ◇ (K0 ◇ (K1 ◇ K1))) ◇ (K0 ◇ (K1 ◇ K1)))) := congrArg ((K0 ◇ (K1 ◇ K1)) ◇ ·) (((f5243 K0 K1).symm).symm)
    _ = ((K0 ◇ (K0 ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1)) := f196 ((K0 ◇ (K1 ◇ K1))) ((K0 ◇ (K0 ◇ (K1 ◇ K1)))) K1

theorem f5381 : ∀ (K0 K1 : G), ((K0 ◇ (K1 ◇ K1)) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) = ((K1 ◇ K1) ◇ (((K0 ◇ (K1 ◇ K1)) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1))) := by
  intro K0 K1
  calc ((K0 ◇ (K1 ◇ K1)) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)))
    _ = ((K0 ◇ (K0 ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1)) := f5360 K0 K1
    _ = ((K1 ◇ K1) ◇ (((K0 ◇ (K0 ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) := (f196 ((K1 ◇ K1)) ((K0 ◇ (K0 ◇ (K1 ◇ K1)))) K1).symm
    _ = ((K1 ◇ K1) ◇ (((K0 ◇ (K1 ◇ K1)) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1))) := congrArg ((K1 ◇ K1) ◇ ·) (congrArg (· ◇ (K1 ◇ K1)) ((f5360 K0 K1).symm))

theorem f10346 : ∀ (X0 K1 : G), ((X0 ◇ (K1 ◇ K1)) ◇ ((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) = ((X0 ◇ (X0 ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1)) := by
  intro X0 K1
  calc ((X0 ◇ (K1 ◇ K1)) ◇ ((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)))
    _ = ((X0 ◇ (K1 ◇ K1)) ◇ (((X0 ◇ (X0 ◇ (K1 ◇ K1))) ◇ (X0 ◇ (K1 ◇ K1))) ◇ (X0 ◇ (K1 ◇ K1)))) := congrArg ((X0 ◇ (K1 ◇ K1)) ◇ ·) (((f9963 X0 K1).symm).symm)
    _ = ((X0 ◇ (X0 ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1)) := f196 ((X0 ◇ (K1 ◇ K1))) ((X0 ◇ (X0 ◇ (K1 ◇ K1)))) K1

end Equation55122Kernel

end

section
                            

namespace Equation55122Kernel

variable {G : Type} [Magma G] [Law G]

                                         

set_option linter.unusedVariables false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000


theorem f10527 : ∀ (K1 X0 : G), ((K1 ◇ K1) ◇ (K1 ◇ K1)) = (((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ ((X0 ◇ (X0 ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1))) := by
  intro K1 X0
  calc ((K1 ◇ K1) ◇ (K1 ◇ K1))
    _ = (((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ ((X0 ◇ (K1 ◇ K1)) ◇ ((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)))) := ((f412 ((K1 ◇ K1)) K1 X0).symm).symm
    _ = (((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ ((X0 ◇ (X0 ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1))) := congrArg (((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ ·) (f10346 X0 K1)

theorem f10593 : ∀ (K1 X0 : G), ((K1 ◇ K1) ◇ (K1 ◇ K1)) = ((((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (((X0 ◇ (X0 ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) := by
  intro K1 X0
  calc ((K1 ◇ K1) ◇ (K1 ◇ K1))
    _ = ((((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (((X0 ◇ (K1 ◇ K1)) ◇ ((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1))) := ((f10527 K1 ((X0 ◇ (K1 ◇ K1)))).symm).symm
    _ = ((((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (((X0 ◇ (X0 ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) := congrArg ((((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ ·) (congrArg (· ◇ (K1 ◇ K1)) (f10346 X0 K1))

theorem f16077 : ∀ (X0 K1 : G), ((((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) = ((((X0 ◇ (X0 ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (((K1 ◇ K1) ◇ (K1 ◇ K1)) ◇ (((X0 ◇ (X0 ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)))) := by
  intro X0 K1
  calc ((((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))
    _ = ((((X0 ◇ (X0 ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (((((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (((X0 ◇ (X0 ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) ◇ (((X0 ◇ (X0 ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)))) := (f196 ((((X0 ◇ (X0 ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) ((((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) K1).symm
    _ = ((((X0 ◇ (X0 ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (((K1 ◇ K1) ◇ (K1 ◇ K1)) ◇ (((X0 ◇ (X0 ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)))) := congrArg ((((X0 ◇ (X0 ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ ·) (congrArg (· ◇ (((X0 ◇ (X0 ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) ((f10593 K1 X0).symm))

theorem f206 : ∀ (X0 X2 X1 K1 : G), (X0 ◇ (X2 ◇ X2)) = ((X1 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (K1 ◇ K1))) := by
  intro X0 X2 X1 K1
  calc (X0 ◇ (X2 ◇ X2))
    _ = ((X1 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) := ((f7 X0 X2 ((X1 ◇ X1))).symm).symm
    _ = ((X1 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (K1 ◇ K1))) := congrArg ((X1 ◇ X1) ◇ ·) (f117 ((X0 ◇ (X1 ◇ X1))) X1 K1)

theorem f219 : ∀ (X0 X2 X1 K1 : G), (X0 ◇ (X2 ◇ X2)) = ((X1 ◇ X1) ◇ ((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) := by
  intro X0 X2 X1 K1
  calc (X0 ◇ (X2 ◇ X2))
    _ = ((X1 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (K1 ◇ K1))) := ((f206 X0 X2 X1 K1).symm).symm
    _ = ((X1 ◇ X1) ◇ ((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) := congrArg ((X1 ◇ X1) ◇ ·) (congrArg (· ◇ (K1 ◇ K1)) (f117 X0 X1 K1))

theorem f235 : ∀ (X0 K1 X1 : G), (X0 ◇ (K1 ◇ K1)) = ((X1 ◇ X1) ◇ ((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) := by
  intro X0 K1 X1
  calc (X0 ◇ (K1 ◇ K1))
    _ = (X0 ◇ (X0 ◇ X0)) := (f117 X0 X0 K1).symm
    _ = ((X1 ◇ X1) ◇ ((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) := f219 X0 X0 X1 K1

theorem f16080 : ∀ (X0 K1 : G), ((((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) = ((((X0 ◇ (X0 ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ ((X0 ◇ (X0 ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1))) := by
  intro X0 K1
  calc ((((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))
    _ = ((((X0 ◇ (X0 ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (((K1 ◇ K1) ◇ (K1 ◇ K1)) ◇ (((X0 ◇ (X0 ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)))) := ((f16077 X0 K1).symm).symm
    _ = ((((X0 ◇ (X0 ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ ((X0 ◇ (X0 ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1))) := congrArg ((((X0 ◇ (X0 ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ ·) ((f235 ((X0 ◇ (X0 ◇ (K1 ◇ K1)))) K1 ((K1 ◇ K1))).symm)

theorem f1354 : ∀ (X0 K1 : G), (((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (X0 ◇ (K1 ◇ K1))) = (((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) := by
  intro X0 K1
  calc (((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (X0 ◇ (K1 ◇ K1)))
    _ = (((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ ((((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ ((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) ◇ ((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)))) := congrArg (((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ ·) (((f235 X0 K1 (((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)))).symm).symm)
    _ = (((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) := f196 (((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) (((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) K1

theorem f16101 : ∀ (X0 K1 : G), ((((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) = ((((X0 ◇ (X0 ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) := by
  intro X0 K1
  calc ((((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))
    _ = ((((X0 ◇ (X0 ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ ((X0 ◇ (X0 ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1))) := ((f16080 X0 K1).symm).symm
    _ = ((((X0 ◇ (X0 ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) := f1354 ((X0 ◇ (X0 ◇ (K1 ◇ K1)))) K1

theorem f16180 : ∀ (X0 K1 : G), (((X0 ◇ (X0 ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) = ((K1 ◇ K1) ◇ ((((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) := by
  intro X0 K1
  calc (((X0 ◇ (X0 ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))
    _ = ((K1 ◇ K1) ◇ ((((X0 ◇ (X0 ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) := (f196 ((K1 ◇ K1)) (((X0 ◇ (X0 ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1))) K1).symm
    _ = ((K1 ◇ K1) ◇ ((((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) := congrArg ((K1 ◇ K1) ◇ ·) ((f16101 X0 K1).symm)

theorem f16204 : ∀ (X0 K1 : G), (((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) = (((X0 ◇ (X0 ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) := by
  intro X0 K1
  calc (((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))
    _ = ((K1 ◇ K1) ◇ ((((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) := (f196 ((K1 ◇ K1)) (((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) K1).symm
    _ = (((X0 ◇ (X0 ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) := (f16180 X0 K1).symm

theorem f16289 : ∀ (X0 K1 : G), ((X0 ◇ (X0 ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1)) = ((K1 ◇ K1) ◇ (((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) := by
  intro X0 K1
  calc ((X0 ◇ (X0 ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1))
    _ = ((K1 ◇ K1) ◇ (((X0 ◇ (X0 ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) := (f196 ((K1 ◇ K1)) ((X0 ◇ (X0 ◇ (K1 ◇ K1)))) K1).symm
    _ = ((K1 ◇ K1) ◇ (((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) := congrArg ((K1 ◇ K1) ◇ ·) ((f16204 X0 K1).symm)

theorem f16316 : ∀ (X0 K1 : G), ((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) = ((X0 ◇ (X0 ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1)) := by
  intro X0 K1
  calc ((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))
    _ = ((K1 ◇ K1) ◇ (((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) := (f196 ((K1 ◇ K1)) ((X0 ◇ (K1 ◇ K1))) K1).symm
    _ = ((X0 ◇ (X0 ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1)) := (f16289 X0 K1).symm

theorem f16383 : ∀ (K0 K1 : G), ((K0 ◇ (K1 ◇ K1)) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) = ((K1 ◇ K1) ◇ (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) := by
  intro K0 K1
  calc ((K0 ◇ (K1 ◇ K1)) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)))
    _ = ((K1 ◇ K1) ◇ (((K0 ◇ (K1 ◇ K1)) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1))) := ((f5381 K0 K1).symm).symm
    _ = ((K1 ◇ K1) ◇ (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) := congrArg ((K1 ◇ K1) ◇ ·) ((f16316 ((K0 ◇ (K1 ◇ K1))) K1).symm)

theorem f16415 : ∀ (K0 K1 : G), ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) = ((K0 ◇ (K1 ◇ K1)) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) := by
  intro K0 K1
  calc ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))
    _ = ((K1 ◇ K1) ◇ (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) := (f196 ((K1 ◇ K1)) ((K0 ◇ (K1 ◇ K1))) K1).symm
    _ = ((K0 ◇ (K1 ◇ K1)) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) := (f16383 K0 K1).symm

theorem f18014 : ∀ (K0 K1 : G), ((((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) = (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) := by
  intro K0 K1
  calc ((((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)))
    _ = ((((K0 ◇ (K1 ◇ K1)) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) := congrArg (· ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) (congrArg (· ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) (((f16415 K0 K1).symm).symm))
    _ = (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) := (f9963 ((K0 ◇ (K1 ◇ K1))) K1).symm

theorem f422 : ∀ (K0 K1 X0 : G), (K0 ◇ (K1 ◇ K1)) = ((X0 ◇ X0) ◇ (((K1 ◇ K1) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) ◇ (X0 ◇ X0))) := by
  intro K0 K1 X0
  calc (K0 ◇ (K1 ◇ K1))
    _ = ((X0 ◇ X0) ◇ ((K0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := (f196 ((X0 ◇ X0)) K0 K1).symm
    _ = ((X0 ◇ X0) ◇ (((K1 ◇ K1) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) ◇ (X0 ◇ X0))) := congrArg ((X0 ◇ X0) ◇ ·) (congrArg (· ◇ (X0 ◇ X0)) (f19 K0 X0 K1))

theorem f472 : ∀ (K0 K1 X0 : G), (K0 ◇ (K1 ◇ K1)) = ((X0 ◇ X0) ◇ (((K1 ◇ K1) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1))) := by
  intro K0 K1 X0
  calc (K0 ◇ (K1 ◇ K1))
    _ = ((X0 ◇ X0) ◇ (((K1 ◇ K1) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) ◇ (X0 ◇ X0))) := ((f422 K0 K1 X0).symm).symm
    _ = ((X0 ◇ X0) ◇ (((K1 ◇ K1) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1))) := congrArg ((X0 ◇ X0) ◇ ·) (f117 (((K1 ◇ K1) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)))) X0 K1)

theorem f492 : ∀ (K0 K1 X0 : G), (K0 ◇ (K1 ◇ K1)) = ((X0 ◇ X0) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) := by
  intro K0 K1 X0
  calc (K0 ◇ (K1 ◇ K1))
    _ = ((X0 ◇ X0) ◇ (((K1 ◇ K1) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1))) := ((f472 K0 K1 X0).symm).symm
    _ = ((X0 ◇ X0) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) := congrArg ((X0 ◇ X0) ◇ ·) (congrArg (· ◇ (K1 ◇ K1)) ((f216 K0 K1).symm))

theorem f499 : ∀ (K0 K1 X0 : G), (K0 ◇ (K1 ◇ K1)) = ((X0 ◇ X0) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) := by
  intro K0 K1 X0
  calc (K0 ◇ (K1 ◇ K1))
    _ = (K0 ◇ (K1 ◇ K1)) := (f10 K0 K1).symm
    _ = ((X0 ◇ X0) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) := f492 K0 K1 X0

end Equation55122Kernel

end

section
                            

namespace Equation55122Kernel

variable {G : Type} [Magma G] [Law G]

                                         

set_option linter.unusedVariables false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000


theorem f18033 : ∀ (K0 K1 : G), (K0 ◇ (K1 ◇ K1)) = (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) := by
  intro K0 K1
  calc (K0 ◇ (K1 ◇ K1))
    _ = ((((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) := ((f499 K0 K1 (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)))).symm).symm
    _ = (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) := f18014 K0 K1

theorem f18062 : ∀ (K1 X0 K0 X1 : G), ((K1 ◇ K1) ◇ (X0 ◇ X0)) = ((K0 ◇ (K1 ◇ K1)) ◇ (((K0 ◇ (K1 ◇ K1)) ◇ (X1 ◇ X1)) ◇ (K0 ◇ (K1 ◇ K1)))) := by
  intro K1 X0 K0 X1
  simpa only [(f18033 K0 K1).symm] using
    (f18 (K1 ◇ K1) X0 (K0 ◇ (K1 ◇ K1)) X1)

theorem f18097 : ∀ (K1 X0 K0 : G), ((K1 ◇ K1) ◇ (X0 ◇ X0)) = ((K0 ◇ (K1 ◇ K1)) ◇ (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K0 ◇ (K1 ◇ K1)))) := by
  intro K1 X0 K0
  calc ((K1 ◇ K1) ◇ (X0 ◇ X0))
    _ = ((K1 ◇ K1) ◇ (K1 ◇ K1)) := (f117 ((K1 ◇ K1)) K1 X0).symm
    _ = ((K0 ◇ (K1 ◇ K1)) ◇ (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K0 ◇ (K1 ◇ K1)))) := f18062 K1 K1 K0 K1

theorem f508 : ∀ (K0 K1 : G), (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) = (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K0 ◇ (K1 ◇ K1))) := by
  intro K0 K1
  calc (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))
    _ = (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ ((((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)))) := (f196 (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) K1).symm
    _ = (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K0 ◇ (K1 ◇ K1))) := congrArg (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ ·) ((f499 K0 K1 (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)))).symm)

theorem f18123 : ∀ (K1 X0 K0 : G), ((K1 ◇ K1) ◇ (X0 ◇ X0)) = ((K0 ◇ (K1 ◇ K1)) ◇ (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) := by
  intro K1 X0 K0
  calc ((K1 ◇ K1) ◇ (X0 ◇ X0))
    _ = ((K0 ◇ (K1 ◇ K1)) ◇ (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K0 ◇ (K1 ◇ K1)))) := ((f18097 K1 X0 K0).symm).symm
    _ = ((K0 ◇ (K1 ◇ K1)) ◇ (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) := congrArg ((K0 ◇ (K1 ◇ K1)) ◇ ·) ((f508 K0 K1).symm)

theorem f18022 : ∀ (K0 K1 : G), ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) = (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)))) := by
  intro K0 K1
  calc ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))
    _ = (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (((K0 ◇ (K1 ◇ K1)) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)))) := (f196 (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) ((K0 ◇ (K1 ◇ K1))) K1).symm
    _ = (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)))) := congrArg (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ ·) (congrArg (· ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) ((f16415 K0 K1).symm))

theorem f18025 : ∀ (K0 K1 : G), ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) = (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) := by
  intro K0 K1
  calc ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))
    _ = (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)))) := ((f18022 K0 K1).symm).symm
    _ = (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) := f117 (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) K1

theorem f18142 : ∀ (K1 X0 K0 : G), ((K1 ◇ K1) ◇ (X0 ◇ X0)) = ((K0 ◇ (K1 ◇ K1)) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) := by
  intro K1 X0 K0
  calc ((K1 ◇ K1) ◇ (X0 ◇ X0))
    _ = ((K0 ◇ (K1 ◇ K1)) ◇ (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) := ((f18123 K1 X0 K0).symm).symm
    _ = ((K0 ◇ (K1 ◇ K1)) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) := congrArg ((K0 ◇ (K1 ◇ K1)) ◇ ·) ((f18025 K0 K1).symm)

theorem f18154 : ∀ (K0 K1 X0 : G), ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) = ((K1 ◇ K1) ◇ (X0 ◇ X0)) := by
  intro K0 K1 X0
  calc ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))
    _ = ((K0 ◇ (K1 ◇ K1)) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) := ((f16415 K0 K1).symm).symm
    _ = ((K1 ◇ K1) ◇ (X0 ◇ X0)) := (f18142 K1 X0 K0).symm

theorem f18162 : ∀ (K0 K1 : G), ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) = ((K1 ◇ K1) ◇ (K1 ◇ K1)) := by
  intro K0 K1
  calc ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))
    _ = ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) := (f117 ((K0 ◇ (K1 ◇ K1))) K1 K1).symm
    _ = ((K1 ◇ K1) ◇ (K1 ◇ K1)) := f18154 K0 K1 K1

theorem f11 : ∀ (K1 K0 : G), (K1 ◇ K0) = (K1 ◇ K0) := by
  intro K1 K0
  rfl

theorem f22 : ∀ (K1 X0 K0 : G), (K1 ◇ (X0 ◇ X0)) = (K0 ◇ ((K1 ◇ K0) ◇ K0)) := by
  intro K1 X0 K0
  exact (Law.source (G := G)) K1 X0 K0

theorem f12 : ∀ (K1 K0 : G), ((K1 ◇ K0) ◇ K0) = ((K1 ◇ K0) ◇ K0) := by
  intro K1 K0
  rfl

theorem f26 : ∀ (K0 K1 X0 : G), (K0 ◇ ((K1 ◇ K0) ◇ K0)) = (K1 ◇ (X0 ◇ X0)) := by
  intro K0 K1 X0
  exact ((Law.source (G := G)) K1 X0 K0).symm

theorem f13 : ∀ (K0 K1 : G), (K0 ◇ ((K1 ◇ K0) ◇ K0)) = (K0 ◇ ((K1 ◇ K0) ◇ K0)) := by
  intro K0 K1
  rfl

theorem f27 : ∀ (K0 K1 X0 : G), (K0 ◇ ((K1 ◇ K0) ◇ K0)) = (K1 ◇ (X0 ◇ X0)) := by
  intro K0 K1 X0
  exact ((Law.source (G := G)) K1 X0 K0).symm

theorem f31 : ∀ (K0 K1 X1 : G), (K0 ◇ ((K1 ◇ K0) ◇ K0)) = (X1 ◇ ((K1 ◇ X1) ◇ X1)) := by
  intro K0 K1 X1
  calc (K0 ◇ ((K1 ◇ K0) ◇ K0))
    _ = (K1 ◇ (K0 ◇ K0)) := (f7 K1 K0 K0).symm
    _ = (X1 ◇ ((K1 ◇ X1) ◇ X1)) := f7 K1 K0 X1

theorem f44 : ∀ (K0 K1 X1 X0 : G), (K0 ◇ ((K1 ◇ K0) ◇ K0)) = ((X1 ◇ X1) ◇ (X0 ◇ (((K1 ◇ (X1 ◇ X1)) ◇ X0) ◇ X0))) := by
  intro K0 K1 X1 X0
  calc (K0 ◇ ((K1 ◇ K0) ◇ K0))
    _ = ((X1 ◇ X1) ◇ ((K1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) := (f31 ((X1 ◇ X1)) K1 K0).symm
    _ = ((X1 ◇ X1) ◇ (X0 ◇ (((K1 ◇ (X1 ◇ X1)) ◇ X0) ◇ X0))) := congrArg ((X1 ◇ X1) ◇ ·) (f7 ((K1 ◇ (X1 ◇ X1))) X1 X0)

theorem f48 : ∀ (K0 K1 X1 X0 : G), (K0 ◇ ((K1 ◇ K0) ◇ K0)) = ((X1 ◇ X1) ◇ (X0 ◇ (((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ X0) ◇ X0))) := by
  intro K0 K1 X1 X0
  calc (K0 ◇ ((K1 ◇ K0) ◇ K0))
    _ = ((X1 ◇ X1) ◇ (X0 ◇ (((K1 ◇ (X1 ◇ X1)) ◇ X0) ◇ X0))) := ((f44 K0 K1 X1 X0).symm).symm
    _ = ((X1 ◇ X1) ◇ (X0 ◇ (((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ X0) ◇ X0))) := congrArg ((X1 ◇ X1) ◇ ·) (congrArg (X0 ◇ ·) (congrArg (· ◇ X0) (congrArg (· ◇ X0) ((f27 K0 K1 X1).symm))))

theorem f414 : ∀ (K1 X0 K0 : G), (((K1 ◇ X0) ◇ X0) ◇ ((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ ((K1 ◇ X0) ◇ X0))) = (X0 ◇ (K1 ◇ K1)) := by
  intro K1 X0 K0
  calc (((K1 ◇ X0) ◇ X0) ◇ ((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ ((K1 ◇ X0) ◇ X0)))
    _ = (((K1 ◇ X0) ◇ X0) ◇ ((X0 ◇ ((K1 ◇ X0) ◇ X0)) ◇ ((K1 ◇ X0) ◇ X0))) := congrArg (((K1 ◇ X0) ◇ X0) ◇ ·) (congrArg (· ◇ ((K1 ◇ X0) ◇ X0)) ((f31 X0 K1 K0).symm))
    _ = (X0 ◇ (K1 ◇ K1)) := f196 (((K1 ◇ X0) ◇ X0)) X0 K1

end Equation55122Kernel

end

section
                            

namespace Equation55122Kernel

variable {G : Type} [Magma G] [Law G]

                                         

set_option linter.unusedVariables false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000


theorem f4114 : ∀ (K0 K1 : G), ((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (K1 ◇ K1)) = (((K1 ◇ (K0 ◇ ((K1 ◇ K0) ◇ K0))) ◇ (K0 ◇ ((K1 ◇ K0) ◇ K0))) ◇ (K0 ◇ ((K1 ◇ K0) ◇ K0))) := by
  intro K0 K1
  calc ((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (K1 ◇ K1))
    _ = (((K1 ◇ (K0 ◇ ((K1 ◇ K0) ◇ K0))) ◇ (K0 ◇ ((K1 ◇ K0) ◇ K0))) ◇ ((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ ((K1 ◇ (K0 ◇ ((K1 ◇ K0) ◇ K0))) ◇ (K0 ◇ ((K1 ◇ K0) ◇ K0))))) := (f414 K1 ((K0 ◇ ((K1 ◇ K0) ◇ K0))) K0).symm
    _ = (((K1 ◇ (K0 ◇ ((K1 ◇ K0) ◇ K0))) ◇ (K0 ◇ ((K1 ◇ K0) ◇ K0))) ◇ (K0 ◇ ((K1 ◇ K0) ◇ K0))) := congrArg (((K1 ◇ (K0 ◇ ((K1 ◇ K0) ◇ K0))) ◇ (K0 ◇ ((K1 ◇ K0) ◇ K0))) ◇ ·) (f31 ((K0 ◇ ((K1 ◇ K0) ◇ K0))) K1 K0)

theorem f5113 : ∀ (K0 K1 : G), ((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ ((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (K1 ◇ K1))) = ((K1 ◇ (K0 ◇ ((K1 ◇ K0) ◇ K0))) ◇ (K1 ◇ K1)) := by
  intro K0 K1
  calc ((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ ((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (K1 ◇ K1)))
    _ = ((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (((K1 ◇ (K0 ◇ ((K1 ◇ K0) ◇ K0))) ◇ (K0 ◇ ((K1 ◇ K0) ◇ K0))) ◇ (K0 ◇ ((K1 ◇ K0) ◇ K0)))) := congrArg ((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ ·) (((f4114 K0 K1).symm).symm)
    _ = ((K1 ◇ (K0 ◇ ((K1 ◇ K0) ◇ K0))) ◇ (K1 ◇ K1)) := f196 ((K0 ◇ ((K1 ◇ K0) ◇ K0))) ((K1 ◇ (K0 ◇ ((K1 ◇ K0) ◇ K0)))) K1

theorem f5133 : ∀ (K0 K1 : G), ((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ ((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (K1 ◇ K1))) = ((K1 ◇ K1) ◇ (((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ ((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1))) := by
  intro K0 K1
  calc ((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ ((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (K1 ◇ K1)))
    _ = ((K1 ◇ (K0 ◇ ((K1 ◇ K0) ◇ K0))) ◇ (K1 ◇ K1)) := f5113 K0 K1
    _ = ((K1 ◇ K1) ◇ (((K1 ◇ (K0 ◇ ((K1 ◇ K0) ◇ K0))) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) := (f196 ((K1 ◇ K1)) ((K1 ◇ (K0 ◇ ((K1 ◇ K0) ◇ K0)))) K1).symm
    _ = ((K1 ◇ K1) ◇ (((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ ((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1))) := congrArg ((K1 ◇ K1) ◇ ·) (congrArg (· ◇ (K1 ◇ K1)) ((f5113 K0 K1).symm))

theorem f16385 : ∀ (K0 K1 : G), ((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ ((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (K1 ◇ K1))) = ((K1 ◇ K1) ◇ (((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) := by
  intro K0 K1
  calc ((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ ((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (K1 ◇ K1)))
    _ = ((K1 ◇ K1) ◇ (((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ ((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1))) := ((f5133 K0 K1).symm).symm
    _ = ((K1 ◇ K1) ◇ (((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) := congrArg ((K1 ◇ K1) ◇ ·) ((f16316 ((K0 ◇ ((K1 ◇ K0) ◇ K0))) K1).symm)

theorem f16413 : ∀ (K0 K1 : G), ((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (K1 ◇ K1)) = ((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ ((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (K1 ◇ K1))) := by
  intro K0 K1
  calc ((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (K1 ◇ K1))
    _ = ((K1 ◇ K1) ◇ (((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) := (f196 ((K1 ◇ K1)) ((K0 ◇ ((K1 ◇ K0) ◇ K0))) K1).symm
    _ = ((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ ((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (K1 ◇ K1))) := (f16385 K0 K1).symm

theorem f16527 : ∀ (K0 K1 X0 : G), (K0 ◇ ((K1 ◇ K0) ◇ K0)) = ((X0 ◇ X0) ◇ (((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (K1 ◇ K1)) ◇ (((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (K1 ◇ K1)) ◇ ((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (K1 ◇ K1))))) := by
  intro K0 K1 X0
  calc (K0 ◇ ((K1 ◇ K0) ◇ K0))
    _ = ((X0 ◇ X0) ◇ (((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (K1 ◇ K1)) ◇ (((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ ((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (K1 ◇ K1))) ◇ ((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (K1 ◇ K1))))) := ((f48 K0 K1 X0 (((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (K1 ◇ K1)))).symm).symm
    _ = ((X0 ◇ X0) ◇ (((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (K1 ◇ K1)) ◇ (((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (K1 ◇ K1)) ◇ ((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (K1 ◇ K1))))) := congrArg ((X0 ◇ X0) ◇ ·) (congrArg (((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (K1 ◇ K1)) ◇ ·) (congrArg (· ◇ ((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (K1 ◇ K1))) ((f16413 K0 K1).symm)))

theorem f16550 : ∀ (K0 K1 X0 : G), (K0 ◇ ((K1 ◇ K0) ◇ K0)) = ((X0 ◇ X0) ◇ (((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) := by
  intro K0 K1 X0
  calc (K0 ◇ ((K1 ◇ K0) ◇ K0))
    _ = ((X0 ◇ X0) ◇ (((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (K1 ◇ K1)) ◇ (((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (K1 ◇ K1)) ◇ ((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (K1 ◇ K1))))) := ((f16527 K0 K1 X0).symm).symm
    _ = ((X0 ◇ X0) ◇ (((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) := congrArg ((X0 ◇ X0) ◇ ·) (f117 (((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (K1 ◇ K1))) (((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (K1 ◇ K1))) K1)

theorem f16562 : ∀ (K0 K1 : G), (K0 ◇ ((K1 ◇ K0) ◇ K0)) = ((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (K1 ◇ K1)) := by
  intro K0 K1
  calc (K0 ◇ ((K1 ◇ K0) ◇ K0))
    _ = ((K0 ◇ K0) ◇ (((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) := ((f16550 K0 K1 K0).symm).symm
    _ = ((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (K1 ◇ K1)) := (f235 ((K0 ◇ ((K1 ◇ K0) ◇ K0))) K1 K0).symm

theorem f16595 : ∀ (K0 K1 : G), ((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (K1 ◇ K1)) = (((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (K0 ◇ ((K1 ◇ K0) ◇ K0))) ◇ (K1 ◇ K1)) := by
  intro K0 K1
  calc ((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (K1 ◇ K1))
    _ = (((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) := congrArg (· ◇ (K1 ◇ K1)) (f16562 K0 K1)
    _ = (((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ ((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (K1 ◇ K1))) ◇ (K1 ◇ K1)) := f16316 ((K0 ◇ ((K1 ◇ K0) ◇ K0))) K1
    _ = (((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (K0 ◇ ((K1 ◇ K0) ◇ K0))) ◇ (K1 ◇ K1)) := congrArg (· ◇ (K1 ◇ K1)) (congrArg ((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ ·) ((f16562 K0 K1).symm))

theorem f510 : ∀ (X0 K1 K0 : G), ((X0 ◇ X0) ◇ (K1 ◇ K1)) = (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)))) := by
  intro X0 K1 K0
  calc ((X0 ◇ X0) ◇ (K1 ◇ K1))
    _ = (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (((X0 ◇ X0) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)))) := (f196 (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) ((X0 ◇ X0)) K1).symm
    _ = (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)))) := congrArg (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ ·) (congrArg (· ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) ((f499 K0 K1 X0).symm))

theorem f242 : ∀ (K1 X0 K0 : G), ((K1 ◇ K1) ◇ (X0 ◇ X0)) = (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)))) := by
  intro K1 X0 K0
  calc ((K1 ◇ K1) ◇ (X0 ◇ X0))
    _ = (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (((K1 ◇ K1) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)))) := ((f7 ((K1 ◇ K1)) X0 (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)))).symm).symm
    _ = (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)))) := congrArg (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ ·) (congrArg (· ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) ((f216 K0 K1).symm))

theorem f243 : ∀ (K0 K1 : G), (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)))) = ((K1 ◇ K1) ◇ (K1 ◇ K1)) := by
  intro K0 K1
  calc (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))))
    _ = ((K1 ◇ K1) ◇ (K0 ◇ K0)) := (f242 K1 K0 K0).symm
    _ = ((K1 ◇ K1) ◇ (K1 ◇ K1)) := f117 ((K1 ◇ K1)) K0 K1

theorem f513 : ∀ (X0 K1 : G), ((X0 ◇ X0) ◇ (K1 ◇ K1)) = ((K1 ◇ K1) ◇ (K1 ◇ K1)) := by
  intro X0 K1
  calc ((X0 ◇ X0) ◇ (K1 ◇ K1))
    _ = (((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ ((X0 ◇ (K1 ◇ K1)) ◇ ((X0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)))) := ((f510 X0 K1 X0).symm).symm
    _ = ((K1 ◇ K1) ◇ (K1 ◇ K1)) := (f510 K1 K1 X0).symm

theorem f16608 : ∀ (K0 K1 : G), ((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (K1 ◇ K1)) = ((K1 ◇ K1) ◇ (K1 ◇ K1)) := by
  intro K0 K1
  calc ((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (K1 ◇ K1))
    _ = (((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (K0 ◇ ((K1 ◇ K0) ◇ K0))) ◇ (K1 ◇ K1)) := ((f16595 K0 K1).symm).symm
    _ = ((K1 ◇ K1) ◇ (K1 ◇ K1)) := f513 ((K0 ◇ ((K1 ◇ K0) ◇ K0))) K1

theorem f16631 : ∀ (K0 K1 : G), (K0 ◇ ((K1 ◇ K0) ◇ K0)) = ((K1 ◇ K1) ◇ (K1 ◇ K1)) := by
  intro K0 K1
  calc (K0 ◇ ((K1 ◇ K0) ◇ K0))
    _ = ((K0 ◇ ((K1 ◇ K0) ◇ K0)) ◇ (K1 ◇ K1)) := ((f16562 K0 K1).symm).symm
    _ = ((K1 ◇ K1) ◇ (K1 ◇ K1)) := f16608 K0 K1

theorem f18166 : ∀ (K0 K1 : G), (K0 ◇ ((K1 ◇ K0) ◇ K0)) = ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) := by
  intro K0 K1
  calc (K0 ◇ ((K1 ◇ K0) ◇ K0))
    _ = ((K1 ◇ K1) ◇ (K1 ◇ K1)) := ((f16631 K0 K1).symm).symm
    _ = ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) := (f18162 K0 K1).symm

theorem f928 : ∀ (K0 K1 : G), (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) = ((K0 ◇ (K1 ◇ K1)) ◇ ((((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K0 ◇ (K1 ◇ K1)))) := by
  intro K0 K1
  calc (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))
    _ = ((K0 ◇ (K1 ◇ K1)) ◇ ((((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K0 ◇ (K1 ◇ K1))) ◇ (K0 ◇ (K1 ◇ K1)))) := (f196 ((K0 ◇ (K1 ◇ K1))) (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1))) K1).symm
    _ = ((K0 ◇ (K1 ◇ K1)) ◇ ((((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K0 ◇ (K1 ◇ K1)))) := congrArg ((K0 ◇ (K1 ◇ K1)) ◇ ·) (congrArg (· ◇ (K0 ◇ (K1 ◇ K1))) ((f508 K0 K1).symm))

theorem f18051 : ∀ (K0 K1 : G), (K0 ◇ (K1 ◇ K1)) = ((K0 ◇ (K1 ◇ K1)) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K0 ◇ (K1 ◇ K1)))) := by
  intro K0 K1
  calc (K0 ◇ (K1 ◇ K1))
    _ = (((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) := f18033 K0 K1
    _ = ((K0 ◇ (K1 ◇ K1)) ◇ ((((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) ◇ (K0 ◇ (K1 ◇ K1)))) := f928 K0 K1
    _ = ((K0 ◇ (K1 ◇ K1)) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K0 ◇ (K1 ◇ K1)))) := congrArg ((K0 ◇ (K1 ◇ K1)) ◇ ·) (congrArg (· ◇ (K0 ◇ (K1 ◇ K1))) ((f18033 K0 K1).symm))

theorem f18107 : ∀ (K0 K1 : G), (K0 ◇ (K1 ◇ K1)) = ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) := by
  intro K0 K1
  calc (K0 ◇ (K1 ◇ K1))
    _ = ((K0 ◇ (K1 ◇ K1)) ◇ ((K0 ◇ (K1 ◇ K1)) ◇ (K0 ◇ (K1 ◇ K1)))) := ((f18051 K0 K1).symm).symm
    _ = ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) := f117 ((K0 ◇ (K1 ◇ K1))) ((K0 ◇ (K1 ◇ K1))) K1

theorem f18168 : ∀ (K0 K1 : G), (K0 ◇ (K1 ◇ K1)) = (K0 ◇ ((K1 ◇ K0) ◇ K0)) := by
  intro K0 K1
  calc (K0 ◇ (K1 ◇ K1))
    _ = ((K0 ◇ (K1 ◇ K1)) ◇ (K1 ◇ K1)) := ((f18107 K0 K1).symm).symm
    _ = (K0 ◇ ((K1 ◇ K0) ◇ K0)) := (f18166 K0 K1).symm

end Equation55122Kernel

end

section
                            

namespace Equation55122Kernel

variable {G : Type} [Magma G] [Law G]

                                         

set_option linter.unusedVariables false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000


theorem compactInterface :
    ∀ (x y : G), x ◇ (y ◇ y) = x ◇ ((y ◇ x) ◇ x) := by
  exact f18168

end Equation55122Kernel

end

end submission

open submission
                   
                          

def submission : Goal := by
  intro G _ h
  letI : Equation55122Kernel.Law G := ⟨h⟩
  exact Equation55122Kernel.compactInterface (G := G)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_55122_to_55048 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_55122_to_55048
