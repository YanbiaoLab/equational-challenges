-- Equation22618 → Equation53590
-- Recorded verdict: true
-- Premise: x = (y ◇ (y ◇ x)) ◇ ((z ◇ z) ◇ y)
-- Conclusion: x ◇ y = (((z ◇ z) ◇ x) ◇ x) ◇ y
-- Original submission SHA-256: da292a41ec883071b5264f953c540398ef27e90efc3537018b99b885fc21632c
-- Aurora-accepted correction SHA-256: 6531c35b46a23478a9c8b7e9e3e4b1ab3821fa1b23644ddd6e12ab3459b87f15
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ (y ◇ x)) ◇ ((z ◇ z) ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (((z ◇ z) ◇ x) ◇ x) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Aurora-accepted corrected submission body
                   

set_option linter.unusedVariables false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

namespace submission

def certificate : Goal := by
  intro G _ h
  intro x y z
  have p3 : ∀ (x y z : G), ((x ◇ (x ◇ y)) ◇ ((z ◇ z) ◇ x)) = y := by
    intro x y z
    exact (h y x z).symm
  have p5 : ∀ (x y z u : G), (((x ◇ (x ◇ y)) ◇ y) ◇ ((z ◇ z) ◇ (x ◇ (x ◇ y)))) = ((u ◇ u) ◇ x) := by
    intro x y z u
    calc (((x ◇ (x ◇ y)) ◇ y) ◇ ((z ◇ z) ◇ (x ◇ (x ◇ y))))
      _ = (((x ◇ (x ◇ y)) ◇ ((x ◇ (x ◇ y)) ◇ ((u ◇ u) ◇ x))) ◇ ((z ◇ z) ◇ (x ◇ (x ◇ y)))) := congrArg (· ◇ ((z ◇ z) ◇ (x ◇ (x ◇ y)))) (congrArg ((x ◇ (x ◇ y)) ◇ ·) ((p3 x y u).symm))
      _ = ((u ◇ u) ◇ x) := p3 ((x ◇ (x ◇ y))) (((u ◇ u) ◇ x)) z
  have p15 : ∀ (x y z : G), ((x ◇ x) ◇ y) = ((z ◇ z) ◇ y) := by
    intro x y z
    calc ((x ◇ x) ◇ y)
      _ = (((y ◇ (y ◇ x)) ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ x)))) := (p5 y x x x).symm
      _ = ((z ◇ z) ◇ y) := p5 y x x z
  have p35 : ∀ (x y z u : G), (((x ◇ x) ◇ (y ◇ y)) ◇ z) = ((u ◇ u) ◇ z) := by
    intro x y z u
    calc (((x ◇ x) ◇ (y ◇ y)) ◇ z)
      _ = (((y ◇ y) ◇ (y ◇ y)) ◇ z) := congrArg (· ◇ z) ((p15 y ((y ◇ y)) x).symm)
      _ = ((u ◇ u) ◇ z) := p15 ((y ◇ y)) z u
  have p39 : ∀ (x y z : G), ((x ◇ x) ◇ ((y ◇ y) ◇ (z ◇ z))) = (z ◇ z) := by
    intro x y z
    calc ((x ◇ x) ◇ ((y ◇ y) ◇ (z ◇ z)))
      _ = (((z ◇ z) ◇ ((z ◇ z) ◇ (z ◇ z))) ◇ ((y ◇ y) ◇ (z ◇ z))) := (p35 z ((z ◇ z)) (((y ◇ y) ◇ (z ◇ z))) x).symm
      _ = (z ◇ z) := p3 ((z ◇ z)) ((z ◇ z)) y
  have p65 : ∀ (x y : G), (x ◇ x) = (y ◇ y) := by
    intro x y
    calc (x ◇ x)
      _ = ((y ◇ y) ◇ ((x ◇ x) ◇ (x ◇ x))) := (p39 y x x).symm
      _ = (((x ◇ x) ◇ ((x ◇ x) ◇ (y ◇ y))) ◇ ((x ◇ x) ◇ (x ◇ x))) := congrArg (· ◇ ((x ◇ x) ◇ (x ◇ x))) ((p39 x x y).symm)
      _ = (y ◇ y) := p3 ((x ◇ x)) ((y ◇ y)) x
  have p77 : ∀ (x y z : G), ((x ◇ (y ◇ y)) ◇ ((z ◇ z) ◇ x)) = x := by
    intro x y z
    calc ((x ◇ (y ◇ y)) ◇ ((z ◇ z) ◇ x))
      _ = ((x ◇ (x ◇ x)) ◇ ((z ◇ z) ◇ x)) := congrArg (· ◇ ((z ◇ z) ◇ x)) (congrArg (x ◇ ·) ((p65 x y).symm))
      _ = x := p3 x x z
  have p96 : ∀ (x y z : G), ((x ◇ x) ◇ y) = (y ◇ (y ◇ (z ◇ z))) := by
    intro x y z
    calc ((x ◇ x) ◇ y)
      _ = (((y ◇ (y ◇ (z ◇ z))) ◇ (z ◇ z)) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ (z ◇ z))))) := (p5 y ((z ◇ z)) x x).symm
      _ = (y ◇ (y ◇ (z ◇ z))) := p77 ((y ◇ (y ◇ (z ◇ z)))) z x
  have p105 : ∀ (x y z : G), ((x ◇ (x ◇ y)) ◇ (x ◇ (x ◇ (z ◇ z)))) = y := by
    intro x y z
    calc ((x ◇ (x ◇ y)) ◇ (x ◇ (x ◇ (z ◇ z))))
      _ = ((x ◇ (x ◇ y)) ◇ ((x ◇ x) ◇ x)) := congrArg ((x ◇ (x ◇ y)) ◇ ·) ((p96 x x z).symm)
      _ = y := p3 x y x
  have p156 : ∀ (x y z u : G), ((x ◇ ((y ◇ y) ◇ x)) ◇ (x ◇ (x ◇ (z ◇ z)))) = (x ◇ (u ◇ u)) := by
    intro x y z u
    calc ((x ◇ ((y ◇ y) ◇ x)) ◇ (x ◇ (x ◇ (z ◇ z))))
      _ = ((x ◇ (x ◇ (x ◇ (u ◇ u)))) ◇ (x ◇ (x ◇ (z ◇ z)))) := congrArg (· ◇ (x ◇ (x ◇ (z ◇ z)))) (congrArg (x ◇ ·) (((p96 y x u).symm).symm))
      _ = (x ◇ (u ◇ u)) := p105 x ((x ◇ (u ◇ u))) z
  have p11 : ∀ (x y z u : G), (((x ◇ x) ◇ y) ◇ ((z ◇ z) ◇ (y ◇ (y ◇ ((x ◇ x) ◇ y))))) = ((u ◇ u) ◇ y) := by
    intro x y z u
    calc (((x ◇ x) ◇ y) ◇ ((z ◇ z) ◇ (y ◇ (y ◇ ((x ◇ x) ◇ y)))))
      _ = (((y ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ y)) ◇ ((z ◇ z) ◇ (y ◇ (y ◇ ((x ◇ x) ◇ y))))) := congrArg (· ◇ ((z ◇ z) ◇ (y ◇ (y ◇ ((x ◇ x) ◇ y))))) ((p3 y (((x ◇ x) ◇ y)) x).symm)
      _ = ((u ◇ u) ◇ y) := p5 y (((x ◇ x) ◇ y)) z u
  have p615 : ∀ (x y z u w : G), (((x ◇ x) ◇ y) ◇ ((z ◇ z) ◇ (y ◇ (y ◇ ((u ◇ u) ◇ y))))) = ((w ◇ w) ◇ y) := by
    intro x y z u w
    calc (((x ◇ x) ◇ y) ◇ ((z ◇ z) ◇ (y ◇ (y ◇ ((u ◇ u) ◇ y)))))
      _ = (((u ◇ u) ◇ y) ◇ ((z ◇ z) ◇ (y ◇ (y ◇ ((u ◇ u) ◇ y))))) := congrArg (· ◇ ((z ◇ z) ◇ (y ◇ (y ◇ ((u ◇ u) ◇ y))))) ((p15 u y x).symm)
      _ = ((w ◇ w) ◇ y) := p11 u y z w
  have p30 : ∀ (x y z u w : G), (((x ◇ (x ◇ y)) ◇ y) ◇ (((z ◇ z) ◇ (u ◇ u)) ◇ (x ◇ (x ◇ y)))) = ((w ◇ w) ◇ x) := by
    intro x y z u w
    calc (((x ◇ (x ◇ y)) ◇ y) ◇ (((z ◇ z) ◇ (u ◇ u)) ◇ (x ◇ (x ◇ y))))
      _ = (((x ◇ (x ◇ y)) ◇ y) ◇ (((u ◇ u) ◇ (u ◇ u)) ◇ (x ◇ (x ◇ y)))) := congrArg (((x ◇ (x ◇ y)) ◇ y) ◇ ·) (congrArg (· ◇ (x ◇ (x ◇ y))) ((p15 u ((u ◇ u)) z).symm))
      _ = ((w ◇ w) ◇ x) := p5 x y ((u ◇ u)) w
  have p107 : ∀ (x y z u : G), (((x ◇ x) ◇ y) ◇ ((z ◇ z) ◇ y)) = (u ◇ u) := by
    intro x y z u
    calc (((x ◇ x) ◇ y) ◇ ((z ◇ z) ◇ y))
      _ = ((y ◇ (y ◇ (u ◇ u))) ◇ ((z ◇ z) ◇ y)) := congrArg (· ◇ ((z ◇ z) ◇ y)) (((p96 x y u).symm).symm)
      _ = (u ◇ u) := p3 y ((u ◇ u)) z
  have p190 : ∀ (x y z u w : G), (((x ◇ x) ◇ (y ◇ y)) ◇ (((z ◇ z) ◇ u) ◇ ((w ◇ w) ◇ u))) = (x ◇ x) := by
    intro x y z u w
    calc (((x ◇ x) ◇ (y ◇ y)) ◇ (((z ◇ z) ◇ u) ◇ ((w ◇ w) ◇ u)))
      _ = (((x ◇ x) ◇ (y ◇ y)) ◇ ((y ◇ y) ◇ (y ◇ y))) := congrArg (((x ◇ x) ◇ (y ◇ y)) ◇ ·) (((p107 z u w ((y ◇ y))).symm).symm)
      _ = (x ◇ x) := p107 x ((y ◇ y)) y x
  have p78 : ∀ (x y z : G), (((x ◇ x) ◇ ((x ◇ x) ◇ y)) ◇ (z ◇ z)) = y := by
    intro x y z
    calc (((x ◇ x) ◇ ((x ◇ x) ◇ y)) ◇ (z ◇ z))
      _ = (((x ◇ x) ◇ ((x ◇ x) ◇ y)) ◇ ((x ◇ x) ◇ (x ◇ x))) := congrArg (((x ◇ x) ◇ ((x ◇ x) ◇ y)) ◇ ·) ((p65 ((x ◇ x)) z).symm)
      _ = y := p3 ((x ◇ x)) y x
  have p137 : ∀ (x y z u : G), (((x ◇ x) ◇ ((y ◇ y) ◇ z)) ◇ (u ◇ u)) = z := by
    intro x y z u
    calc (((x ◇ x) ◇ ((y ◇ y) ◇ z)) ◇ (u ◇ u))
      _ = (((y ◇ y) ◇ ((y ◇ y) ◇ z)) ◇ (u ◇ u)) := congrArg (· ◇ (u ◇ u)) ((p15 y (((y ◇ y) ◇ z)) x).symm)
      _ = z := p78 y z u
  have p227 : ∀ (x y z u w v5 : G), (((((x ◇ x) ◇ y) ◇ ((z ◇ z) ◇ y)) ◇ ((u ◇ u) ◇ w)) ◇ (v5 ◇ v5)) = w := by
    intro x y z u w v5
    calc (((((x ◇ x) ◇ y) ◇ ((z ◇ z) ◇ y)) ◇ ((u ◇ u) ◇ w)) ◇ (v5 ◇ v5))
      _ = (((x ◇ x) ◇ ((u ◇ u) ◇ w)) ◇ (v5 ◇ v5)) := congrArg (· ◇ (v5 ◇ v5)) (congrArg (· ◇ ((u ◇ u) ◇ w)) (((p107 x y z x).symm).symm))
      _ = w := p137 x u w v5
  have p709 : ∀ (x y z u w v5 v6 v7 : G), (((((x ◇ x) ◇ y) ◇ (((z ◇ z) ◇ y) ◇ ((u ◇ u) ◇ (y ◇ (y ◇ ((w ◇ w) ◇ y)))))) ◇ ((v5 ◇ v5) ◇ v6)) ◇ (v7 ◇ v7)) = v6 := by
    intro x y z u w v5 v6 v7
    calc (((((x ◇ x) ◇ y) ◇ (((z ◇ z) ◇ y) ◇ ((u ◇ u) ◇ (y ◇ (y ◇ ((w ◇ w) ◇ y)))))) ◇ ((v5 ◇ v5) ◇ v6)) ◇ (v7 ◇ v7))
      _ = (((((x ◇ x) ◇ y) ◇ ((x ◇ x) ◇ y)) ◇ ((v5 ◇ v5) ◇ v6)) ◇ (v7 ◇ v7)) := congrArg (· ◇ (v7 ◇ v7)) (congrArg (· ◇ ((v5 ◇ v5) ◇ v6)) (congrArg (((x ◇ x) ◇ y) ◇ ·) (((p615 z y u w x).symm).symm)))
      _ = v6 := p227 x y x v5 v6 v7
  have p10252x : ∀ (X0 X1 X2 X3 X4 X5 X6 X7 : G), (((((X0 ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X2 ◇ X2) ◇ (X1 ◇ (X1 ◇ ((X3 ◇ X3) ◇ X1)))))) ◇ ((X2 ◇ X2) ◇ (X1 ◇ (X1 ◇ ((X3 ◇ X3) ◇ X1))))) ◇ (((X4 ◇ X4) ◇ (X5 ◇ X5)) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X6 ◇ X6) ◇ X1)))) = ((X7 ◇ X7) ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1 X2 X3 X4 X5 X6 X7
    calc (((((X0 ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X2 ◇ X2) ◇ (X1 ◇ (X1 ◇ ((X3 ◇ X3) ◇ X1)))))) ◇ ((X2 ◇ X2) ◇ (X1 ◇ (X1 ◇ ((X3 ◇ X3) ◇ X1))))) ◇ (((X4 ◇ X4) ◇ (X5 ◇ X5)) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X6 ◇ X6) ◇ X1))))
      _ = (((((X0 ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X2 ◇ X2) ◇ (X1 ◇ (X1 ◇ ((X3 ◇ X3) ◇ X1)))))) ◇ ((X2 ◇ X2) ◇ (X1 ◇ (X1 ◇ ((X3 ◇ X3) ◇ X1))))) ◇ (((X4 ◇ X4) ◇ (X5 ◇ X5)) ◇ (((X0 ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X2 ◇ X2) ◇ (X1 ◇ (X1 ◇ ((X3 ◇ X3) ◇ X1)))))))) := congrArg (((((X0 ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X2 ◇ X2) ◇ (X1 ◇ (X1 ◇ ((X3 ◇ X3) ◇ X1)))))) ◇ ((X2 ◇ X2) ◇ (X1 ◇ (X1 ◇ ((X3 ◇ X3) ◇ X1))))) ◇ ·) (congrArg (((X4 ◇ X4) ◇ (X5 ◇ X5)) ◇ ·) (congrArg (((X0 ◇ X0) ◇ X1) ◇ ·) ((p615 X0 X1 X2 X3 X6).symm)))
      _ = ((X7 ◇ X7) ◇ ((X0 ◇ X0) ◇ X1)) := p30 (((X0 ◇ X0) ◇ X1)) (((X2 ◇ X2) ◇ (X1 ◇ (X1 ◇ ((X3 ◇ X3) ◇ X1))))) X4 X5 X7
  have p10252 : ∀ (x y z u : G), ((x ◇ x) ◇ ((y ◇ y) ◇ z)) = (z ◇ (z ◇ ((u ◇ u) ◇ z))) := by
    intro x y z u
    simpa only [p190, p709] using ((p10252x y z x u x x x x).symm)
  have p10848x : ∀ (X0 X1 X2 X3 : G), ((X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) ◇ ((X2 ◇ X2) ◇ ((X2 ◇ X2) ◇ (X3 ◇ X3)))) = X0 := by
    intro X0 X1 X2 X3
    calc ((X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) ◇ ((X2 ◇ X2) ◇ ((X2 ◇ X2) ◇ (X3 ◇ X3))))
      _ = (((X2 ◇ X2) ◇ ((X2 ◇ X2) ◇ X0)) ◇ ((X2 ◇ X2) ◇ ((X2 ◇ X2) ◇ (X3 ◇ X3)))) := congrArg (· ◇ ((X2 ◇ X2) ◇ ((X2 ◇ X2) ◇ (X3 ◇ X3)))) ((p10252 X2 X2 X0 X1).symm)
      _ = X0 := p105 ((X2 ◇ X2)) X0 X3
  have p10848 : ∀ (x y z : G), ((x ◇ (x ◇ ((y ◇ y) ◇ x))) ◇ (z ◇ z)) = x := by
    intro x y z
    simpa only [p39] using (p10848x x y x z)
  have p11053x : ∀ (X0 X1 X2 X3 : G), ((X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0)))) ◇ ((X2 ◇ X2) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))))))) = ((X3 ◇ X3) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0)))) := by
    intro X0 X1 X2 X3
    calc ((X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0)))) ◇ ((X2 ◇ X2) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0)))))))
      _ = ((((X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))))) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0)))) ◇ ((X2 ◇ X2) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))))))) := congrArg (· ◇ ((X2 ◇ X2) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))))))) (congrArg (· ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0)))) ((p10848 X0 X1 ((X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))))).symm))
      _ = ((X3 ◇ X3) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0)))) := p5 ((X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0)))) ((X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0)))) X2 X3
  have p11053 : ∀ (x y z : G), ((x ◇ x) ◇ (y ◇ (y ◇ ((z ◇ z) ◇ y)))) = (y ◇ ((z ◇ z) ◇ y)) := by
    intro x y z
    simpa only [p10848, p3] using ((p11053x y z x x).symm)
  have p10847x : ∀ (X0 X1 X2 X3 X4 : G), (((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X1)))) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X3 ◇ X3)))) = ((X4 ◇ X4) ◇ X1) := by
    intro X0 X1 X2 X3 X4
    calc (((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X1)))) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X3 ◇ X3))))
      _ = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X4 ◇ X4) ◇ X1))) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X3 ◇ X3)))) := congrArg (· ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X3 ◇ X3)))) (congrArg ((X0 ◇ X0) ◇ ·) ((p10252 X0 X4 X1 X2).symm))
      _ = ((X4 ◇ X4) ◇ X1) := p105 ((X0 ◇ X0)) (((X4 ◇ X4) ◇ X1)) X3
  have p10847 : ∀ (x y z u w : G), (((x ◇ x) ◇ (y ◇ (y ◇ ((z ◇ z) ◇ y)))) ◇ (u ◇ u)) = ((w ◇ w) ◇ y) := by
    intro x y z u w
    simpa only [p39] using (p10847x x y z u w)
  have p11129 : ∀ (x y z u : G), ((x ◇ ((y ◇ y) ◇ x)) ◇ (z ◇ z)) = ((u ◇ u) ◇ x) := by
    intro x y z u
    calc ((x ◇ ((y ◇ y) ◇ x)) ◇ (z ◇ z))
      _ = (((x ◇ x) ◇ (x ◇ (x ◇ ((y ◇ y) ◇ x)))) ◇ (z ◇ z)) := congrArg (· ◇ (z ◇ z)) ((p11053 x x y).symm)
      _ = ((u ◇ u) ◇ x) := p10847 x x y z u
  have p11467 : ∀ (x y z u : G), ((x ◇ ((y ◇ y) ◇ x)) ◇ (z ◇ z)) = (x ◇ (x ◇ (u ◇ u))) := by
    intro x y z u
    calc ((x ◇ ((y ◇ y) ◇ x)) ◇ (z ◇ z))
      _ = ((x ◇ x) ◇ x) := ((p11129 x y z x).symm).symm
      _ = (x ◇ (x ◇ (u ◇ u))) := p96 x x u
  have p13422 : ∀ (x y z u : G), ((x ◇ (x ◇ (x ◇ (y ◇ y)))) ◇ (z ◇ z)) = (x ◇ (x ◇ (u ◇ u))) := by
    intro x y z u
    calc ((x ◇ (x ◇ (x ◇ (y ◇ y)))) ◇ (z ◇ z))
      _ = ((x ◇ ((x ◇ x) ◇ x)) ◇ (z ◇ z)) := congrArg (· ◇ (z ◇ z)) (congrArg (x ◇ ·) ((p96 x x y).symm))
      _ = (x ◇ (x ◇ (u ◇ u))) := p11467 x x z u
  have p143 : ∀ (x y z u : G), (((x ◇ x) ◇ (y ◇ (y ◇ (z ◇ z)))) ◇ (u ◇ u)) = y := by
    intro x y z u
    calc (((x ◇ x) ◇ (y ◇ (y ◇ (z ◇ z)))) ◇ (u ◇ u))
      _ = (((x ◇ x) ◇ ((x ◇ x) ◇ y)) ◇ (u ◇ u)) := congrArg (· ◇ (u ◇ u)) (congrArg ((x ◇ x) ◇ ·) ((p96 x y z).symm))
      _ = y := p78 x y u
  have p13567x : ∀ (X0 X1 X2 X3 X4 X5 : G), (((X0 ◇ X0) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X1 ◇ (X3 ◇ X3))))) ◇ (X4 ◇ X4)) = (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) := by
    intro X0 X1 X2 X3 X4 X5
    calc (((X0 ◇ X0) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X1 ◇ (X3 ◇ X3))))) ◇ (X4 ◇ X4))
      _ = (((X0 ◇ X0) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X5 ◇ X5)))) ◇ (X4 ◇ X4)) := congrArg (· ◇ (X4 ◇ X4)) (congrArg ((X0 ◇ X0) ◇ ·) (congrArg ((X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ ·) ((p13422 X1 X2 X5 X3).symm)))
      _ = (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) := p143 X0 ((X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2))))) X5 X4
  have p13567 : ∀ (x y z u : G), (((x ◇ x) ◇ (y ◇ (z ◇ z))) ◇ (u ◇ u)) = (y ◇ (y ◇ (y ◇ (z ◇ z)))) := by
    intro x y z u
    simpa only [p105] using (p13567x x y z x u x)
  have p11447 : ∀ (x y z u : G), ((x ◇ (x ◇ y)) ◇ ((x ◇ ((z ◇ z) ◇ x)) ◇ (u ◇ u))) = y := by
    intro x y z u
    calc ((x ◇ (x ◇ y)) ◇ ((x ◇ ((z ◇ z) ◇ x)) ◇ (u ◇ u)))
      _ = ((x ◇ (x ◇ y)) ◇ ((x ◇ x) ◇ x)) := congrArg ((x ◇ (x ◇ y)) ◇ ·) (((p11129 x z u x).symm).symm)
      _ = y := p3 x y x
  have p12985 : ∀ (x y z u : G), ((x ◇ (x ◇ y)) ◇ ((x ◇ (x ◇ (x ◇ (z ◇ z)))) ◇ (u ◇ u))) = y := by
    intro x y z u
    calc ((x ◇ (x ◇ y)) ◇ ((x ◇ (x ◇ (x ◇ (z ◇ z)))) ◇ (u ◇ u)))
      _ = ((x ◇ (x ◇ y)) ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ (u ◇ u))) := congrArg ((x ◇ (x ◇ y)) ◇ ·) (congrArg (· ◇ (u ◇ u)) (congrArg (x ◇ ·) ((p96 x x z).symm)))
      _ = y := p11447 x y x u
  have p13568x : ∀ (X0 X1 X2 X3 X4 X5 : G), (((X0 ◇ X0) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X3 ◇ X3))) ◇ (X4 ◇ X4)) = X1 := by
    intro X0 X1 X2 X3 X4 X5
    calc (((X0 ◇ X0) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X3 ◇ X3))) ◇ (X4 ◇ X4))
      _ = (((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ (X5 ◇ X5)))) ◇ (X4 ◇ X4)) := congrArg (· ◇ (X4 ◇ X4)) (congrArg ((X0 ◇ X0) ◇ ·) (((p13422 X1 X2 X3 X5).symm).symm))
      _ = X1 := p143 X0 X1 X5 X4
  have p13568 : ∀ (x y : G), ((x ◇ (x ◇ (x ◇ (y ◇ y)))) ◇ (x ◇ (y ◇ y))) = x := by
    intro x y
    simpa only [p13567, p12985] using (p13568x x x y x x x)
  have p13943 : ∀ (x y z : G), ((x ◇ ((y ◇ y) ◇ x)) ◇ (x ◇ (z ◇ z))) = x := by
    intro x y z
    calc ((x ◇ ((y ◇ y) ◇ x)) ◇ (x ◇ (z ◇ z)))
      _ = ((x ◇ (x ◇ (x ◇ (z ◇ z)))) ◇ (x ◇ (z ◇ z))) := congrArg (· ◇ (x ◇ (z ◇ z))) (congrArg (x ◇ ·) (((p96 y x z).symm).symm))
      _ = x := p13568 x z
  have p14052 : ∀ (x y z u : G), ((x ◇ ((y ◇ y) ◇ x)) ◇ ((x ◇ ((z ◇ z) ◇ x)) ◇ (x ◇ (x ◇ (u ◇ u))))) = x := by
    intro x y z u
    calc ((x ◇ ((y ◇ y) ◇ x)) ◇ ((x ◇ ((z ◇ z) ◇ x)) ◇ (x ◇ (x ◇ (u ◇ u)))))
      _ = ((x ◇ ((y ◇ y) ◇ x)) ◇ (x ◇ (x ◇ x))) := congrArg ((x ◇ ((y ◇ y) ◇ x)) ◇ ·) (((p156 x z u x).symm).symm)
      _ = x := p13943 x y x
  have p6547 : ∀ (x y z u w v5 : G), ((((x ◇ ((y ◇ y) ◇ x)) ◇ (x ◇ (z ◇ z))) ◇ (x ◇ (x ◇ (u ◇ u)))) ◇ ((w ◇ w) ◇ ((x ◇ ((y ◇ y) ◇ x)) ◇ ((x ◇ ((y ◇ y) ◇ x)) ◇ (x ◇ (x ◇ (u ◇ u))))))) = ((v5 ◇ v5) ◇ (x ◇ ((y ◇ y) ◇ x))) := by
    intro x y z u w v5
    calc ((((x ◇ ((y ◇ y) ◇ x)) ◇ (x ◇ (z ◇ z))) ◇ (x ◇ (x ◇ (u ◇ u)))) ◇ ((w ◇ w) ◇ ((x ◇ ((y ◇ y) ◇ x)) ◇ ((x ◇ ((y ◇ y) ◇ x)) ◇ (x ◇ (x ◇ (u ◇ u)))))))
      _ = ((((x ◇ ((y ◇ y) ◇ x)) ◇ ((x ◇ ((y ◇ y) ◇ x)) ◇ (x ◇ (x ◇ (u ◇ u))))) ◇ (x ◇ (x ◇ (u ◇ u)))) ◇ ((w ◇ w) ◇ ((x ◇ ((y ◇ y) ◇ x)) ◇ ((x ◇ ((y ◇ y) ◇ x)) ◇ (x ◇ (x ◇ (u ◇ u))))))) := congrArg (· ◇ ((w ◇ w) ◇ ((x ◇ ((y ◇ y) ◇ x)) ◇ ((x ◇ ((y ◇ y) ◇ x)) ◇ (x ◇ (x ◇ (u ◇ u))))))) (congrArg (· ◇ (x ◇ (x ◇ (u ◇ u)))) (congrArg ((x ◇ ((y ◇ y) ◇ x)) ◇ ·) ((p156 x y u z).symm)))
      _ = ((v5 ◇ v5) ◇ (x ◇ ((y ◇ y) ◇ x))) := p5 ((x ◇ ((y ◇ y) ◇ x))) ((x ◇ (x ◇ (u ◇ u)))) w v5
  have p14004 : ∀ (x y z u w : G), ((x ◇ (x ◇ (x ◇ (y ◇ y)))) ◇ ((z ◇ z) ◇ ((x ◇ ((u ◇ u) ◇ x)) ◇ ((x ◇ ((u ◇ u) ◇ x)) ◇ (x ◇ (x ◇ (y ◇ y))))))) = ((w ◇ w) ◇ (x ◇ ((u ◇ u) ◇ x))) := by
    intro x y z u w
    calc ((x ◇ (x ◇ (x ◇ (y ◇ y)))) ◇ ((z ◇ z) ◇ ((x ◇ ((u ◇ u) ◇ x)) ◇ ((x ◇ ((u ◇ u) ◇ x)) ◇ (x ◇ (x ◇ (y ◇ y)))))))
      _ = ((((x ◇ ((u ◇ u) ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (x ◇ (x ◇ (y ◇ y)))) ◇ ((z ◇ z) ◇ ((x ◇ ((u ◇ u) ◇ x)) ◇ ((x ◇ ((u ◇ u) ◇ x)) ◇ (x ◇ (x ◇ (y ◇ y))))))) := congrArg (· ◇ ((z ◇ z) ◇ ((x ◇ ((u ◇ u) ◇ x)) ◇ ((x ◇ ((u ◇ u) ◇ x)) ◇ (x ◇ (x ◇ (y ◇ y))))))) (congrArg (· ◇ (x ◇ (x ◇ (y ◇ y)))) ((p13943 x u x).symm))
      _ = ((w ◇ w) ◇ (x ◇ ((u ◇ u) ◇ x))) := p6547 x u x y z w
  have p14090 : ∀ (x y z u : G), ((x ◇ x) ◇ (y ◇ ((z ◇ z) ◇ y))) = (y ◇ (u ◇ u)) := by
    intro x y z u
    calc ((x ◇ x) ◇ (y ◇ ((z ◇ z) ◇ y)))
      _ = ((y ◇ (y ◇ (y ◇ (u ◇ u)))) ◇ ((x ◇ x) ◇ ((y ◇ ((z ◇ z) ◇ y)) ◇ ((y ◇ ((z ◇ z) ◇ y)) ◇ (y ◇ (y ◇ (u ◇ u))))))) := (p14004 y u x z x).symm
      _ = ((y ◇ (y ◇ (y ◇ (u ◇ u)))) ◇ ((x ◇ x) ◇ y)) := congrArg ((y ◇ (y ◇ (y ◇ (u ◇ u)))) ◇ ·) (congrArg ((x ◇ x) ◇ ·) (p14052 y z z u))
      _ = (y ◇ (u ◇ u)) := ((p3 y ((y ◇ (u ◇ u))) x).symm).symm
  have p106 : ∀ (x y z u : G), ((x ◇ ((y ◇ y) ◇ x)) ◇ ((z ◇ z) ◇ x)) = (x ◇ (u ◇ u)) := by
    intro x y z u
    calc ((x ◇ ((y ◇ y) ◇ x)) ◇ ((z ◇ z) ◇ x))
      _ = ((x ◇ (x ◇ (x ◇ (u ◇ u)))) ◇ ((z ◇ z) ◇ x)) := congrArg (· ◇ ((z ◇ z) ◇ x)) (congrArg (x ◇ ·) (((p96 y x u).symm).symm))
      _ = (x ◇ (u ◇ u)) := p3 x ((x ◇ (u ◇ u))) z
  have p14043 : ∀ (x y z u : G), ((x ◇ ((y ◇ y) ◇ x)) ◇ ((x ◇ ((z ◇ z) ◇ x)) ◇ ((u ◇ u) ◇ x))) = x := by
    intro x y z u
    calc ((x ◇ ((y ◇ y) ◇ x)) ◇ ((x ◇ ((z ◇ z) ◇ x)) ◇ ((u ◇ u) ◇ x)))
      _ = ((x ◇ ((y ◇ y) ◇ x)) ◇ (x ◇ (x ◇ x))) := congrArg ((x ◇ ((y ◇ y) ◇ x)) ◇ ·) (((p106 x z u x).symm).symm)
      _ = x := p13943 x y x
  have p11054x : ∀ (X0 X1 X2 X3 X4 : G), ((((X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) ◇ (X2 ◇ X2))) ◇ (X2 ◇ X2)) ◇ ((X3 ◇ X3) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) ◇ X0))) = ((X4 ◇ X4) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0)))) := by
    intro X0 X1 X2 X3 X4
    calc ((((X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) ◇ (X2 ◇ X2))) ◇ (X2 ◇ X2)) ◇ ((X3 ◇ X3) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) ◇ X0)))
      _ = ((((X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) ◇ (X2 ◇ X2))) ◇ (X2 ◇ X2)) ◇ ((X3 ◇ X3) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) ◇ (X2 ◇ X2))))) := congrArg ((((X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) ◇ (X2 ◇ X2))) ◇ (X2 ◇ X2)) ◇ ·) (congrArg ((X3 ◇ X3) ◇ ·) (congrArg ((X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) ◇ ·) ((p10848 X0 X1 X2).symm)))
      _ = ((X4 ◇ X4) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0)))) := p5 ((X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0)))) ((X2 ◇ X2)) X3 X4
  have p11054 : ∀ (x y : G), ((x ◇ (x ◇ ((y ◇ y) ◇ x))) ◇ x) = (x ◇ ((y ◇ y) ◇ x)) := by
    intro x y
    simpa only [p10848, p77, p11053] using (p11054x x y x x x)
  have p11777 : ∀ (x y z : G), (x ◇ ((y ◇ y) ◇ x)) = (x ◇ (x ◇ (x ◇ (z ◇ z)))) := by
    intro x y z
    calc (x ◇ ((y ◇ y) ◇ x))
      _ = (x ◇ (x ◇ (x ◇ (z ◇ z)))) := congrArg (x ◇ ·) (p96 y x z)
  have p12387 : ∀ (x y z u : G), ((x ◇ ((y ◇ y) ◇ x)) ◇ ((z ◇ z) ◇ (x ◇ ((y ◇ y) ◇ x)))) = ((x ◇ ((y ◇ y) ◇ x)) ◇ ((x ◇ ((y ◇ y) ◇ x)) ◇ ((u ◇ u) ◇ x))) := by
    intro x y z u
    calc ((x ◇ ((y ◇ y) ◇ x)) ◇ ((z ◇ z) ◇ (x ◇ ((y ◇ y) ◇ x))))
      _ = ((x ◇ ((y ◇ y) ◇ x)) ◇ ((x ◇ ((y ◇ y) ◇ x)) ◇ ((x ◇ ((y ◇ y) ◇ x)) ◇ (x ◇ x)))) := ((p11777 ((x ◇ ((y ◇ y) ◇ x))) z x).symm).symm
      _ = ((x ◇ ((y ◇ y) ◇ x)) ◇ ((x ◇ ((y ◇ y) ◇ x)) ◇ ((u ◇ u) ◇ x))) := congrArg ((x ◇ ((y ◇ y) ◇ x)) ◇ ·) (congrArg ((x ◇ ((y ◇ y) ◇ x)) ◇ ·) (p11129 x y x u))
  have p14088 : ∀ (x y z : G), ((x ◇ ((y ◇ y) ◇ x)) ◇ ((z ◇ z) ◇ (x ◇ ((y ◇ y) ◇ x)))) = x := by
    intro x y z
    calc ((x ◇ ((y ◇ y) ◇ x)) ◇ ((z ◇ z) ◇ (x ◇ ((y ◇ y) ◇ x))))
      _ = ((x ◇ ((y ◇ y) ◇ x)) ◇ ((x ◇ ((y ◇ y) ◇ x)) ◇ ((x ◇ x) ◇ x))) := ((p12387 x y z x).symm).symm
      _ = x := p14043 x y y x
  have p14330x : ∀ (X0 X1 X2 X3 X4 : G), ((X0 ◇ X0) ◇ ((X1 ◇ ((X2 ◇ X2) ◇ X1)) ◇ ((X1 ◇ ((X2 ◇ X2) ◇ X1)) ◇ (X1 ◇ (X3 ◇ X3))))) = ((X1 ◇ ((X2 ◇ X2) ◇ X1)) ◇ ((X4 ◇ X4) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X1)))) := by
    intro X0 X1 X2 X3 X4
    calc ((X0 ◇ X0) ◇ ((X1 ◇ ((X2 ◇ X2) ◇ X1)) ◇ ((X1 ◇ ((X2 ◇ X2) ◇ X1)) ◇ (X1 ◇ (X3 ◇ X3)))))
      _ = ((X0 ◇ X0) ◇ ((X1 ◇ ((X2 ◇ X2) ◇ X1)) ◇ ((X1 ◇ ((X2 ◇ X2) ◇ X1)) ◇ ((X4 ◇ X4) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X1)))))) := congrArg ((X0 ◇ X0) ◇ ·) (congrArg ((X1 ◇ ((X2 ◇ X2) ◇ X1)) ◇ ·) (congrArg ((X1 ◇ ((X2 ◇ X2) ◇ X1)) ◇ ·) ((p14090 X4 X1 X2 X3).symm)))
      _ = ((X1 ◇ ((X2 ◇ X2) ◇ X1)) ◇ ((X4 ◇ X4) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X1)))) := p11053 X0 ((X1 ◇ ((X2 ◇ X2) ◇ X1))) X4
  have p14330 : ∀ (x y z : G), ((x ◇ x) ◇ ((y ◇ ((z ◇ z) ◇ y)) ◇ y)) = y := by
    intro x y z
    simpa only [p13943, p14088] using (p14330x x y z x x)
  have p10821 : ∀ (x y z u w : G), (((x ◇ x) ◇ ((y ◇ y) ◇ z)) ◇ ((u ◇ u) ◇ z)) = ((w ◇ w) ◇ z) := by
    intro x y z u w
    calc (((x ◇ x) ◇ ((y ◇ y) ◇ z)) ◇ ((u ◇ u) ◇ z))
      _ = ((z ◇ (z ◇ ((w ◇ w) ◇ z))) ◇ ((u ◇ u) ◇ z)) := congrArg (· ◇ ((u ◇ u) ◇ z)) (((p10252 x y z w).symm).symm)
      _ = ((w ◇ w) ◇ z) := p3 z (((w ◇ w) ◇ z)) u
  have p15067x : ∀ (X0 X1 X2 X3 X4 X5 : G), (((X0 ◇ X0) ◇ X1) ◇ ((X2 ◇ X2) ◇ ((X1 ◇ ((X3 ◇ X3) ◇ X1)) ◇ X1))) = ((X4 ◇ X4) ◇ ((X1 ◇ ((X3 ◇ X3) ◇ X1)) ◇ X1)) := by
    intro X0 X1 X2 X3 X4 X5
    calc (((X0 ◇ X0) ◇ X1) ◇ ((X2 ◇ X2) ◇ ((X1 ◇ ((X3 ◇ X3) ◇ X1)) ◇ X1)))
      _ = (((X0 ◇ X0) ◇ ((X5 ◇ X5) ◇ ((X1 ◇ ((X3 ◇ X3) ◇ X1)) ◇ X1))) ◇ ((X2 ◇ X2) ◇ ((X1 ◇ ((X3 ◇ X3) ◇ X1)) ◇ X1))) := congrArg (· ◇ ((X2 ◇ X2) ◇ ((X1 ◇ ((X3 ◇ X3) ◇ X1)) ◇ X1))) (congrArg ((X0 ◇ X0) ◇ ·) ((p14330 X5 X1 X3).symm))
      _ = ((X4 ◇ X4) ◇ ((X1 ◇ ((X3 ◇ X3) ◇ X1)) ◇ X1)) := p10821 X0 X5 (((X1 ◇ ((X3 ◇ X3) ◇ X1)) ◇ X1)) X2 X4
  have p15067 : ∀ (x y : G), (((x ◇ x) ◇ y) ◇ y) = y := by
    intro x y
    simpa only [p14330, p14330] using (p15067x x y x x x x)
  exact congrArg (fun t => t ◇ y) (p15067 z x).symm

end submission


def submission : Goal := submission.certificate

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_22618_to_53590 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_22618_to_53590
