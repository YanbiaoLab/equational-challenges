-- Equation6711 → Equation41582
-- Recorded verdict: true
-- Premise: x = y ◇ (x ◇ ((y ◇ z) ◇ (x ◇ z)))
-- Conclusion: x ◇ x = y ◇ (x ◇ (x ◇ (x ◇ y)))
-- Original submission SHA-256: 3f8396c167cb271ca166ee2d6fe20a50337a8bafa7eab4009631d38d05bd33a0
-- Aurora-accepted correction SHA-256: fcdd31bfe48429cb5a371f6a6c5706e7299cf0b30d998f51fc7bd709ba8c1fdf
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (x ◇ ((y ◇ z) ◇ (x ◇ z)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ x = y ◇ (x ◇ (x ◇ (x ◇ y)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Aurora-accepted corrected submission body
                   

namespace submission

set_option linter.unusedVariables false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

def certificate : Goal := by
  intro G _ h
  intro x y
  have p3 : ∀ (x y z : G), (x ◇ (y ◇ ((x ◇ z) ◇ (y ◇ z)))) = y := by
    intro x y z
    exact (h y x z).symm
  have p5 : ∀ (x y z u : G), (x ◇ (y ◇ (z ◇ (y ◇ (z ◇ ((x ◇ u) ◇ (z ◇ u))))))) = y := by
    intro x y z u
    calc (x ◇ (y ◇ (z ◇ (y ◇ (z ◇ ((x ◇ u) ◇ (z ◇ u)))))))
      _ = (x ◇ (y ◇ ((x ◇ (z ◇ ((x ◇ u) ◇ (z ◇ u)))) ◇ (y ◇ (z ◇ ((x ◇ u) ◇ (z ◇ u))))))) := congrArg (x ◇ ·) (congrArg (y ◇ ·) (congrArg (· ◇ (y ◇ (z ◇ ((x ◇ u) ◇ (z ◇ u))))) ((p3 x z u).symm)))
      _ = y := p3 x y ((z ◇ ((x ◇ u) ◇ (z ◇ u))))
  have p10 : ∀ (x y : G), (x ◇ (x ◇ (y ◇ y))) = x := by
    intro x y
    calc (x ◇ (x ◇ (y ◇ y)))
      _ = (x ◇ (x ◇ (y ◇ (x ◇ (y ◇ ((x ◇ x) ◇ (y ◇ x))))))) := congrArg (x ◇ ·) (congrArg (x ◇ ·) (congrArg (y ◇ ·) ((p3 x y x).symm)))
      _ = x := p5 x x y x
  have p14 : ∀ (x y z : G), (x ◇ (y ◇ (x ◇ (y ◇ (x ◇ (z ◇ z)))))) = y := by
    intro x y z
    calc (x ◇ (y ◇ (x ◇ (y ◇ (x ◇ (z ◇ z))))))
      _ = (x ◇ (y ◇ ((x ◇ (x ◇ (z ◇ z))) ◇ (y ◇ (x ◇ (z ◇ z)))))) := congrArg (x ◇ ·) (congrArg (y ◇ ·) (congrArg (· ◇ (y ◇ (x ◇ (z ◇ z)))) ((p10 x z).symm)))
      _ = y := p3 x y ((x ◇ (z ◇ z)))
  have p28 : ∀ (x y : G), (x ◇ x) = (y ◇ y) := by
    intro x y
    calc (x ◇ x)
      _ = (x ◇ ((y ◇ y) ◇ (x ◇ ((y ◇ y) ◇ (x ◇ ((y ◇ y) ◇ (y ◇ y))))))) := congrArg (x ◇ ·) ((p14 ((y ◇ y)) x y).symm)
      _ = (y ◇ y) := p14 x ((y ◇ y)) ((y ◇ y))
  have p29 : ∀ (x y z : G), (x ◇ (y ◇ ((z ◇ z) ◇ (y ◇ x)))) = y := by
    intro x y z
    calc (x ◇ (y ◇ ((z ◇ z) ◇ (y ◇ x))))
      _ = (x ◇ (y ◇ ((x ◇ x) ◇ (y ◇ x)))) := congrArg (x ◇ ·) (congrArg (y ◇ ·) (congrArg (· ◇ (y ◇ x)) ((p28 x z).symm)))
      _ = y := p3 x y x
  have p59 : ∀ (x y z : G), ((((x ◇ x) ◇ y) ◇ (z ◇ y)) ◇ (z ◇ z)) = z := by
    intro x y z
    calc ((((x ◇ x) ◇ y) ◇ (z ◇ y)) ◇ (z ◇ z))
      _ = ((((x ◇ x) ◇ y) ◇ (z ◇ y)) ◇ (z ◇ ((x ◇ x) ◇ (z ◇ (((x ◇ x) ◇ y) ◇ (z ◇ y)))))) := congrArg ((((x ◇ x) ◇ y) ◇ (z ◇ y)) ◇ ·) (congrArg (z ◇ ·) ((p3 ((x ◇ x)) z y).symm))
      _ = z := p29 ((((x ◇ x) ◇ y) ◇ (z ◇ y))) z x
  have p30 : ∀ (x y z : G), (x ◇ (y ◇ ((x ◇ y) ◇ (z ◇ z)))) = y := by
    intro x y z
    calc (x ◇ (y ◇ ((x ◇ y) ◇ (z ◇ z))))
      _ = (x ◇ (y ◇ ((x ◇ y) ◇ (y ◇ y)))) := congrArg (x ◇ ·) (congrArg (y ◇ ·) (congrArg ((x ◇ y) ◇ ·) ((p28 y z).symm)))
      _ = y := p3 x y y
  have p140 : ∀ (x y z : G), (((x ◇ x) ◇ y) ◇ ((z ◇ y) ◇ z)) = (z ◇ y) := by
    intro x y z
    calc (((x ◇ x) ◇ y) ◇ ((z ◇ y) ◇ z))
      _ = (((x ◇ x) ◇ y) ◇ ((z ◇ y) ◇ ((((x ◇ x) ◇ y) ◇ (z ◇ y)) ◇ (z ◇ z)))) := congrArg (((x ◇ x) ◇ y) ◇ ·) (congrArg ((z ◇ y) ◇ ·) ((p59 x y z).symm))
      _ = (z ◇ y) := p30 (((x ◇ x) ◇ y)) ((z ◇ y)) z
  have p6 : ∀ (x y z u : G), (x ◇ (y ◇ ((x ◇ (z ◇ ((y ◇ u) ◇ (z ◇ u)))) ◇ z))) = y := by
    intro x y z u
    calc (x ◇ (y ◇ ((x ◇ (z ◇ ((y ◇ u) ◇ (z ◇ u)))) ◇ z)))
      _ = (x ◇ (y ◇ ((x ◇ (z ◇ ((y ◇ u) ◇ (z ◇ u)))) ◇ (y ◇ (z ◇ ((y ◇ u) ◇ (z ◇ u))))))) := congrArg (x ◇ ·) (congrArg (y ◇ ·) (congrArg ((x ◇ (z ◇ ((y ◇ u) ◇ (z ◇ u)))) ◇ ·) ((p3 y z u).symm)))
      _ = y := p3 x y ((z ◇ ((y ◇ u) ◇ (z ◇ u))))
  have p49 : ∀ (x y z u : G), ((x ◇ ((y ◇ z) ◇ (x ◇ z))) ◇ (y ◇ ((u ◇ u) ◇ x))) = y := by
    intro x y z u
    calc ((x ◇ ((y ◇ z) ◇ (x ◇ z))) ◇ (y ◇ ((u ◇ u) ◇ x)))
      _ = ((x ◇ ((y ◇ z) ◇ (x ◇ z))) ◇ (y ◇ (((x ◇ ((y ◇ z) ◇ (x ◇ z))) ◇ (x ◇ ((y ◇ z) ◇ (x ◇ z)))) ◇ x))) := congrArg ((x ◇ ((y ◇ z) ◇ (x ◇ z))) ◇ ·) (congrArg (y ◇ ·) (congrArg (· ◇ x) ((p28 ((x ◇ ((y ◇ z) ◇ (x ◇ z)))) u).symm)))
      _ = y := p6 ((x ◇ ((y ◇ z) ◇ (x ◇ z)))) y x z
  have p1262x : ∀ (X0 X1 X2 X3 X4 : G), (((X0 ◇ X0) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X3))) ◇ (X1 ◇ (X3 ◇ ((X1 ◇ X4) ◇ (X3 ◇ X4))))) = ((X3 ◇ ((X1 ◇ X4) ◇ (X3 ◇ X4))) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X3))) := by
    intro X0 X1 X2 X3 X4
    calc (((X0 ◇ X0) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X3))) ◇ (X1 ◇ (X3 ◇ ((X1 ◇ X4) ◇ (X3 ◇ X4)))))
      _ = (((X0 ◇ X0) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X3))) ◇ (((X3 ◇ ((X1 ◇ X4) ◇ (X3 ◇ X4))) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X3))) ◇ (X3 ◇ ((X1 ◇ X4) ◇ (X3 ◇ X4))))) := congrArg (((X0 ◇ X0) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X3))) ◇ ·) (congrArg (· ◇ (X3 ◇ ((X1 ◇ X4) ◇ (X3 ◇ X4)))) ((p49 X3 X1 X4 X2).symm))
      _ = ((X3 ◇ ((X1 ◇ X4) ◇ (X3 ◇ X4))) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X3))) := p140 X0 ((X1 ◇ ((X2 ◇ X2) ◇ X3))) ((X3 ◇ ((X1 ◇ X4) ◇ (X3 ◇ X4))))
  have p1262 : ∀ (x y z u : G), (((x ◇ x) ◇ (y ◇ ((z ◇ z) ◇ u))) ◇ u) = y := by
    intro x y z u
    simpa only [p3, p49] using (p1262x x y z u x)
  have p35 : ∀ (x y : G), ((x ◇ x) ◇ (y ◇ y)) = (x ◇ x) := by
    intro x y
    calc ((x ◇ x) ◇ (y ◇ y))
      _ = ((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) := congrArg ((x ◇ x) ◇ ·) ((p28 ((x ◇ x)) y).symm)
      _ = (x ◇ x) := p10 ((x ◇ x)) x
  have p125 : ∀ (x y z : G), ((((x ◇ x) ◇ y) ◇ (z ◇ y)) ◇ z) = (((x ◇ x) ◇ y) ◇ (z ◇ y)) := by
    intro x y z
    calc ((((x ◇ x) ◇ y) ◇ (z ◇ y)) ◇ z)
      _ = ((((x ◇ x) ◇ y) ◇ (z ◇ y)) ◇ ((((x ◇ x) ◇ y) ◇ (z ◇ y)) ◇ (z ◇ z))) := congrArg ((((x ◇ x) ◇ y) ◇ (z ◇ y)) ◇ ·) ((p59 x y z).symm)
      _ = (((x ◇ x) ◇ y) ◇ (z ◇ y)) := p10 ((((x ◇ x) ◇ y) ◇ (z ◇ y))) z
  have p135 : ∀ (x y z : G), (((x ◇ x) ◇ y) ◇ ((z ◇ z) ◇ y)) = (z ◇ z) := by
    intro x y z
    calc (((x ◇ x) ◇ y) ◇ ((z ◇ z) ◇ y))
      _ = ((((x ◇ x) ◇ y) ◇ ((z ◇ z) ◇ y)) ◇ (z ◇ z)) := (p125 x y ((z ◇ z))).symm
      _ = ((((x ◇ x) ◇ y) ◇ ((z ◇ z) ◇ y)) ◇ ((z ◇ z) ◇ (z ◇ z))) := congrArg ((((x ◇ x) ◇ y) ◇ ((z ◇ z) ◇ y)) ◇ ·) ((p35 z z).symm)
      _ = (z ◇ z) := ((p59 x y ((z ◇ z))).symm).symm
  have p33 : ∀ (x y z u : G), (x ◇ (y ◇ (z ◇ (y ◇ (z ◇ ((x ◇ z) ◇ (u ◇ u))))))) = y := by
    intro x y z u
    calc (x ◇ (y ◇ (z ◇ (y ◇ (z ◇ ((x ◇ z) ◇ (u ◇ u)))))))
      _ = (x ◇ (y ◇ (z ◇ (y ◇ (z ◇ ((x ◇ z) ◇ (z ◇ z))))))) := congrArg (x ◇ ·) (congrArg (y ◇ ·) (congrArg (z ◇ ·) (congrArg (y ◇ ·) (congrArg (z ◇ ·) (congrArg ((x ◇ z) ◇ ·) ((p28 z u).symm))))))
      _ = y := p5 x y z z
  have p68 : ∀ (x y z : G), (((x ◇ x) ◇ (y ◇ (z ◇ z))) ◇ (x ◇ x)) = y := by
    intro x y z
    calc (((x ◇ x) ◇ (y ◇ (z ◇ z))) ◇ (x ◇ x))
      _ = (((x ◇ x) ◇ (y ◇ (z ◇ z))) ◇ (y ◇ ((x ◇ x) ◇ (y ◇ ((x ◇ x) ◇ (y ◇ (z ◇ z))))))) := congrArg (((x ◇ x) ◇ (y ◇ (z ◇ z))) ◇ ·) ((p14 y ((x ◇ x)) z).symm)
      _ = y := p29 (((x ◇ x) ◇ (y ◇ (z ◇ z)))) y x
  have p179 : ∀ (x y z u : G), (((x ◇ x) ◇ (y ◇ (z ◇ z))) ◇ (u ◇ u)) = y := by
    intro x y z u
    calc (((x ◇ x) ◇ (y ◇ (z ◇ z))) ◇ (u ◇ u))
      _ = (((u ◇ u) ◇ (y ◇ (z ◇ z))) ◇ (u ◇ u)) := congrArg (· ◇ (u ◇ u)) (congrArg (· ◇ (y ◇ (z ◇ z))) ((p28 u x).symm))
      _ = y := p68 u y z
  have p957x : ∀ (X0 X1 X2 X3 : G), (X0 ◇ (((X1 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3))) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2)))) = ((X1 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3))) := by
    intro X0 X1 X2 X3
    calc (X0 ◇ (((X1 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3))) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))))
      _ = (X0 ◇ (((X1 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3))) ◇ ((X2 ◇ X2) ◇ (((X1 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3))) ◇ ((X2 ◇ X2) ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3))))))) := congrArg (X0 ◇ ·) (congrArg (((X1 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3))) ◇ ·) (congrArg ((X2 ◇ X2) ◇ ·) ((p135 X1 (((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3))) X2).symm)))
      _ = ((X1 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3))) := p33 X0 (((X1 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3)))) ((X2 ◇ X2)) X3
  have p957 : ∀ (x y z u : G), ((x ◇ x) ◇ ((y ◇ (z ◇ z)) ◇ (u ◇ u))) = y := by
    intro x y z u
    simpa only [p35, p179, p10] using ((p957x y x z u).symm)
  have p130 : ∀ (x y z u : G), ((((x ◇ x) ◇ y) ◇ (z ◇ y)) ◇ (u ◇ u)) = z := by
    intro x y z u
    calc ((((x ◇ x) ◇ y) ◇ (z ◇ y)) ◇ (u ◇ u))
      _ = ((((x ◇ x) ◇ y) ◇ (z ◇ y)) ◇ (z ◇ z)) := congrArg ((((x ◇ x) ◇ y) ◇ (z ◇ y)) ◇ ·) ((p28 z u).symm)
      _ = z := p59 x y z
  have p1004 : ∀ (x y z u w : G), ((x ◇ (y ◇ ((x ◇ (z ◇ z)) ◇ (u ◇ u)))) ◇ (w ◇ w)) = y := by
    intro x y z u w
    calc ((x ◇ (y ◇ ((x ◇ (z ◇ z)) ◇ (u ◇ u)))) ◇ (w ◇ w))
      _ = ((((x ◇ x) ◇ ((x ◇ (z ◇ z)) ◇ (u ◇ u))) ◇ (y ◇ ((x ◇ (z ◇ z)) ◇ (u ◇ u)))) ◇ (w ◇ w)) := congrArg (· ◇ (w ◇ w)) (congrArg (· ◇ (y ◇ ((x ◇ (z ◇ z)) ◇ (u ◇ u)))) ((p957 x x z u).symm))
      _ = y := p130 x (((x ◇ (z ◇ z)) ◇ (u ◇ u))) y w
  have p2727x : ∀ (X0 X1 X2 X3 X4 X5 X6 : G), ((X0 ◇ X1) ◇ (X2 ◇ X2)) = ((X3 ◇ X3) ◇ (X1 ◇ ((X4 ◇ X4) ◇ ((X0 ◇ (X5 ◇ X5)) ◇ (X6 ◇ X6))))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    calc ((X0 ◇ X1) ◇ (X2 ◇ X2))
      _ = ((X0 ◇ (((X3 ◇ X3) ◇ (X1 ◇ ((X4 ◇ X4) ◇ ((X0 ◇ (X5 ◇ X5)) ◇ (X6 ◇ X6))))) ◇ ((X0 ◇ (X5 ◇ X5)) ◇ (X6 ◇ X6)))) ◇ (X2 ◇ X2)) := congrArg (· ◇ (X2 ◇ X2)) (congrArg (X0 ◇ ·) ((p1262 X3 X1 X4 (((X0 ◇ (X5 ◇ X5)) ◇ (X6 ◇ X6)))).symm))
      _ = ((X3 ◇ X3) ◇ (X1 ◇ ((X4 ◇ X4) ◇ ((X0 ◇ (X5 ◇ X5)) ◇ (X6 ◇ X6))))) := p1004 X0 (((X3 ◇ X3) ◇ (X1 ◇ ((X4 ◇ X4) ◇ ((X0 ◇ (X5 ◇ X5)) ◇ (X6 ◇ X6)))))) X5 X6 X2
  have p2727 : ∀ (x y z u : G), ((x ◇ y) ◇ (z ◇ z)) = ((u ◇ u) ◇ (y ◇ x)) := by
    intro x y z u
    simpa only [p957] using (p2727x x y z u x x x)
  have p3018 : ∀ (x y z u : G), (((((x ◇ x) ◇ y) ◇ z) ◇ (u ◇ u)) ◇ y) = z := by
    intro x y z u
    calc (((((x ◇ x) ◇ y) ◇ z) ◇ (u ◇ u)) ◇ y)
      _ = (((x ◇ x) ◇ (z ◇ ((x ◇ x) ◇ y))) ◇ y) := congrArg (· ◇ y) (((p2727 (((x ◇ x) ◇ y)) z u x).symm).symm)
      _ = z := p1262 x z x y
  have p3601 : ∀ (x y z : G), (((x ◇ y) ◇ (z ◇ z)) ◇ y) = ((x ◇ y) ◇ x) := by
    intro x y z
    calc (((x ◇ y) ◇ (z ◇ z)) ◇ y)
      _ = (((((x ◇ x) ◇ y) ◇ ((x ◇ y) ◇ x)) ◇ (z ◇ z)) ◇ y) := congrArg (· ◇ y) (congrArg (· ◇ (z ◇ z)) ((p140 x y x).symm))
      _ = ((x ◇ y) ◇ x) := p3018 x y (((x ◇ y) ◇ x)) z
  have p83 : ∀ (x y z : G), ((((x ◇ x) ◇ y) ◇ (z ◇ z)) ◇ (y ◇ y)) = y := by
    intro x y z
    calc ((((x ◇ x) ◇ y) ◇ (z ◇ z)) ◇ (y ◇ y))
      _ = ((((x ◇ x) ◇ y) ◇ (z ◇ z)) ◇ (y ◇ ((x ◇ x) ◇ (y ◇ (((x ◇ x) ◇ y) ◇ (z ◇ z)))))) := congrArg ((((x ◇ x) ◇ y) ◇ (z ◇ z)) ◇ ·) (congrArg (y ◇ ·) ((p30 ((x ◇ x)) y z).symm))
      _ = y := p29 ((((x ◇ x) ◇ y) ◇ (z ◇ z))) y x
  have p202 : ∀ (x y z u : G), ((((x ◇ x) ◇ y) ◇ (z ◇ z)) ◇ (u ◇ u)) = y := by
    intro x y z u
    calc ((((x ◇ x) ◇ y) ◇ (z ◇ z)) ◇ (u ◇ u))
      _ = ((((x ◇ x) ◇ y) ◇ (z ◇ z)) ◇ (y ◇ y)) := congrArg ((((x ◇ x) ◇ y) ◇ (z ◇ z)) ◇ ·) ((p28 y u).symm)
      _ = y := p83 x y z
  have p529 : ∀ (x y z u : G), (((x ◇ (y ◇ y)) ◇ (z ◇ z)) ◇ (u ◇ u)) = ((x ◇ (y ◇ y)) ◇ x) := by
    intro x y z u
    calc (((x ◇ (y ◇ y)) ◇ (z ◇ z)) ◇ (u ◇ u))
      _ = (((((y ◇ y) ◇ (y ◇ y)) ◇ ((x ◇ (y ◇ y)) ◇ x)) ◇ (z ◇ z)) ◇ (u ◇ u)) := congrArg (· ◇ (u ◇ u)) (congrArg (· ◇ (z ◇ z)) ((p140 y ((y ◇ y)) x).symm))
      _ = ((x ◇ (y ◇ y)) ◇ x) := p202 ((y ◇ y)) (((x ◇ (y ◇ y)) ◇ x)) z u
  have p2936 : ∀ (x y z : G), (((x ◇ y) ◇ (z ◇ z)) ◇ (x ◇ y)) = (y ◇ x) := by
    intro x y z
    calc (((x ◇ y) ◇ (z ◇ z)) ◇ (x ◇ y))
      _ = ((((x ◇ y) ◇ (z ◇ z)) ◇ (x ◇ x)) ◇ (x ◇ x)) := (p529 ((x ◇ y)) z x x).symm
      _ = ((((x ◇ x) ◇ (y ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ x)) := congrArg (· ◇ (x ◇ x)) (congrArg (· ◇ (x ◇ x)) (p2727 x y z x))
      _ = (y ◇ x) := p202 x ((y ◇ x)) x x
  have p4697 : ∀ (x y z : G), (x ◇ ((y ◇ x) ◇ (z ◇ z))) = (y ◇ (y ◇ x)) := by
    intro x y z
    calc (x ◇ ((y ◇ x) ◇ (z ◇ z)))
      _ = (((((y ◇ x) ◇ (z ◇ z)) ◇ x) ◇ (x ◇ x)) ◇ (((y ◇ x) ◇ (z ◇ z)) ◇ x)) := (p2936 (((y ◇ x) ◇ (z ◇ z))) x x).symm
      _ = (((((y ◇ x) ◇ (z ◇ z)) ◇ x) ◇ (x ◇ x)) ◇ ((y ◇ x) ◇ y)) := congrArg (((((y ◇ x) ◇ (z ◇ z)) ◇ x) ◇ (x ◇ x)) ◇ ·) (p3601 y x z)
      _ = ((((y ◇ x) ◇ y) ◇ (x ◇ x)) ◇ ((y ◇ x) ◇ y)) := congrArg (· ◇ ((y ◇ x) ◇ y)) (congrArg (· ◇ (x ◇ x)) (((p3601 y x z).symm).symm))
      _ = (y ◇ (y ◇ x)) := ((p2936 ((y ◇ x)) y x).symm).symm
  have p5173 : ∀ (x y : G), (x ◇ (x ◇ (x ◇ y))) = y := by
    intro x y
    simpa only [p4697] using (p30 x y x)
  calc (x ◇ x)
    _ = (y ◇ y) := p28 x y
    _ = (y ◇ (x ◇ (x ◇ (x ◇ y)))) := congrArg (fun t => y ◇ t) (p5173 x y).symm

end submission

def submission : Goal := submission.certificate

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_6711_to_41582 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_6711_to_41582
