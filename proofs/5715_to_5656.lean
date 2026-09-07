-- Equation5715 → Equation5656
-- Recorded verdict: true
-- Premise: x = x ◇ (y ◇ (z ◇ ((y ◇ x) ◇ x)))
-- Conclusion: x = x ◇ (y ◇ (x ◇ ((z ◇ w) ◇ x)))
-- Original submission SHA-256: 27a0c965461f674eb6df066624e8d5728bc8966cdc4048a0042cf456d604552a
-- Aurora-accepted correction SHA-256: 5072226aa8e77c14c20b151b3bf024d1b2faa474663f592d7db313ccdc6e49cf
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = x ◇ (y ◇ (z ◇ ((y ◇ x) ◇ x)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = x ◇ (y ◇ (x ◇ ((z ◇ w) ◇ x)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Aurora-accepted corrected submission body
                   

set_option linter.unusedVariables false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

namespace submission

def certificate : Goal := by
  intro G _ h
  intro x y z w
  have p3 : ∀ (x y z : G), (x ◇ (y ◇ (z ◇ ((y ◇ x) ◇ x)))) = x := by
    intro x y z
    exact (h x y z).symm
  have p5x : ∀ (X0 X1 X2 X3 : G), ((X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X2))) ◇ (X2 ◇ (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X2))))))) = (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X2))) := by
    intro X0 X1 X2 X3
    calc ((X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X2))) ◇ (X2 ◇ (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X2)))))))
      _ = ((X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X2))) ◇ (X2 ◇ (X3 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X2)))) ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X2))))))) := congrArg ((X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X2))) ◇ ·) (congrArg (X2 ◇ ·) (congrArg (X3 ◇ ·) (congrArg (· ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X2)))) ((p3 X2 X0 X1).symm))))
      _ = (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X2))) := p3 ((X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X2)))) X2 X3
  have p5 : ∀ (x y z u : G), ((x ◇ (y ◇ ((x ◇ z) ◇ z))) ◇ (z ◇ (u ◇ z))) = (x ◇ (y ◇ ((x ◇ z) ◇ z))) := by
    intro x y z u
    simpa only [p3] using (p5x x y z u)
  have p13 : ∀ (x y z u w v5 : G), ((x ◇ (y ◇ ((x ◇ (z ◇ (u ◇ z))) ◇ (z ◇ (u ◇ z))))) ◇ ((z ◇ (u ◇ z)) ◇ (w ◇ (v5 ◇ ((w ◇ z) ◇ z))))) = (x ◇ (y ◇ ((x ◇ (z ◇ (u ◇ z))) ◇ (z ◇ (u ◇ z))))) := by
    intro x y z u w v5
    calc ((x ◇ (y ◇ ((x ◇ (z ◇ (u ◇ z))) ◇ (z ◇ (u ◇ z))))) ◇ ((z ◇ (u ◇ z)) ◇ (w ◇ (v5 ◇ ((w ◇ z) ◇ z)))))
      _ = ((x ◇ (y ◇ ((x ◇ (z ◇ (u ◇ z))) ◇ (z ◇ (u ◇ z))))) ◇ ((z ◇ (u ◇ z)) ◇ ((w ◇ (v5 ◇ ((w ◇ z) ◇ z))) ◇ (z ◇ (u ◇ z))))) := congrArg ((x ◇ (y ◇ ((x ◇ (z ◇ (u ◇ z))) ◇ (z ◇ (u ◇ z))))) ◇ ·) (congrArg ((z ◇ (u ◇ z)) ◇ ·) ((p5 w v5 z u).symm))
      _ = (x ◇ (y ◇ ((x ◇ (z ◇ (u ◇ z))) ◇ (z ◇ (u ◇ z))))) := p5 x y ((z ◇ (u ◇ z))) ((w ◇ (v5 ◇ ((w ◇ z) ◇ z))))
  have p10 : ∀ (x y z u w : G), ((x ◇ (y ◇ ((x ◇ (z ◇ (u ◇ ((z ◇ w) ◇ w)))) ◇ (z ◇ (u ◇ ((z ◇ w) ◇ w)))))) ◇ ((z ◇ (u ◇ ((z ◇ w) ◇ w))) ◇ w)) = (x ◇ (y ◇ ((x ◇ (z ◇ (u ◇ ((z ◇ w) ◇ w)))) ◇ (z ◇ (u ◇ ((z ◇ w) ◇ w)))))) := by
    intro x y z u w
    calc ((x ◇ (y ◇ ((x ◇ (z ◇ (u ◇ ((z ◇ w) ◇ w)))) ◇ (z ◇ (u ◇ ((z ◇ w) ◇ w)))))) ◇ ((z ◇ (u ◇ ((z ◇ w) ◇ w))) ◇ w))
      _ = ((x ◇ (y ◇ ((x ◇ (z ◇ (u ◇ ((z ◇ w) ◇ w)))) ◇ (z ◇ (u ◇ ((z ◇ w) ◇ w)))))) ◇ ((z ◇ (u ◇ ((z ◇ w) ◇ w))) ◇ (w ◇ (z ◇ (u ◇ ((z ◇ w) ◇ w)))))) := congrArg ((x ◇ (y ◇ ((x ◇ (z ◇ (u ◇ ((z ◇ w) ◇ w)))) ◇ (z ◇ (u ◇ ((z ◇ w) ◇ w)))))) ◇ ·) (congrArg ((z ◇ (u ◇ ((z ◇ w) ◇ w))) ◇ ·) ((p3 w z u).symm))
      _ = (x ◇ (y ◇ ((x ◇ (z ◇ (u ◇ ((z ◇ w) ◇ w)))) ◇ (z ◇ (u ◇ ((z ◇ w) ◇ w)))))) := p5 x y ((z ◇ (u ◇ ((z ◇ w) ◇ w)))) w
  have p22x : ∀ (X0 X1 X2 X3 X4 X5 : G), (((X0 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ (X3 ◇ X2))) ◇ (X2 ◇ (X3 ◇ X2))))) ◇ (X4 ◇ ((X0 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ (X3 ◇ X2))) ◇ (X2 ◇ (X3 ◇ X2))))) ◇ ((X2 ◇ (X3 ◇ X2)) ◇ (X5 ◇ (((X2 ◇ (X3 ◇ X2)) ◇ ((X5 ◇ X2) ◇ X2)) ◇ ((X5 ◇ X2) ◇ X2))))))) ◇ (((X2 ◇ (X3 ◇ X2)) ◇ (X5 ◇ (((X2 ◇ (X3 ◇ X2)) ◇ ((X5 ◇ X2) ◇ X2)) ◇ ((X5 ◇ X2) ◇ X2)))) ◇ ((X5 ◇ X2) ◇ X2))) = ((X0 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ (X3 ◇ X2))) ◇ (X2 ◇ (X3 ◇ X2))))) ◇ (X4 ◇ (((X0 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ (X3 ◇ X2))) ◇ (X2 ◇ (X3 ◇ X2))))) ◇ ((X2 ◇ (X3 ◇ X2)) ◇ (X5 ◇ (((X2 ◇ (X3 ◇ X2)) ◇ ((X5 ◇ X2) ◇ X2)) ◇ ((X5 ◇ X2) ◇ X2))))) ◇ ((X2 ◇ (X3 ◇ X2)) ◇ (X5 ◇ (((X2 ◇ (X3 ◇ X2)) ◇ ((X5 ◇ X2) ◇ X2)) ◇ ((X5 ◇ X2) ◇ X2))))))) := by
    intro X0 X1 X2 X3 X4 X5
    calc (((X0 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ (X3 ◇ X2))) ◇ (X2 ◇ (X3 ◇ X2))))) ◇ (X4 ◇ ((X0 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ (X3 ◇ X2))) ◇ (X2 ◇ (X3 ◇ X2))))) ◇ ((X2 ◇ (X3 ◇ X2)) ◇ (X5 ◇ (((X2 ◇ (X3 ◇ X2)) ◇ ((X5 ◇ X2) ◇ X2)) ◇ ((X5 ◇ X2) ◇ X2))))))) ◇ (((X2 ◇ (X3 ◇ X2)) ◇ (X5 ◇ (((X2 ◇ (X3 ◇ X2)) ◇ ((X5 ◇ X2) ◇ X2)) ◇ ((X5 ◇ X2) ◇ X2)))) ◇ ((X5 ◇ X2) ◇ X2)))
      _ = (((X0 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ (X3 ◇ X2))) ◇ (X2 ◇ (X3 ◇ X2))))) ◇ (X4 ◇ (((X0 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ (X3 ◇ X2))) ◇ (X2 ◇ (X3 ◇ X2))))) ◇ ((X2 ◇ (X3 ◇ X2)) ◇ (X5 ◇ (((X2 ◇ (X3 ◇ X2)) ◇ ((X5 ◇ X2) ◇ X2)) ◇ ((X5 ◇ X2) ◇ X2))))) ◇ ((X2 ◇ (X3 ◇ X2)) ◇ (X5 ◇ (((X2 ◇ (X3 ◇ X2)) ◇ ((X5 ◇ X2) ◇ X2)) ◇ ((X5 ◇ X2) ◇ X2))))))) ◇ (((X2 ◇ (X3 ◇ X2)) ◇ (X5 ◇ (((X2 ◇ (X3 ◇ X2)) ◇ ((X5 ◇ X2) ◇ X2)) ◇ ((X5 ◇ X2) ◇ X2)))) ◇ ((X5 ◇ X2) ◇ X2))) := congrArg (· ◇ (((X2 ◇ (X3 ◇ X2)) ◇ (X5 ◇ (((X2 ◇ (X3 ◇ X2)) ◇ ((X5 ◇ X2) ◇ X2)) ◇ ((X5 ◇ X2) ◇ X2)))) ◇ ((X5 ◇ X2) ◇ X2))) (congrArg ((X0 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ (X3 ◇ X2))) ◇ (X2 ◇ (X3 ◇ X2))))) ◇ ·) (congrArg (X4 ◇ ·) (congrArg (· ◇ ((X2 ◇ (X3 ◇ X2)) ◇ (X5 ◇ (((X2 ◇ (X3 ◇ X2)) ◇ ((X5 ◇ X2) ◇ X2)) ◇ ((X5 ◇ X2) ◇ X2))))) ((p13 X0 X1 X2 X3 X5 (((X2 ◇ (X3 ◇ X2)) ◇ ((X5 ◇ X2) ◇ X2)))).symm))))
      _ = ((X0 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ (X3 ◇ X2))) ◇ (X2 ◇ (X3 ◇ X2))))) ◇ (X4 ◇ (((X0 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ (X3 ◇ X2))) ◇ (X2 ◇ (X3 ◇ X2))))) ◇ ((X2 ◇ (X3 ◇ X2)) ◇ (X5 ◇ (((X2 ◇ (X3 ◇ X2)) ◇ ((X5 ◇ X2) ◇ X2)) ◇ ((X5 ◇ X2) ◇ X2))))) ◇ ((X2 ◇ (X3 ◇ X2)) ◇ (X5 ◇ (((X2 ◇ (X3 ◇ X2)) ◇ ((X5 ◇ X2) ◇ X2)) ◇ ((X5 ◇ X2) ◇ X2))))))) := p10 ((X0 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ (X3 ◇ X2))) ◇ (X2 ◇ (X3 ◇ X2)))))) X4 ((X2 ◇ (X3 ◇ X2))) X5 (((X5 ◇ X2) ◇ X2))
  have p22 : ∀ (x y z u w v5 : G), (((x ◇ (y ◇ ((x ◇ (z ◇ (u ◇ z))) ◇ (z ◇ (u ◇ z))))) ◇ (w ◇ (x ◇ (y ◇ ((x ◇ (z ◇ (u ◇ z))) ◇ (z ◇ (u ◇ z))))))) ◇ (((z ◇ (u ◇ z)) ◇ (v5 ◇ (((z ◇ (u ◇ z)) ◇ ((v5 ◇ z) ◇ z)) ◇ ((v5 ◇ z) ◇ z)))) ◇ ((v5 ◇ z) ◇ z))) = ((x ◇ (y ◇ ((x ◇ (z ◇ (u ◇ z))) ◇ (z ◇ (u ◇ z))))) ◇ (w ◇ (x ◇ (y ◇ ((x ◇ (z ◇ (u ◇ z))) ◇ (z ◇ (u ◇ z))))))) := by
    intro x y z u w v5
    simpa only [p13, p13, p13] using (p22x x y z u w v5)
  have p23 : ∀ (x y z u w : G), (x ◇ ((y ◇ (z ◇ ((y ◇ (x ◇ (u ◇ x))) ◇ (x ◇ (u ◇ x))))) ◇ (w ◇ (y ◇ (z ◇ ((y ◇ (x ◇ (u ◇ x))) ◇ (x ◇ (u ◇ x)))))))) = x := by
    intro x y z u w
    calc (x ◇ ((y ◇ (z ◇ ((y ◇ (x ◇ (u ◇ x))) ◇ (x ◇ (u ◇ x))))) ◇ (w ◇ (y ◇ (z ◇ ((y ◇ (x ◇ (u ◇ x))) ◇ (x ◇ (u ◇ x))))))))
      _ = (x ◇ (((y ◇ (z ◇ ((y ◇ (x ◇ (u ◇ x))) ◇ (x ◇ (u ◇ x))))) ◇ (w ◇ (y ◇ (z ◇ ((y ◇ (x ◇ (u ◇ x))) ◇ (x ◇ (u ◇ x))))))) ◇ (((x ◇ (u ◇ x)) ◇ (((y ◇ (z ◇ ((y ◇ (x ◇ (u ◇ x))) ◇ (x ◇ (u ◇ x))))) ◇ (w ◇ (y ◇ (z ◇ ((y ◇ (x ◇ (u ◇ x))) ◇ (x ◇ (u ◇ x))))))) ◇ (((x ◇ (u ◇ x)) ◇ ((((y ◇ (z ◇ ((y ◇ (x ◇ (u ◇ x))) ◇ (x ◇ (u ◇ x))))) ◇ (w ◇ (y ◇ (z ◇ ((y ◇ (x ◇ (u ◇ x))) ◇ (x ◇ (u ◇ x))))))) ◇ x) ◇ x)) ◇ ((((y ◇ (z ◇ ((y ◇ (x ◇ (u ◇ x))) ◇ (x ◇ (u ◇ x))))) ◇ (w ◇ (y ◇ (z ◇ ((y ◇ (x ◇ (u ◇ x))) ◇ (x ◇ (u ◇ x))))))) ◇ x) ◇ x)))) ◇ ((((y ◇ (z ◇ ((y ◇ (x ◇ (u ◇ x))) ◇ (x ◇ (u ◇ x))))) ◇ (w ◇ (y ◇ (z ◇ ((y ◇ (x ◇ (u ◇ x))) ◇ (x ◇ (u ◇ x))))))) ◇ x) ◇ x)))) := congrArg (x ◇ ·) ((p22 y z x u w (((y ◇ (z ◇ ((y ◇ (x ◇ (u ◇ x))) ◇ (x ◇ (u ◇ x))))) ◇ (w ◇ (y ◇ (z ◇ ((y ◇ (x ◇ (u ◇ x))) ◇ (x ◇ (u ◇ x))))))))).symm)
      _ = x := p3 x (((y ◇ (z ◇ ((y ◇ (x ◇ (u ◇ x))) ◇ (x ◇ (u ◇ x))))) ◇ (w ◇ (y ◇ (z ◇ ((y ◇ (x ◇ (u ◇ x))) ◇ (x ◇ (u ◇ x)))))))) (((x ◇ (u ◇ x)) ◇ (((y ◇ (z ◇ ((y ◇ (x ◇ (u ◇ x))) ◇ (x ◇ (u ◇ x))))) ◇ (w ◇ (y ◇ (z ◇ ((y ◇ (x ◇ (u ◇ x))) ◇ (x ◇ (u ◇ x))))))) ◇ (((x ◇ (u ◇ x)) ◇ ((((y ◇ (z ◇ ((y ◇ (x ◇ (u ◇ x))) ◇ (x ◇ (u ◇ x))))) ◇ (w ◇ (y ◇ (z ◇ ((y ◇ (x ◇ (u ◇ x))) ◇ (x ◇ (u ◇ x))))))) ◇ x) ◇ x)) ◇ ((((y ◇ (z ◇ ((y ◇ (x ◇ (u ◇ x))) ◇ (x ◇ (u ◇ x))))) ◇ (w ◇ (y ◇ (z ◇ ((y ◇ (x ◇ (u ◇ x))) ◇ (x ◇ (u ◇ x))))))) ◇ x) ◇ x)))))
  have p34x : ∀ (X0 X1 X2 X3 : G), (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))))) ◇ (X3 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))))))) = X0 := by
    intro X0 X1 X2 X3
    calc (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))))) ◇ (X3 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))))))))
      _ = (X0 ◇ ((X1 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))))) ◇ (X3 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))))))) := congrArg (X0 ◇ ·) (congrArg (· ◇ (X3 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))))))) (congrArg (X1 ◇ ·) (congrArg (X2 ◇ ·) ((p5 X1 X0 X0 ((X1 ◇ X0))).symm))))
      _ = X0 := p23 X0 X1 X2 ((X1 ◇ X0)) X3
  have p34 : ∀ (x y z u : G), (x ◇ ((y ◇ (z ◇ (y ◇ (x ◇ ((y ◇ x) ◇ x))))) ◇ (u ◇ (y ◇ (z ◇ (y ◇ (x ◇ ((y ◇ x) ◇ x)))))))) = x := by
    intro x y z u
    simpa only [p5] using (p34x x y z u)
  have p41x : ∀ (X0 X1 X2 : G), (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))))))) = X0 := by
    intro X0 X1 X2
    calc (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))))))))
      _ = (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))))) ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))))))) := congrArg (X0 ◇ ·) (congrArg (· ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))))))) (congrArg (X1 ◇ ·) ((p3 X0 X1 X0).symm)))
      _ = X0 := p34 X0 X1 X0 X2
  have p41 : ∀ (x y z : G), (x ◇ ((y ◇ x) ◇ (z ◇ (y ◇ x)))) = x := by
    intro x y z
    simpa only [p3] using (p41x x y z)
  have p74x : ∀ (X0 X1 X2 X3 X4 : G), ((X0 ◇ X1) ◇ ((X1 ◇ (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1)))))) ◇ (X4 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1))))))))) = (X0 ◇ X1) := by
    intro X0 X1 X2 X3 X4
    calc ((X0 ◇ X1) ◇ ((X1 ◇ (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1)))))) ◇ (X4 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1)))))))))
      _ = ((X0 ◇ X1) ◇ ((X1 ◇ (X2 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1)))))) ◇ (X4 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1))))))))) := congrArg ((X0 ◇ X1) ◇ ·) (congrArg (· ◇ (X4 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1)))))))) (congrArg (X1 ◇ ·) (congrArg (X2 ◇ ·) (congrArg (· ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1)))) ((p41 X1 X0 X3).symm)))))
      _ = (X0 ◇ X1) := p23 ((X0 ◇ X1)) X1 X2 X3 X4
  have p74 : ∀ (x y z u : G), ((x ◇ y) ◇ ((y ◇ (z ◇ y)) ◇ (u ◇ (y ◇ (z ◇ y))))) = (x ◇ y) := by
    intro x y z u
    simpa only [p41, p41, p41] using (p74x x y z x u)
  have p50 : ∀ (x y : G), ((x ◇ y) ◇ y) = (x ◇ y) := by
    intro x y
    calc ((x ◇ y) ◇ y)
      _ = ((x ◇ y) ◇ (y ◇ ((x ◇ y) ◇ ((y ◇ (x ◇ y)) ◇ (x ◇ y))))) := congrArg ((x ◇ y) ◇ ·) ((p41 y x ((y ◇ (x ◇ y)))).symm)
      _ = (x ◇ y) := p3 ((x ◇ y)) y ((x ◇ y))
  have p117 : ∀ (x y z : G), (x ◇ (y ◇ (z ◇ (y ◇ x)))) = x := by
    intro x y z
    calc (x ◇ (y ◇ (z ◇ (y ◇ x))))
      _ = (x ◇ (y ◇ (z ◇ ((y ◇ x) ◇ x)))) := congrArg (x ◇ ·) (congrArg (y ◇ ·) (congrArg (z ◇ ·) ((p50 y x).symm)))
      _ = x := p3 x y z
  have p124 : ∀ (x y z : G), ((x ◇ (y ◇ x)) ◇ (z ◇ x)) = (x ◇ (y ◇ x)) := by
    intro x y z
    calc ((x ◇ (y ◇ x)) ◇ (z ◇ x))
      _ = ((x ◇ (y ◇ x)) ◇ ((z ◇ x) ◇ ((x ◇ (y ◇ x)) ◇ ((z ◇ x) ◇ (x ◇ (y ◇ x)))))) := congrArg ((x ◇ (y ◇ x)) ◇ ·) ((p74 z x y ((z ◇ x))).symm)
      _ = (x ◇ (y ◇ x)) := p117 ((x ◇ (y ◇ x))) ((z ◇ x)) ((x ◇ (y ◇ x)))
  have p136 : ∀ (x y z : G), (x ◇ (y ◇ (x ◇ (z ◇ x)))) = x := by
    intro x y z
    calc (x ◇ (y ◇ (x ◇ (z ◇ x))))
      _ = (x ◇ (y ◇ ((x ◇ (z ◇ x)) ◇ (y ◇ x)))) := congrArg (x ◇ ·) (congrArg (y ◇ ·) ((p124 x z y).symm))
      _ = x := p117 x y ((x ◇ (z ◇ x)))
  calc x
    _ = (x ◇ (y ◇ (x ◇ ((z ◇ w) ◇ x)))) := (p136 x y ((z ◇ w))).symm

end submission


def submission : Goal := submission.certificate

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_5715_to_5656 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_5715_to_5656
