-- Equation49201 → Equation62564
-- Recorded verdict: true
-- Premise: x * y = ((z * y) * w) * (u * w)
-- Conclusion: (x * y) * z = ((w * u) * u) * x
-- Original submission SHA-256: 1a07d089e1e0ad64e266b669b27f226a0bc97a610cf55d14b58514bb56543c8e
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = ((z ◇ y) ◇ w) ◇ (u ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), (x ◇ y) ◇ z = ((w ◇ u) ◇ u) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (x y z w u:G), (y ◇ y) = (x ◇ y):=by
    intro x y z w u
    exact ((h x y z w u).trans ((h y y z w u).symm)).symm
  have apc5 : forall (q0 q1 q2 q3:G), ((q0 ◇ q1) ◇ (q0 ◇ q1)) = (q2 ◇ q3):=by
    intro q0 q1 q2 q3
    exact (apc0 ((q0 ◇ q3) ◇ q1) (q0 ◇ q1) q0 q0 q0).trans ((h q2 q3 q0 q1 q0).symm)
  have apc6 : forall (q0 q1 q2 q3:G), (q2 ◇ q3) = (q0 ◇ q0):=by
    intro q0 q1 q2 q3
    exact ((apc5 q0 q1 q2 q3).symm).trans (apc5 q0 q1 q0 q0)
  exact (apc6 ((x ◇ y) ◇ z) ((x ◇ y) ◇ z) (x ◇ y) z).trans ((apc6 ((x ◇ y) ◇ z) ((x ◇ y) ◇ z) ((w ◇ u) ◇ u) x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_49201_to_62564 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_49201_to_62564
