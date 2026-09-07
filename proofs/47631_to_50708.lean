-- Equation47631 → Equation50708
-- Recorded verdict: true
-- Premise: x * y = (z * w) * ((u * x) * x)
-- Conclusion: x * y = (y * ((y * y) * z)) * z
-- Original submission SHA-256: 827400ca22cac1813ab1872f3b99d0886ab09e9bd5a73204be9e60038faffe79
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = (z ◇ w) ◇ ((u ◇ x) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (y ◇ ((y ◇ y) ◇ z)) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (x y z w u:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w u
    exact (h x y z w u).trans ((h x x z w u).symm)
  have apc1 : forall (q0 q1 q2 q3:G), ((q2 ◇ q0) ◇ (q2 ◇ q0)) = (q1 ◇ q1):=by
    intro q0 q1 q2 q3
    exact (((apc0 (q2 ◇ q0) ((q0 ◇ q1) ◇ q1) q0 q0 q0).symm).trans ((h q1 q3 q2 q0 q0).symm)).trans (apc0 q1 q3 (q1 ◇ q3) (q1 ◇ q3) (q1 ◇ q3))
  have apc2 : forall (q4 q5 q6:G), (q6 ◇ q6) = (q5 ◇ q4):=by
    intro q4 q5 q6
    exact ((h q5 q4 (q4 ◇ q5) q5 q4).trans (apc1 q5 q6 (q4 ◇ q5) q4)).symm
  exact ((apc2 y x (x ◇ y)).symm).trans (apc2 z (y ◇ ((y ◇ y) ◇ z)) (x ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_47631_to_50708 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_47631_to_50708
