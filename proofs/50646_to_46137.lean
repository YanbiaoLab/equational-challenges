-- Equation50646 → Equation46137
-- Recorded verdict: true
-- Premise: x * y = (x * ((z * w) * w)) * u
-- Conclusion: x * y = (x * x) * (z * (x * x))
-- Original submission SHA-256: 82a46a833e89fa5bc2c7998f3174967e4efd0d69763c84037bfa7fbdc40f4397
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = (x ◇ ((z ◇ w) ◇ w)) ◇ u
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (x ◇ x) ◇ (z ◇ (x ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (x y z w u:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w u
    exact (h x y z w u).trans ((h x x z w u).symm)
  have apc1 : forall (q0 q1 q2 q3:G), ((q0 ◇ q0) ◇ (q0 ◇ q0)) = (q0 ◇ q0):=by
    intro q0 q1 q2 q3
    exact (((congrArg (fun t => t ◇ (q0 ◇ ((q1 ◇ q2) ◇ q2))) (apc0 q0 ((q1 ◇ q2) ◇ q2) (q0 ◇ ((q1 ◇ q2) ◇ q2)) (q0 ◇ ((q1 ◇ q2) ◇ q2)) (q0 ◇ ((q1 ◇ q2) ◇ q2)))).trans (congrArg (fun t => (q0 ◇ q0) ◇ t) (apc0 q0 ((q1 ◇ q2) ◇ q2) (q0 ◇ ((q1 ◇ q2) ◇ q2)) (q0 ◇ ((q1 ◇ q2) ◇ q2)) (q0 ◇ ((q1 ◇ q2) ◇ q2))))).symm).trans ((((apc0 (q0 ◇ ((q1 ◇ q2) ◇ q2)) q2 q2 q2 q2).symm).trans ((h q0 q3 q1 q2 q2).symm)).trans (apc0 q0 q3 (q0 ◇ q3) (q0 ◇ q3) (q0 ◇ q3)))
  exact (calc
    (x ◇ y) = (x ◇ x):=apc0 x y (x ◇ y) (x ◇ y) (x ◇ y)
    _ = ((x ◇ x) ◇ (z ◇ (x ◇ x))):=(((congrArg (fun t => (x ◇ x) ◇ t) (apc0 z (x ◇ x) (z ◇ (x ◇ x)) (z ◇ (x ◇ x)) (z ◇ (x ◇ x)))).trans (apc0 (x ◇ x) (z ◇ z) ((x ◇ x) ◇ (z ◇ z)) ((x ◇ x) ◇ (z ◇ z)) ((x ◇ x) ◇ (z ◇ z)))).trans (apc1 x ((x ◇ x) ◇ (x ◇ x)) ((x ◇ x) ◇ (x ◇ x)) ((x ◇ x) ◇ (x ◇ x)))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_50646_to_46137 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_50646_to_46137
