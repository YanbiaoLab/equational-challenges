-- Equation42230 → Equation52630
-- Recorded verdict: true
-- Premise: x * y = z * (z * (z * (z * x)))
-- Conclusion: x * y = ((z * (x * w)) * u) * y
-- Original submission SHA-256: cacb5c6d9f82a22429f35e5a0ccc769d8ebfda430267c9763c9506cd620b4f2c
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = z ◇ (z ◇ (z ◇ (z ◇ x)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = ((z ◇ (x ◇ w)) ◇ u) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (x y z:G), (x ◇ y) = (x ◇ x):=by
    intro x y z
    exact (h x y z).trans ((h x x z).symm)
  have apc1 : forall (q0 q1 q2:G), (q1 ◇ q1) = (q0 ◇ q0):=by
    intro q0 q1 q2
    exact (((apc0 q1 (q1 ◇ (q1 ◇ (q1 ◇ q0))) q0).symm).trans ((h q0 q2 q1).symm)).trans (apc0 q0 q2 (q0 ◇ q2))
  exact (calc
    (x ◇ y) = (x ◇ x):=apc0 x y u
    _ = (((z ◇ (x ◇ w)) ◇ u) ◇ ((z ◇ (x ◇ w)) ◇ u)):=apc1 ((z ◇ (x ◇ w)) ◇ u) x u
    _ = (((z ◇ (x ◇ w)) ◇ u) ◇ y):=(apc0 ((z ◇ (x ◇ w)) ◇ u) y u).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_42230_to_52630 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_42230_to_52630
