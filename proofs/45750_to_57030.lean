-- Equation45750 → Equation57030
-- Recorded verdict: true
-- Premise: x * y = z * (((z * w) * x) * w)
-- Conclusion: x * (y * z) = (y * (x * z)) * z
-- Original submission SHA-256: 8a587b3f2e521d9dda5e5aa39489690e3bf98e8b7afdfa01528c54f6462444ce
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ (((z ◇ w) ◇ x) ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ z) = (y ◇ (x ◇ z)) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (x y z w:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w
    exact (h x y z w).trans ((h x x z w).symm)
  have apc1 : forall (q0 q1 q2:G), (q1 ◇ q1) = (q0 ◇ q0):=by
    intro q0 q1 q2
    exact (((apc0 q1 (((q1 ◇ q0) ◇ q0) ◇ q0) q0 q0).symm).trans ((h q0 q2 q1 q0).symm)).trans (apc0 q0 q2 (q0 ◇ q2) (q0 ◇ q2))
  exact (calc
    (x ◇ (y ◇ z)) = (x ◇ x):=apc0 x (y ◇ z) x x
    _ = ((y ◇ (x ◇ z)) ◇ (y ◇ (x ◇ z))):=apc1 (y ◇ (x ◇ z)) x x
    _ = ((y ◇ (x ◇ z)) ◇ z):=(apc0 (y ◇ (x ◇ z)) z x x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_45750_to_57030 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_45750_to_57030
