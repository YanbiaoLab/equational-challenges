-- Equation49378 → Equation4074
-- Recorded verdict: true
-- Premise: x * y = ((z * w) * w) * (w * u)
-- Conclusion: x * x = ((x * y) * y) * y
-- Original submission SHA-256: 1f51032c3599acb415e3a4a33aab930a8c55aebcf0b018225be88d11d956c55c
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = ((z ◇ w) ◇ w) ◇ (w ◇ u)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ x = ((x ◇ y) ◇ y) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (x y z w u:G), (z ◇ z) = (x ◇ y):=by
    intro x y z w u
    exact ((h x y z w u).trans ((h z z z w u).symm)).symm
  exact (apc0 (x ◇ x) (x ◇ x) x (x ◇ x) (x ◇ x)).trans (apc0 ((x ◇ y) ◇ y) y (x ◇ x) (x ◇ x) (x ◇ x))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_49378_to_4074 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_49378_to_4074
