-- Equation52015 → Equation45214
-- Recorded verdict: true
-- Premise: x * y = ((z * w) * (w * u)) * v
-- Conclusion: x * x = y * (((z * w) * x) * x)
-- Original submission SHA-256: 9bcf1565d46cbc6244a74a64afb7f180b7958dfd7ae678d4751e7f953c32b2c5
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G), x ◇ y = ((z ◇ w) ◇ (w ◇ u)) ◇ v
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ x = y ◇ (((z ◇ w) ◇ x) ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z w u v:G), (z ◇ z) = (x ◇ y):=by
    intro x y z w u v
    exact ((h x y z w u v).trans ((h z z z w u v).symm)).symm
  exact (apc0 (x ◇ x) (x ◇ x) x (x ◇ x) (x ◇ x) (x ◇ x)).trans (apc0 y (((z ◇ w) ◇ x) ◇ x) (x ◇ x) (x ◇ x) (x ◇ x) (x ◇ x))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_52015_to_45214 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_52015_to_45214
