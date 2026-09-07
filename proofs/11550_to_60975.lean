-- Equation11550 → Equation60975
-- Recorded verdict: true
-- Premise: x = y * ((z * (z * w)) * (y * y))
-- Conclusion: (x * x) * y = (z * (y * z)) * y
-- Original submission SHA-256: c8cec262ad9bc62e9aa69f7c33295a6c3248e84e30cb1bd6313e6dbb1ef5545c
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ ((z ◇ (z ◇ w)) ◇ (y ◇ y))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ x) ◇ y = (z ◇ (y ◇ z)) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (x y z w:G), y = x:=by
    intro x y z w
    exact ((h x y z w).trans ((h y y z w).symm)).symm
  exact (apc0 ((x ◇ x) ◇ y) ((x ◇ x) ◇ y) ((x ◇ x) ◇ y) ((x ◇ x) ◇ y)).trans ((apc0 ((x ◇ x) ◇ y) ((z ◇ (y ◇ z)) ◇ y) ((x ◇ x) ◇ y) ((x ◇ x) ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_11550_to_60975 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_11550_to_60975
