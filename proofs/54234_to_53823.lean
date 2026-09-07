-- Equation54234 → Equation53823
-- Recorded verdict: true
-- Premise: x ◇ (y ◇ y) = y ◇ (z ◇ (w ◇ u))
-- Conclusion: x ◇ (x ◇ x) = y ◇ (x ◇ (x ◇ y))
-- Original submission SHA-256: 12169827b13062ff2ad633acb8da337a538fd55ce90a15b93017088099f2817e
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ (y ◇ y) = y ◇ (z ◇ (w ◇ u))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ (x ◇ x) = y ◇ (x ◇ (x ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  calc
    (x ◇ (x ◇ x)) = (y ◇ (x ◇ (x ◇ y))):=(((h x x (x ◇ y) x y).trans (h x (x ◇ y) x x y)).trans ((h y (x ◇ y) x x y).symm)).trans ((((h x y x x y).symm).trans (h x y (x ◇ y) x y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_54234_to_53823 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_54234_to_53823
