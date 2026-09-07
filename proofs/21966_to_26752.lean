-- Equation21966 → Equation26752
-- Recorded verdict: true
-- Premise: x = (y * (z * y)) * (y * (z * y))
-- Conclusion: x = ((x * y) * (z * x)) * (y * z)
-- Original submission SHA-256: 61fb652f24ed35ae72d6d835c4cf16993455a9c9c188ca2ababfbb9477efc2f2
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ (z ◇ y)) ◇ (y ◇ (z ◇ y))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((x ◇ y) ◇ (z ◇ x)) ◇ (y ◇ z)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  calc
    x = (((x ◇ y) ◇ (z ◇ x)) ◇ (y ◇ z)):=(h x x x).trans ((h (((x ◇ y) ◇ (z ◇ x)) ◇ (y ◇ z)) x x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_21966_to_26752 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_21966_to_26752
