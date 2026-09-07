-- Equation54234 → Equation54248
-- Recorded verdict: true
-- Premise: x ◇ (y ◇ y) = y ◇ (z ◇ (w ◇ u))
-- Conclusion: x ◇ (y ◇ y) = z ◇ (x ◇ (w ◇ y))
-- Original submission SHA-256: f5e2568d32ba5a0518daf9d340aed0293311d683a72f8b505faa82d2c939c56b
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
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ y) = z ◇ (x ◇ (w ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  calc
    (x ◇ (y ◇ y)) = (z ◇ (x ◇ (w ◇ y))):=(((h x y (w ◇ y) w y).trans (h y (w ◇ y) x w y)).trans ((h z (w ◇ y) x w y).symm)).trans ((((h x z x w y).symm).trans (h x z (w ◇ y) w y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_54234_to_54248 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_54234_to_54248
