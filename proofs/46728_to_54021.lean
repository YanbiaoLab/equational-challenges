-- Equation46728 → Equation54021
-- Recorded verdict: true
-- Premise: x * y = (z * w) * (w * (x * x))
-- Conclusion: x * (y * x) = x * (y * (x * y))
-- Original submission SHA-256: 380736cc94cd09a6f0da6df068c9234c0ef2545a97a8dc1f1d915850843246d5
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ w) ◇ (w ◇ (x ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ (y ◇ x) = x ◇ (y ◇ (x ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  calc
    (x ◇ (y ◇ x)) = (x ◇ (y ◇ (x ◇ y))):=(h x (y ◇ x) (x ◇ (y ◇ (x ◇ y))) (x ◇ (y ◇ x))).trans ((h x (y ◇ (x ◇ y)) (x ◇ (y ◇ (x ◇ y))) (x ◇ (y ◇ x))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_46728_to_54021 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_46728_to_54021
