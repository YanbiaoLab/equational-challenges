-- Equation55110 → Equation54734
-- Recorded verdict: true
-- Premise: x ◇ (y ◇ y) = y ◇ ((z ◇ w) ◇ w)
-- Conclusion: x ◇ (x ◇ x) = y ◇ ((z ◇ w) ◇ w)
-- Original submission SHA-256: d3beda84af6d15d5928078249aaadb8d2d271e1050730540c36f36dfd8e7001f
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ y) = y ◇ ((z ◇ w) ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (x ◇ x) = y ◇ ((z ◇ w) ◇ w)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  calc
    (x ◇ (x ◇ x)) = (y ◇ ((z ◇ w) ◇ w)):=(((h x x z (x ◇ x)).trans (congrArg (fun t => x ◇ t) (h (z ◇ (x ◇ x)) x w w))).trans (congrArg (fun t => x ◇ t) ((h (x ◇ x) x w w).symm))).trans ((((((((h x y z w).symm).trans (h x y w (x ◇ x))).trans (congrArg (fun t => y ◇ t) (h (w ◇ (x ◇ x)) x w w))).trans (congrArg (fun t => y ◇ t) ((h (x ◇ x) x w w).symm))).trans (h y (x ◇ x) w x)).trans ((h x (x ◇ x) w x).symm)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_55110_to_54734 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_55110_to_54734
