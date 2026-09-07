-- Equation3892 → Equation54692
-- Recorded verdict: true
-- Premise: x ◇ x = (y ◇ (y ◇ y)) ◇ z
-- Conclusion: x ◇ (x ◇ x) = x ◇ ((y ◇ y) ◇ x)
-- Original submission SHA-256: a3ad0417fbedc540c5132ba29aa287971d8857f9771c1cb0f5a4b7d312c689d5
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = (y ◇ (y ◇ y)) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ (x ◇ x) = x ◇ ((y ◇ y) ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  calc
    (x ◇ (x ◇ x)) = (x ◇ ((y ◇ y) ◇ x)):=(congrArg (fun t => x ◇ t) (h x (x ◇ (x ◇ x)) x)).trans (((congrArg (fun t => x ◇ t) (congrArg (fun t => t ◇ x) (h y x (x ◇ x)))).trans (congrArg (fun t => x ◇ t) (congrArg (fun t => t ◇ x) (congrArg (fun t => (x ◇ (x ◇ x)) ◇ t) (h x x (x ◇ (x ◇ x))))))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_3892_to_54692 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_3892_to_54692
