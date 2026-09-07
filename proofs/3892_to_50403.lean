-- Equation3892 → Equation50403
-- Recorded verdict: true
-- Premise: x ◇ x = (y ◇ (y ◇ y)) ◇ z
-- Conclusion: x ◇ x = (y ◇ ((y ◇ y) ◇ y)) ◇ z
-- Original submission SHA-256: c6667c88ac31ef83ff0e18d369bfd2d1ee50293baeb5c1b7f9b9ac5d8d99ba3f
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
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = (y ◇ ((y ◇ y) ◇ y)) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  calc
    (x ◇ x) = ((y ◇ ((y ◇ y) ◇ y)) ◇ z):=((h x y z).trans (congrArg (fun t => t ◇ z) (congrArg (fun t => y ◇ t) (h y (y ◇ (y ◇ y)) y)))).trans (((congrArg (fun t => t ◇ z) (congrArg (fun t => y ◇ t) (congrArg (fun t => t ◇ y) (h y y (x ◇ x))))).trans (congrArg (fun t => t ◇ z) (congrArg (fun t => y ◇ t) (congrArg (fun t => t ◇ y) (congrArg (fun t => (y ◇ (y ◇ y)) ◇ t) (h x y (y ◇ (y ◇ y)))))))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_3892_to_50403 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_3892_to_50403
