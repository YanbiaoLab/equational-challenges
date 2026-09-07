-- Equation54959 → Equation54024
-- Recorded verdict: true
-- Premise: x ◇ (y ◇ x) = y ◇ ((z ◇ w) ◇ w)
-- Conclusion: x ◇ (y ◇ x) = x ◇ (y ◇ (y ◇ y))
-- Original submission SHA-256: 6e0200d06297535d7e7f91ef674c81792ee2d6a397e87581146020d4e1cbd802
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ x) = y ◇ ((z ◇ w) ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ (y ◇ x) = x ◇ (y ◇ (y ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  calc
    (x ◇ (y ◇ x)) = (x ◇ (y ◇ (y ◇ y))):=((((((h x y y y).trans (h y (y ◇ y) y (y ◇ y))).trans (congrArg (fun t => (y ◇ y) ◇ t) (congrArg (fun t => t ◇ (y ◇ y)) (h y y x x)))).trans (congrArg (fun t => (y ◇ y) ◇ t) (congrArg (fun t => t ◇ (y ◇ y)) ((h x y x x).symm)))).trans (h (y ◇ y) (x ◇ (y ◇ x)) x (y ◇ y))).trans ((h (y ◇ x) (x ◇ (y ◇ x)) x (y ◇ y)).symm)).trans ((((((((congrArg (fun t => x ◇ t) (h y y y y)).trans (congrArg (fun t => x ◇ t) (h y (y ◇ y) y (y ◇ y)))).trans (congrArg (fun t => x ◇ t) (h (y ◇ y) (y ◇ (y ◇ y)) x x))).trans (congrArg (fun t => x ◇ t) (congrArg (fun t => t ◇ ((x ◇ x) ◇ x)) (h y y x x)))).trans ((h x x y ((x ◇ x) ◇ x)).symm)).trans (h x x y x)).trans (h x (y ◇ x) x (y ◇ x))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_54959_to_54024 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_54959_to_54024
