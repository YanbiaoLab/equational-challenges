-- Equation41616 → Equation60926
-- Recorded verdict: true
-- Premise: x ◇ x = y ◇ (x ◇ (z ◇ (w ◇ w)))
-- Conclusion: (x ◇ x) ◇ y = (y ◇ (y ◇ y)) ◇ y
-- Original submission SHA-256: 374f88b0f0c0894c8bc2d39774b697d091d99f1738af8c00fad00b0b8eedb4f3
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ x = y ◇ (x ◇ (z ◇ (w ◇ w)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), (x ◇ x) ◇ y = (y ◇ (y ◇ y)) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  calc
    ((x ◇ x) ◇ y) = ((y ◇ (y ◇ y)) ◇ y):=(congrArg (fun t => t ◇ y) (h x y y (x ◇ x))).trans ((congrArg (fun t => t ◇ y) (congrArg (fun t => y ◇ t) (h y x (x ◇ x) x))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_41616_to_60926 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_41616_to_60926
