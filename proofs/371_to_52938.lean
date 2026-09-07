-- Equation371 → Equation52938
-- Recorded verdict: true
-- Premise: x ◇ x = (y ◇ z) ◇ y
-- Conclusion: x ◇ x = (((x ◇ x) ◇ y) ◇ y) ◇ x
-- Original submission SHA-256: 70b76386d869c68474a4a9e958efd5913cee33a1e2d25f9515b72251c4df42e9
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = (y ◇ z) ◇ y
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ x = (((x ◇ x) ◇ y) ◇ y) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  calc
    (x ◇ x) = ((((x ◇ x) ◇ y) ◇ y) ◇ x):=(h x x x).trans (((((congrArg (fun t => t ◇ x) (congrArg (fun t => t ◇ y) (congrArg (fun t => t ◇ y) (h x x x)))).trans (congrArg (fun t => t ◇ x) (congrArg (fun t => t ◇ y) (congrArg (fun t => t ◇ y) ((h y x x).symm))))).trans (congrArg (fun t => t ◇ x) (congrArg (fun t => t ◇ y) ((h y y y).symm)))).trans (congrArg (fun t => t ◇ x) ((h x y y).symm))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_371_to_52938 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_371_to_52938
