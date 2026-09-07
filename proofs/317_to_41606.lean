-- Equation317 → Equation41606
-- Recorded verdict: true
-- Premise: x ◇ x = y ◇ (y ◇ z)
-- Conclusion: x ◇ x = y ◇ (x ◇ (z ◇ (y ◇ y)))
-- Original submission SHA-256: 65ad0db6c8ffdadf551c6dc658b772620459de54c6257256f6965ee599392a55
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = y ◇ (y ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = y ◇ (x ◇ (z ◇ (y ◇ y)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  calc
    (x ◇ x) = (y ◇ (x ◇ (z ◇ (y ◇ y)))):=(h x y y).trans (((((congrArg (fun t => y ◇ t) (congrArg (fun t => x ◇ t) (congrArg (fun t => z ◇ t) (h y x x)))).trans (congrArg (fun t => y ◇ t) (congrArg (fun t => x ◇ t) (congrArg (fun t => z ◇ t) ((h z x x).symm))))).trans (congrArg (fun t => y ◇ t) (congrArg (fun t => x ◇ t) ((h x z z).symm)))).trans (congrArg (fun t => y ◇ t) ((h y x x).symm))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_317_to_41606 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_317_to_41606
