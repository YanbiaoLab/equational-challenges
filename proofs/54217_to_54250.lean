-- Equation54217 → Equation54250
-- Recorded verdict: true
-- Premise: x ◇ (y ◇ y) = y ◇ (y ◇ (z ◇ w))
-- Conclusion: x ◇ (y ◇ y) = z ◇ (x ◇ (w ◇ w))
-- Original submission SHA-256: 4c41ffd422780164bc6d9684446fb760fcf3c4c19906eb4782062a3ce1e8d862
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ y) = y ◇ (y ◇ (z ◇ w))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ y) = z ◇ (x ◇ (w ◇ w))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  calc
    (x ◇ (y ◇ y)) = (z ◇ (x ◇ (w ◇ w))):=(((((h x y w w).trans (congrArg (fun t => y ◇ t) (h y w w w))).trans (congrArg (fun t => y ◇ t) ((h (w ◇ w) w w w).symm))).trans (h y (w ◇ w) w w)).trans ((h z (w ◇ w) w w).symm)).trans (((congrArg (fun t => z ◇ t) (h x w w w)).trans (congrArg (fun t => z ◇ t) ((h (w ◇ w) w w w).symm))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_54217_to_54250 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_54217_to_54250
