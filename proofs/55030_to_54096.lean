-- Equation55030 → Equation54096
-- Recorded verdict: true
-- Premise: x ◇ (y ◇ x) = z ◇ ((w ◇ w) ◇ w)
-- Conclusion: x ◇ (y ◇ x) = z ◇ (x ◇ (w ◇ x))
-- Original submission SHA-256: ae37e30304f8a3c9909717d9d90d02c3af54638e74f8c402e486f6cce1651a2e
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ x) = z ◇ ((w ◇ w) ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ x) = z ◇ (x ◇ (w ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  calc
    (x ◇ (y ◇ x)) = (z ◇ (x ◇ (w ◇ x))):=(h x y z ((w ◇ w) ◇ w)).trans (((congrArg (fun t => z ◇ t) (h x w (x ◇ (w ◇ x)) w)).trans (congrArg (fun t => z ◇ t) (congrArg (fun t => t ◇ ((w ◇ w) ◇ w)) (h x w ((w ◇ w) ◇ w) w)))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_55030_to_54096 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_55030_to_54096
