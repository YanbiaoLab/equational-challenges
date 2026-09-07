-- Equation54808 → Equation53927
-- Recorded verdict: true
-- Premise: x ◇ (x ◇ y) = y ◇ ((z ◇ w) ◇ w)
-- Conclusion: x ◇ (x ◇ y) = y ◇ (z ◇ (z ◇ w))
-- Original submission SHA-256: c7c59251fcce72d31a859eb8bfa6324d50a8e8de6a330eb75bd2f0577d1af2c2
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (x ◇ y) = y ◇ ((z ◇ w) ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (x ◇ y) = y ◇ (z ◇ (z ◇ w))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  calc
    (x ◇ (x ◇ y)) = (y ◇ (z ◇ (z ◇ w))):=((((h x y w ((z ◇ w) ◇ w)).trans (congrArg (fun t => y ◇ t) ((h z (w ◇ ((z ◇ w) ◇ w)) z w).symm))).trans (congrArg (fun t => y ◇ t) (congrArg (fun t => z ◇ t) (congrArg (fun t => z ◇ t) ((h z w z w).symm))))).trans (congrArg (fun t => y ◇ t) (congrArg (fun t => z ◇ t) (h z (z ◇ w) z w)))).trans ((((((congrArg (fun t => y ◇ t) (h z w w w)).trans (congrArg (fun t => y ◇ t) ((h (z ◇ w) w w w).symm))).trans (congrArg (fun t => y ◇ t) ((h z (z ◇ w) z w).symm))).trans (congrArg (fun t => y ◇ t) (congrArg (fun t => z ◇ t) (h z w w w)))).trans (congrArg (fun t => y ◇ t) (congrArg (fun t => z ◇ t) ((h (z ◇ w) w w w).symm)))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_54808_to_53927 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_54808_to_53927
