-- Equation3816 → Equation57323
-- Recorded verdict: true
-- Premise: x * y = (z * y) * (w * z)
-- Conclusion: x * (x * x) = ((x * y) * y) * x
-- Original submission SHA-256: c06c78959f45d4c3ed311fed77bb1c54ae4f8d2c474a4341251fda3c0b2a5480
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ y) ◇ (w ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ (x ◇ x) = ((x ◇ y) ◇ y) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (x y z w:G), (y ◇ y) = (x ◇ y):=by
    intro x y z w
    exact ((h x y z w).trans ((h y y z w).symm)).symm
  have apc1 : forall (q0 q1 q2:G), (q0 ◇ (q1 ◇ q1)) = (q2 ◇ q1):=by
    intro q0 q1 q2
    exact ((apc0 q0 (q1 ◇ q1) q0 q0).symm).trans ((h q2 q1 q1 q1).symm)
  exact apc1 x x ((x ◇ y) ◇ y)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_3816_to_57323 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_3816_to_57323
