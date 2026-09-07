-- Equation51585 → Equation45790
-- Recorded verdict: true
-- Premise: x * y = ((y * y) * (y * z)) * z
-- Conclusion: x * y = z * (((w * x) * w) * z)
-- Original submission SHA-256: 5e232cd0c979994eea1e8cba1a5339f2f04ff024c79588d19eebb81bba1fb1c7
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = ((y ◇ y) ◇ (y ◇ z)) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ (((w ◇ x) ◇ w) ◇ z)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z:G), (y ◇ y) = (x ◇ y):=by
    intro x y z
    exact ((h x y z).trans ((h y y z).symm)).symm
  have apc2 : forall (q0 q1 q2:G), (q2 ◇ q2) = (q0 ◇ q1):=by
    intro q0 q1 q2
    exact (apc0 ((q1 ◇ q1) ◇ (q1 ◇ q2)) q2 q0).trans ((h q0 q1 q2).symm)
  exact ((apc2 x y (x ◇ y)).symm).trans (apc2 z (((w ◇ x) ◇ w) ◇ z) (x ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_51585_to_45790 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_51585_to_45790
