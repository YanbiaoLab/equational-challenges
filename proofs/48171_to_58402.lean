-- Equation48171 → Equation58402
-- Recorded verdict: true
-- Premise: x * y = (y * (z * w)) * (u * u)
-- Conclusion: (x * y) * x = x * (x * (z * y))
-- Original submission SHA-256: 2e178bd8d212046f8fceedacc479151fbb52d2c03608ac09129ea5ad6fd4af2a
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = (y ◇ (z ◇ w)) ◇ (u ◇ u)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ x = x ◇ (x ◇ (z ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2:G), (q1 ◇ q2) = (q0 ◇ q2):=by
    intro q0 q1 q2
    exact ((h q0 q2 q0 q0 q0).trans ((h q1 q2 q0 q0 q0).symm)).symm
  have apc2 : forall (q3 q4 q5 q6:G), (q3 ◇ (q4 ◇ q4)) = (q5 ◇ q6):=by
    intro q3 q4 q5 q6
    exact ((apc0 q3 (q6 ◇ (q3 ◇ q3)) (q4 ◇ q4)).symm).trans ((h q5 q6 q3 q3 q4).symm)
  exact ((apc2 (x ◇ (x ◇ (z ◇ y))) ((x ◇ y) ◇ x) (x ◇ y) x).symm).trans (apc2 (x ◇ (x ◇ (z ◇ y))) ((x ◇ y) ◇ x) x (x ◇ (z ◇ y)))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_48171_to_58402 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_48171_to_58402
