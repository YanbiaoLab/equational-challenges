-- Equation42985 → Equation58269
-- Recorded verdict: true
-- Premise: x * y = z * (x * ((w * u) * w))
-- Conclusion: (x * x) * y = x * (z * (y * y))
-- Original submission SHA-256: 4b5813cc12c815e9840eabe5f75b62f4cb09f81b85819bfe71becbbfb9ec4da3
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = z ◇ (x ◇ ((w ◇ u) ◇ w))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ x) ◇ y = x ◇ (z ◇ (y ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2:G), (q1 ◇ q2) = (q1 ◇ q0):=by
    intro q0 q1 q2
    exact ((h q1 q0 q0 q0 q0).trans ((h q1 q2 q0 q0 q0).symm)).symm
  have apc1 : forall (x y z w u:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w u
    exact (h x y z w u).trans ((h x x z w u).symm)
  have apc2 : forall (q3 q4 q5 q6:G), (q5 ◇ q3) = (q4 ◇ q4):=by
    intro q3 q4 q5 q6
    exact (((apc0 q3 q5 (q4 ◇ ((q3 ◇ q3) ◇ q3))).symm).trans ((h q4 q6 q5 q3 q3).symm)).trans (apc1 q4 q6 (q4 ◇ q6) (q4 ◇ q6) (q4 ◇ q6))
  exact (apc2 y ((x ◇ x) ◇ y) (x ◇ x) ((x ◇ x) ◇ y)).trans ((apc2 (z ◇ (y ◇ y)) ((x ◇ x) ◇ y) x ((x ◇ x) ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_42985_to_58269 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_42985_to_58269
