-- Equation48967 → Equation4338
-- Recorded verdict: true
-- Premise: x * y = ((y * y) * z) * (z * w)
-- Conclusion: x * (y * x) = z * (w * u)
-- Original submission SHA-256: f008a0a4f9da4b7f4dddafa5ed784272cc6fa6850327259a61b0e69ecfa29c87
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((y ◇ y) ◇ z) ◇ (z ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ (y ◇ x) = z ◇ (w ◇ u)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc1 : forall (q0 q1 q2:G), (q1 ◇ q2) = (q0 ◇ q2):=by
    intro q0 q1 q2
    exact ((h q0 q2 q0 q0).trans ((h q1 q2 q0 q0).symm)).symm
  have apc2 : forall (q3 q4 q5 q6 q7:G), (q3 ◇ (q7 ◇ q4)) = (q5 ◇ q6):=by
    intro q3 q4 q5 q6 q7
    exact ((apc1 q3 ((q6 ◇ q6) ◇ q7) (q7 ◇ q4)).symm).trans ((h q5 q6 q7 q4).symm)
  exact (apc2 x x (x ◇ (y ◇ x)) (z ◇ (w ◇ u)) y).trans ((apc2 z u (x ◇ (y ◇ x)) (z ◇ (w ◇ u)) w).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_48967_to_4338 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_48967_to_4338
