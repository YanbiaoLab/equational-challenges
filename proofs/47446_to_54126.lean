-- Equation47446 → Equation54126
-- Recorded verdict: true
-- Premise: x * y = (z * y) * ((w * u) * z)
-- Conclusion: x * (y * x) = z * (z * (z * x))
-- Original submission SHA-256: 0c2a0d107c8c2ac8461ff9c94bbe19b810d2449ca2a3bca40244d6c7accf1719
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = (z ◇ y) ◇ ((w ◇ u) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ x) = z ◇ (z ◇ (z ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2:G), (q1 ◇ q2) = (q0 ◇ q2):=by
    intro q0 q1 q2
    exact ((h q0 q2 q0 q0 q0).trans ((h q1 q2 q0 q0 q0).symm)).symm
  have apc2 : forall (q3 q4 q5 q6 q7 q8:G), (q3 ◇ ((q5 ◇ q4) ◇ q8)) = (q6 ◇ q7):=by
    intro q3 q4 q5 q6 q7 q8
    exact ((apc0 q3 (q8 ◇ q7) ((q5 ◇ q4) ◇ q8)).symm).trans ((h q6 q7 q8 q5 q4).symm)
  have apc3 : forall (q9 q10 q11 q12:G), (q11 ◇ q12) = (q9 ◇ q10):=by
    intro q9 q10 q11 q12
    exact (((apc2 q9 q9 q9 q9 q10 q9).symm).trans (apc2 q9 q9 q9 q11 q12 q9)).symm
  exact (apc3 (x ◇ (y ◇ x)) (z ◇ (z ◇ (z ◇ x))) x (y ◇ x)).trans ((apc3 (x ◇ (y ◇ x)) (z ◇ (z ◇ (z ◇ x))) z (z ◇ (z ◇ x))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_47446_to_54126 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_47446_to_54126
