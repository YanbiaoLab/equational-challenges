-- Equation48154 → Equation42645
-- Recorded verdict: true
-- Premise: x * y = (y * (z * w)) * (y * z)
-- Conclusion: x * y = x * (x * ((z * w) * u))
-- Original submission SHA-256: 330f12d9115e8b4d59c5adfbb18c3e4a9dba68e0ec49531ff72df76bb5635f00
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (y ◇ (z ◇ w)) ◇ (y ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = x ◇ (x ◇ ((z ◇ w) ◇ u))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (q0 q1 q2:G), (q1 ◇ q2) = (q0 ◇ q2):=by
    intro q0 q1 q2
    exact ((h q0 q2 q0 q0).trans ((h q1 q2 q0 q0).symm)).symm
  have apc1 : forall (x y z w:G), (y ◇ y) = (x ◇ y):=by
    intro x y z w
    exact ((h x y z w).trans ((h y y z w).symm)).symm
  have apc2 : forall (q3 q4 q5 q6:G), (q3 ◇ (q5 ◇ q6)) = (q4 ◇ q5):=by
    intro q3 q4 q5 q6
    exact ((apc0 q3 (q5 ◇ (q6 ◇ q3)) (q5 ◇ q6)).symm).trans ((h q4 q5 q6 q3).symm)
  have apc4 : forall (q7 q8 q9 q10:G), (q8 ◇ (q7 ◇ q10)) = (q9 ◇ q10):=by
    intro q7 q8 q9 q10
    exact ((congrArg (fun t => q8 ◇ t) (apc1 q7 q10 q7 q7)).symm).trans (apc2 q8 q9 q10 q10)
  have apc6 : forall (q11 q12 q13 q14:G), (q12 ◇ q13) = (q11 ◇ q14):=by
    intro q11 q12 q13 q14
    exact (((apc4 q13 q11 q11 q14).symm).trans (apc2 q11 q12 q13 q14)).symm
  have apc7 : forall (q11 q12 q14 q13:G), (q12 ◇ q12) = (q11 ◇ q14):=by
    intro q11 q12 q14 q13
    exact (((apc6 q11 q12 q13 q14).symm).trans (apc6 q12 q12 q13 q12)).symm
  exact ((apc7 x (x ◇ y) y (x ◇ y)).symm).trans (apc7 x (x ◇ y) (x ◇ ((z ◇ w) ◇ u)) (x ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_48154_to_42645 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_48154_to_42645
