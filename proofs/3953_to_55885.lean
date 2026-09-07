-- Equation3953 → Equation55885
-- Recorded verdict: true
-- Premise: x * y = (y * (x * x)) * z
-- Conclusion: x * (y * x) = (z * z) * (w * y)
-- Original submission SHA-256: d33cde0b2bb88d58102bf5276529e1c21880c09ce926ffee4eb0c1bf69d25f93
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (y ◇ (x ◇ x)) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ x) = (z ◇ z) ◇ (w ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3:G), (q2 ◇ (q1 ◇ (q0 ◇ q0))) = ((q0 ◇ q1) ◇ q3):=by
    intro q0 q1 q2 q3
    exact (((congrArg (fun t => t ◇ q3) ((h q0 q1 (q2 ◇ q2)).symm)).symm).trans ((h q2 (q1 ◇ (q0 ◇ q0)) q3).symm)).symm
  have apc1 : forall (q4 q5 q6 q7 q8:G), ((q4 ◇ q5) ◇ q6) = (q7 ◇ q8):=by
    intro q4 q5 q6 q7 q8
    exact ((apc0 q4 q5 (q8 ◇ (q7 ◇ q7)) q6).symm).trans ((h q7 q8 (q5 ◇ (q4 ◇ q4))).symm)
  have apc2 : forall (q9 q10 q11 q12 q13 q14:G), (q13 ◇ (q9 ◇ q10)) = ((q11 ◇ q12) ◇ q14):=by
    intro q9 q10 q11 q12 q13 q14
    exact (((congrArg (fun t => t ◇ q14) (apc1 q9 q10 (q13 ◇ q13) q11 q12)).symm).trans ((h q13 (q9 ◇ q10) q14).symm)).symm
  have apc3 : forall (q9 q10 q11 q12 q13 q14:G), (q13 ◇ (q9 ◇ q10)) = (q11 ◇ (q11 ◇ q11)):=by
    intro q9 q10 q11 q12 q13 q14
    exact (apc2 q9 q10 q11 q12 q13 q14).trans ((apc2 q11 q11 q11 q12 q11 q14).symm)
  exact (apc3 y x (x ◇ (y ◇ x)) (x ◇ (y ◇ x)) x (x ◇ (y ◇ x))).trans ((apc3 w y (x ◇ (y ◇ x)) (x ◇ (y ◇ x)) (z ◇ z) (x ◇ (y ◇ x))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_3953_to_55885 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_3953_to_55885
