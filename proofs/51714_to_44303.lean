-- Equation51714 → Equation44303
-- Recorded verdict: true
-- Premise: x * y = ((z * x) * (y * w)) * u
-- Conclusion: x * x = y * ((z * (y * x)) * x)
-- Original submission SHA-256: 3a8161230d5c27b692c96c3a4b330d0fcce99d43e1ccc4667b2a03be0102dfc4
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = ((z ◇ x) ◇ (y ◇ w)) ◇ u
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = y ◇ ((z ◇ (y ◇ x)) ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3 q4:G), ((q2 ◇ q0) ◇ q4) = ((q1 ◇ q2) ◇ q3):=by
    intro q0 q1 q2 q3 q4
    exact (((congrArg (fun t => t ◇ q3) ((h q1 q2 q0 q0 (q4 ◇ q0)).symm)).symm).trans ((h (q2 ◇ q0) q4 (q0 ◇ q1) q0 q3).symm)).symm
  have apc1 : forall (q5 q6 q7 q8 q9:G), ((q5 ◇ (q9 ◇ q7)) ◇ q6) = (q7 ◇ q8):=by
    intro q5 q6 q7 q8 q9
    exact ((apc0 (q8 ◇ q5) q5 (q9 ◇ q7) q6 q5).symm).trans ((h q7 q8 q9 q5 q5).symm)
  have apc4 : forall (q10 q11 q12 q13:G), (q12 ◇ q13) = (q11 ◇ q10):=by
    intro q10 q11 q12 q13
    exact (((apc1 (q10 ◇ q12) q10 q11 q10 q13).symm).trans ((h q12 q13 q10 q11 q10).symm)).symm
  exact (apc4 (x ◇ x) (y ◇ ((z ◇ (y ◇ x)) ◇ x)) x x).trans ((apc4 (x ◇ x) (y ◇ ((z ◇ (y ◇ x)) ◇ x)) y ((z ◇ (y ◇ x)) ◇ x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_51714_to_44303 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_51714_to_44303
