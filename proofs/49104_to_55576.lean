-- Equation49104 → Equation55576
-- Recorded verdict: true
-- Premise: x * y = ((z * x) * w) * (x * w)
-- Conclusion: x * (x * x) = (y * x) * (x * x)
-- Original submission SHA-256: c6fb1e3cec7d661b9269f232416dcbf27869a5607e5ba5370caab00498350fee
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((z ◇ x) ◇ w) ◇ (x ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ (x ◇ x) = (y ◇ x) ◇ (x ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (q0 q1 q2 q3:G), ((q0 ◇ q1) ◇ (q2 ◇ (q0 ◇ q2))) = (q2 ◇ q3):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => t ◇ (q2 ◇ (q0 ◇ q2))) ((h q0 q1 q0 q2).symm)).symm).trans ((h q2 q3 (q0 ◇ q0) (q0 ◇ q2)).symm)
  have apc1 : forall (q4 q5 q6 q7 q8:G), ((q5 ◇ q7) ◇ (q5 ◇ q6)) = ((q4 ◇ q5) ◇ q8):=by
    intro q4 q5 q6 q7 q8
    exact ((congrArg (fun t => (q5 ◇ q7) ◇ t) (apc0 q4 q5 q5 q6)).symm).trans (apc0 q5 q7 (q4 ◇ q5) q8)
  have apc2 : forall (q9 q10 q11 q12 q13:G), ((q11 ◇ q10) ◇ (q11 ◇ q9)) = (q12 ◇ q13):=by
    intro q9 q10 q11 q12 q13
    exact (apc1 (q9 ◇ q12) q11 q9 q10 (q12 ◇ q11)).trans ((h q12 q13 q9 q11).symm)
  have apc3 : forall (q4 q5 q6 q7 q8:G), ((q5 ◇ q7) ◇ (q5 ◇ q6)) = ((q5 ◇ q4) ◇ (q5 ◇ q4)):=by
    intro q4 q5 q6 q7 q8
    exact (apc1 q4 q5 q6 q7 q8).trans ((apc1 q4 q5 q4 q4 q8).symm)
  have apc4 : forall (q14 q15 q16 q17:G), ((q15 ◇ q14) ◇ (q15 ◇ q14)) = (q16 ◇ q17):=by
    intro q14 q15 q16 q17
    exact ((apc3 q14 q15 q14 q14 q14).symm).trans (apc2 q14 q14 q15 q16 q17)
  exact ((apc4 (x ◇ (x ◇ x)) ((y ◇ x) ◇ (x ◇ x)) x (x ◇ x)).symm).trans (apc4 (x ◇ (x ◇ x)) ((y ◇ x) ◇ (x ◇ x)) (y ◇ x) (x ◇ x))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_49104_to_55576 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_49104_to_55576
