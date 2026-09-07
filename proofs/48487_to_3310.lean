-- Equation48487 → Equation3310
-- Recorded verdict: true
-- Premise: x * y = (z * (w * w)) * (y * x)
-- Conclusion: x * y = x * (x * (y * z))
-- Original submission SHA-256: ef7af5f82cff862813e175d80548099c3b45353119e54c6c500f9ba3a88b9d24
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ (w ◇ w)) ◇ (y ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = x ◇ (x ◇ (y ◇ z))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2:G), ((q0 ◇ q0) ◇ (q2 ◇ q1)) = (q1 ◇ q2):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ (q2 ◇ q1)) ((h q0 q0 q0 q0).symm)).symm).trans ((h q1 q2 (q0 ◇ (q0 ◇ q0)) q0).symm)
  have apc1 : forall (q3 q4 q5 q6 q7:G), ((q5 ◇ q4) ◇ (q6 ◇ (q3 ◇ q3))) = (q5 ◇ q4):=by
    intro q3 q4 q5 q6 q7
    exact (((apc0 q7 q5 q4).symm).trans (((congrArg (fun t => (q7 ◇ q7) ◇ t) ((h q4 q5 q6 q3).symm)).symm).trans (apc0 q7 (q5 ◇ q4) (q6 ◇ (q3 ◇ q3))))).symm
  have apc2 : forall (q8 q9 q10 q11:G), ((q10 ◇ q9) ◇ (q8 ◇ q8)) = (q10 ◇ q9):=by
    intro q8 q9 q10 q11
    exact (((apc0 q11 q10 q9).symm).trans (((congrArg (fun t => (q11 ◇ q11) ◇ t) (apc0 q8 q9 q10)).symm).trans (apc0 q11 (q10 ◇ q9) (q8 ◇ q8)))).symm
  have apc3 : forall (q12 q13 q14:G), (q14 ◇ (q12 ◇ q12)) = (q13 ◇ q13):=by
    intro q12 q13 q14
    exact ((apc2 q13 (q12 ◇ q12) q14 q12).symm).trans ((h q13 q13 q14 q12).symm)
  have apc10 : forall (q15 q16 q17:G), (q17 ◇ q16) = (q15 ◇ q15):=by
    intro q15 q16 q17
    exact (((apc3 (q15 ◇ q15) q15 (q17 ◇ q16)).symm).trans (apc1 q15 q16 q17 (q15 ◇ q15) q15)).symm
  exact (apc10 (x ◇ y) y x).trans ((apc10 (x ◇ y) (x ◇ (y ◇ z)) x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_48487_to_3310 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_48487_to_3310
