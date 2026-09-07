-- Equation49193 → Equation58913
-- Recorded verdict: true
-- Premise: x * y = ((z * y) * w) * (w * x)
-- Conclusion: (x * y) * z = z * (w * (z * y))
-- Original submission SHA-256: b777ab46b06fce5687f8fe395c2c928dfe8d4cadd6fb7437affe3c14867f14cf
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((z ◇ y) ◇ w) ◇ (w ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ z = z ◇ (w ◇ (z ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3:G), ((q0 ◇ q1) ◇ ((q3 ◇ q0) ◇ q2)) = (q2 ◇ q3):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => t ◇ ((q3 ◇ q0) ◇ q2)) ((h q0 q1 q0 q3).symm)).symm).trans ((h q2 q3 (q0 ◇ q1) (q3 ◇ q0)).symm)
  have apc1 : forall (q4 q5 q6:G), (q5 ◇ q6) = (q5 ◇ q4):=by
    intro q4 q5 q6
    exact (((apc0 (q4 ◇ q6) (q4 ◇ (q4 ◇ q6)) q5 q4).symm).trans ((h q5 q6 q4 (q4 ◇ (q4 ◇ q6))).symm)).symm
  have apc2 : forall (q7 q8 q9 q10 q11:G), (q8 ◇ q9) = (q7 ◇ q9):=by
    intro q7 q8 q9 q10 q11
    exact (((apc0 q10 q11 q7 q9).symm).trans (((congrArg (fun t => (q10 ◇ q11) ◇ t) (apc1 q7 (q9 ◇ q10) q8)).symm).trans (apc0 q10 q11 q8 q9))).symm
  have apc4 : forall (q12 q13 q14 q15:G), (q14 ◇ q13) = (q12 ◇ q15):=by
    intro q12 q13 q14 q15
    exact (((apc2 q12 q14 q15 q12 q12).symm).trans (apc1 q13 q14 q15)).symm
  exact (apc4 ((x ◇ y) ◇ z) z (x ◇ y) (z ◇ (w ◇ (z ◇ y)))).trans ((apc4 ((x ◇ y) ◇ z) (w ◇ (z ◇ y)) z (z ◇ (w ◇ (z ◇ y)))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_49193_to_58913 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_49193_to_58913
