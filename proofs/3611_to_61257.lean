-- Equation3611 → Equation61257
-- Recorded verdict: true
-- Premise: x * y = z * ((y * w) * x)
-- Conclusion: (x * y) * y = (z * (x * y)) * z
-- Original submission SHA-256: e2189d4d0af76a3ca1dbc7b5204bf5754e37998a61198bd8d19f0494b9463b04
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ ((y ◇ w) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ y = (z ◇ (x ◇ y)) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3 q4:G), (((q2 ◇ q0) ◇ q1) ◇ q3) = (q4 ◇ (q1 ◇ q2)):=by
    intro q0 q1 q2 q3 q4
    exact (((congrArg (fun t => q4 ◇ t) ((h q1 q2 (q3 ◇ q0) q0).symm)).symm).trans ((h ((q2 ◇ q0) ◇ q1) q3 q4 q0).symm)).symm
  have apc1 : forall (q5 q6 q7 q8 q9:G), (((q8 ◇ q5) ◇ (q9 ◇ q7)) ◇ q6) = (q8 ◇ q9):=by
    intro q5 q6 q7 q8 q9
    exact (apc0 q5 (q9 ◇ q7) q8 q6 q5).trans ((h q8 q9 q5 q7).symm)
  have apc2 : forall (q10 q11 q12 q13 q14 q15:G), ((q12 ◇ (q13 ◇ q11)) ◇ q14) = ((q11 ◇ q10) ◇ q15):=by
    intro q10 q11 q12 q13 q14 q15
    exact ((congrArg (fun t => t ◇ q14) (apc0 q10 q13 q11 (q15 ◇ q10) q12)).symm).trans (apc1 q13 q14 q10 (q11 ◇ q10) q15)
  have apc3 : forall (q16 q17 q18 q19 q20 q21 q22:G), ((q20 ◇ (q21 ◇ q19)) ◇ q22) = ((q17 ◇ q16) ◇ q18):=by
    intro q16 q17 q18 q19 q20 q21 q22
    exact (((apc2 q16 q17 q19 q16 q16 q18).symm).trans ((apc2 (q16 ◇ q17) q19 q20 q21 q22 q16).symm)).symm
  have apc14 : forall (q16 q17 q18 q19 q20 q21 q22:G), ((q19 ◇ q19) ◇ q19) = ((q17 ◇ q16) ◇ q18):=by
    intro q16 q17 q18 q19 q20 q21 q22
    exact (((apc3 q16 q17 q18 q19 q20 q21 q22).symm).trans (apc3 q19 q19 q19 q19 q20 q21 q22)).symm
  exact ((apc14 y x y ((x ◇ y) ◇ y) ((x ◇ y) ◇ y) ((x ◇ y) ◇ y) ((x ◇ y) ◇ y)).symm).trans (apc14 (x ◇ y) z z ((x ◇ y) ◇ y) ((x ◇ y) ◇ y) ((x ◇ y) ◇ y) ((x ◇ y) ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_3611_to_61257 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_3611_to_61257
