-- Equation3557 → Equation61412
-- Recorded verdict: true
-- Premise: x * y = y * ((y * x) * z)
-- Conclusion: (x * y) * z = (y * (x * y)) * w
-- Original submission SHA-256: 2eefeca792dd53b133b6fd4b406e6713ea89cc7ce2c6da50809a8e3099c53ccf
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = y ◇ ((y ◇ x) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ z = (y ◇ (x ◇ y)) ◇ w
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2:G), (q2 ◇ (q0 ◇ (q2 ◇ q1))) = (q1 ◇ q2):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => q2 ◇ t) ((h q0 (q2 ◇ q1) q0).symm)).symm).trans ((h q1 q2 (((q2 ◇ q1) ◇ q0) ◇ q0)).symm)
  have apc1 : forall (q3 q4 q5:G), (q4 ◇ q5) = (q3 ◇ q5):=by
    intro q3 q4 q5
    exact (((apc0 (q5 ◇ q4) q3 q5).symm).trans ((h q4 q5 (q5 ◇ q3)).symm)).symm
  have apc2 : forall (q6 q7 q8:G), (q8 ◇ (q6 ◇ q7)) = ((q7 ◇ q6) ◇ q8):=by
    intro q6 q7 q8
    exact ((congrArg (fun t => q8 ◇ t) (apc0 q8 q6 q7)).symm).trans (apc0 q7 (q7 ◇ q6) q8)
  have apc3 : forall (q9 q10 q11 q12:G), ((q10 ◇ q9) ◇ q12) = ((q10 ◇ q9) ◇ q11):=by
    intro q9 q10 q11 q12
    exact (((apc2 q9 q10 q12).symm).trans (apc1 q11 q12 (q9 ◇ q10))).trans (apc2 q9 q10 q11)
  have apc4 : forall (q13 q14 q15 q16:G), ((q15 ◇ q14) ◇ q16) = ((q15 ◇ q13) ◇ q16):=by
    intro q13 q14 q15 q16
    exact (((apc2 q13 q15 q16).symm).trans (((congrArg (fun t => q16 ◇ t) (apc1 q13 q14 q15)).symm).trans (apc2 q14 q15 q16))).symm
  have apc6 : forall (q17 q18 q19 q20 q21:G), ((q19 ◇ q18) ◇ q20) = ((q17 ◇ q18) ◇ q21):=by
    intro q17 q18 q19 q20 q21
    exact (((congrArg (fun t => t ◇ q21) (apc1 q17 q19 q18)).symm).trans (apc3 q18 q19 q20 q21)).symm
  have apc12 : forall (q22 q23 q24 q25 q26 q27:G), ((q26 ◇ q24) ◇ q27) = ((q22 ◇ q25) ◇ q23):=by
    intro q22 q23 q24 q25 q26 q27
    exact (((apc6 q22 q25 q26 q27 q23).symm).trans (apc4 q24 q25 q26 q27)).symm
  have apc16 : forall (q22 q23 q24 q25 q26 q27:G), ((q24 ◇ q24) ◇ q24) = ((q22 ◇ q25) ◇ q23):=by
    intro q22 q23 q24 q25 q26 q27
    exact (((apc12 q22 q23 q24 q25 q26 q27).symm).trans (apc12 q24 q24 q24 q24 q26 q27)).symm
  exact ((apc16 x z ((x ◇ y) ◇ z) y ((x ◇ y) ◇ z) ((x ◇ y) ◇ z)).symm).trans (apc16 y w ((x ◇ y) ◇ z) (x ◇ y) ((x ◇ y) ◇ z) ((x ◇ y) ◇ z))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_3557_to_61412 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_3557_to_61412
