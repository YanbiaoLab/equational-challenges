-- Equation48099 → Equation49479
-- Recorded verdict: true
-- Premise: x * y = (y * (z * x)) * (x * w)
-- Conclusion: x * x = (y * (x * (x * y))) * z
-- Original submission SHA-256: b9c525361beb050c0715c4ad215ad3cb3f27ebb0f32b1ec03a288090c6195313
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (y ◇ (z ◇ x)) ◇ (x ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = (y ◇ (x ◇ (x ◇ y))) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3 q4:G), (q3 ◇ (q0 ◇ (q1 ◇ q4))) = ((q4 ◇ q0) ◇ (q3 ◇ q2)):=by
    intro q0 q1 q2 q3 q4
    exact (((congrArg (fun t => t ◇ (q3 ◇ q2)) ((h q4 q0 q1 q3).symm)).symm).trans ((h q3 (q0 ◇ (q1 ◇ q4)) q4 q2).symm)).symm
  have apc1 : forall (q0 q1 q2 q3 q4:G), ((q4 ◇ q0) ◇ (q3 ◇ q2)) = ((q4 ◇ q0) ◇ (q3 ◇ q0)):=by
    intro q0 q1 q2 q3 q4
    exact ((apc0 q0 q0 q2 q3 q4).symm).trans (apc0 q0 q0 q0 q3 q4)
  have apc4 : forall (q5 q6 q7 q8:G), (q6 ◇ ((q8 ◇ q6) ◇ (q5 ◇ q6))) = (q6 ◇ q7):=by
    intro q5 q6 q7 q8
    exact ((congrArg (fun t => q6 ◇ t) (apc1 q6 ((q8 ◇ q6) ◇ (q5 ◇ q7)) q7 q5 q8)).symm).trans ((apc0 (q8 ◇ q6) q5 q5 q6 q7).trans ((h q6 q7 q8 q5).symm))
  have apc5 : forall (q5 q6 q7 q8:G), (q6 ◇ q7) = (q6 ◇ q5):=by
    intro q5 q6 q7 q8
    exact ((apc4 q5 q6 q7 q5).symm).trans (apc4 q5 q6 q5 q5)
  have apc7 : forall (q9 q10 q11:G), ((q9 ◇ q10) ◇ (q10 ◇ q10)) = ((q9 ◇ q10) ◇ q11):=by
    intro q9 q10 q11
    exact ((apc1 q10 ((q9 ◇ q10) ◇ (q10 ◇ q9)) q9 q10 q9).symm).trans (((congrArg (fun t => (q9 ◇ q10) ◇ t) ((h q10 q9 q9 (q9 ◇ q10)).symm)).symm).trans (apc4 q10 (q9 ◇ q10) q11 q9))
  have apc8 : forall (q9 q10 q11:G), ((q9 ◇ q10) ◇ q11) = ((q9 ◇ q10) ◇ q9):=by
    intro q9 q10 q11
    exact ((apc7 q9 q10 q11).symm).trans (apc7 q9 q10 q9)
  have apc9 : forall (q12 q13 q14:G), ((q13 ◇ q14) ◇ q13) = ((q13 ◇ q12) ◇ q13):=by
    intro q12 q13 q14
    exact (((apc8 q13 q12 q12).symm).trans (((congrArg (fun t => t ◇ q12) (apc5 q12 q13 q14 q12)).symm).trans (apc8 q13 q14 q12))).symm
  have apc11 : forall (q15 q16 q17 q18:G), ((q18 ◇ q16) ◇ q17) = ((q18 ◇ q15) ◇ q18):=by
    intro q15 q16 q17 q18
    exact (((apc9 q15 q18 q16).symm).trans (apc5 q17 (q18 ◇ q16) q18 q15)).symm
  have apc14 : forall (q19 q20 q21:G), ((q21 ◇ q19) ◇ q21) = (q20 ◇ q21):=by
    intro q19 q20 q21
    exact ((apc11 q19 (q19 ◇ q20) (q20 ◇ q19) q21).symm).trans ((h q20 q21 q19 q19).symm)
  have apc15 : forall (q19 q20 q21:G), (q20 ◇ q21) = (q19 ◇ q21):=by
    intro q19 q20 q21
    exact ((apc14 q19 q20 q21).symm).trans (apc14 q19 q19 q21)
  have apc16 : forall (q22 q23 q24 q25:G), (q24 ◇ q23) = (q22 ◇ q25):=by
    intro q22 q23 q24 q25
    exact (((apc15 q22 q24 q25).symm).trans (apc5 q23 q24 q25 q22)).symm
  exact (apc16 (x ◇ x) x x ((y ◇ (x ◇ (x ◇ y))) ◇ z)).trans ((apc16 (x ◇ x) z (y ◇ (x ◇ (x ◇ y))) ((y ◇ (x ◇ (x ◇ y))) ◇ z)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_48099_to_49479 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_48099_to_49479
