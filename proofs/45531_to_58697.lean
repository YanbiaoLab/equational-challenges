-- Equation45531 → Equation58697
-- Recorded verdict: true
-- Premise: x * y = y * (((z * w) * w) * x)
-- Conclusion: (x * y) * z = x * (x * (x * x))
-- Original submission SHA-256: 6332369b21811ed9aa145424207b564e839d0a2d4967b77d72b850600c80734f
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = y ◇ (((z ◇ w) ◇ w) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ z = x ◇ (x ◇ (x ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3 q4 q5:G), (q4 ◇ (q1 ◇ ((q5 ◇ q3) ◇ q3))) = ((((q2 ◇ q0) ◇ q0) ◇ q1) ◇ q4):=by
    intro q0 q1 q2 q3 q4 q5
    exact ((congrArg (fun t => q4 ◇ t) ((h q1 ((q5 ◇ q3) ◇ q3) q2 q0).symm)).symm).trans ((h (((q2 ◇ q0) ◇ q0) ◇ q1) q4 q5 q3).symm)
  have apc1 : forall (q6 q7 q8 q9 q10:G), ((((q8 ◇ q6) ◇ q6) ◇ q7) ◇ q10) = (q10 ◇ (q9 ◇ q7)):=by
    intro q6 q7 q8 q9 q10
    exact (((congrArg (fun t => q10 ◇ t) ((h q9 q7 q6 q9).symm)).symm).trans (apc0 q6 q7 q8 q9 q10 (q6 ◇ q9))).symm
  have apc2 : forall (q11 q12 q13 q14:G), (q14 ◇ (q13 ◇ (q11 ◇ q12))) = (q13 ◇ q14):=by
    intro q11 q12 q13 q14
    exact ((congrArg (fun t => q14 ◇ t) (apc1 q12 q12 q11 q11 q13)).symm).trans ((h q13 q14 (q11 ◇ q12) q12).symm)
  have apc3 : forall (q15 q16 q17:G), (q17 ◇ (q15 ◇ q16)) = (q16 ◇ q17):=by
    intro q15 q16 q17
    exact ((congrArg (fun t => q17 ◇ t) (apc2 q15 q15 q15 q16)).symm).trans (apc2 q15 (q15 ◇ q15) q16 q17)
  have apc4 : forall (q18 q19 q20 q21:G), ((q18 ◇ q19) ◇ q21) = (q20 ◇ q21):=by
    intro q18 q19 q20 q21
    exact (((apc3 q19 q20 q21).symm).trans (((congrArg (fun t => q21 ◇ t) (apc3 q18 q19 q20)).symm).trans (apc3 q20 (q18 ◇ q19) q21))).symm
  have apc7 : forall (q22 q23 q24 q25 q26:G), (q24 ◇ q23) = (q22 ◇ q24):=by
    intro q22 q23 q24 q25 q26
    exact ((apc3 q25 q24 q23).symm).trans ((((apc4 q26 q22 q23 (q25 ◇ q24)).symm).trans (apc3 q25 q24 (q26 ◇ q22))).trans (apc3 q26 q22 q24))
  exact (apc7 (x ◇ (x ◇ x)) z (x ◇ y) ((x ◇ y) ◇ z) ((x ◇ y) ◇ z)).trans (apc7 x (x ◇ y) (x ◇ (x ◇ x)) ((x ◇ y) ◇ z) ((x ◇ y) ◇ z))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_45531_to_58697 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_45531_to_58697
