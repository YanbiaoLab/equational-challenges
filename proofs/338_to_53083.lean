-- Equation338 → Equation53083
-- Recorded verdict: true
-- Premise: x * y = y * (z * x)
-- Conclusion: x * x = (((y * z) * y) * z) * z
-- Original submission SHA-256: ad21afed507ea58ee947e32abcfed04925ef59899bd28a927f6a9f614a8c2b37
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = y ◇ (z ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = (((y ◇ z) ◇ y) ◇ z) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3:G), (q2 ◇ (q0 ◇ q3)) = ((q1 ◇ q0) ◇ q2):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => q2 ◇ t) ((h q0 q3 q1).symm)).symm).trans ((h (q1 ◇ q0) q2 q3).symm)
  have apc1 : forall (q4 q5 q6 q7:G), ((q4 ◇ q7) ◇ q6) = (q5 ◇ q6):=by
    intro q4 q5 q6 q7
    exact ((apc0 q7 q4 q6 q5).symm).trans ((h q5 q6 q7).symm)
  have apc2 : forall (q8 q9 q10 q11 q12:G), (((q8 ◇ q9) ◇ q12) ◇ q11) = (q10 ◇ q11):=by
    intro q8 q9 q10 q11 q12
    exact ((congrArg (fun t => t ◇ q11) ((apc1 q8 q8 q12 q9).symm)).symm).trans (apc1 q8 q10 q11 q12)
  have apc3 : forall (q13 q14 q15 q16 q17 q18:G), ((((q13 ◇ q14) ◇ q15) ◇ q18) ◇ q17) = (q16 ◇ q17):=by
    intro q13 q14 q15 q16 q17 q18
    exact ((congrArg (fun t => t ◇ q17) ((apc2 q13 q14 (q13 ◇ q13) q18 q15).symm)).symm).trans (apc2 q13 q13 q16 q17 q18)
  have apc5 : forall (x y z:G), (y ◇ (z ◇ x)) = (y ◇ (x ◇ x)):=by
    intro x y z
    exact ((h x y z).symm).trans (h x y x)
  have apc7 : forall (q19 q20 q21 q22 q23 q24 q25:G), ((((q19 ◇ q20) ◇ q21) ◇ q22) ◇ (q23 ◇ q23)) = (q23 ◇ q24):=by
    intro q19 q20 q21 q22 q23 q24 q25
    exact ((apc5 q23 (((q19 ◇ q20) ◇ q21) ◇ q22) q25).symm).trans ((apc3 q19 q20 q21 q24 (q25 ◇ q23) q22).trans ((h q23 q24 q25).symm))
  have apc11 : forall (q0 q1 q2 q3:G), ((q1 ◇ q0) ◇ q2) = ((q0 ◇ q0) ◇ q2):=by
    intro q0 q1 q2 q3
    exact ((apc0 q0 q1 q2 q3).symm).trans (apc0 q0 q0 q2 q3)
  have apc12 : forall (q26 q27 q28:G), ((q28 ◇ q28) ◇ q27) = (q26 ◇ q27):=by
    intro q26 q27 q28
    exact ((apc11 q28 q26 q27 q26).symm).trans (apc1 q26 q26 q27 q28)
  have apc15 : forall (q26 q27 q28:G), (q27 ◇ q27) = (q26 ◇ q27):=by
    intro q26 q27 q28
    exact (((apc12 q26 q27 q28).symm).trans (apc12 q27 q27 q28)).symm
  have apc17 : forall (q19 q20 q21 q22 q23 q24 q25:G), (q23 ◇ q24) = (q23 ◇ q19):=by
    intro q19 q20 q21 q22 q23 q24 q25
    exact ((apc7 q19 q20 q21 q22 q23 q24 q25).symm).trans (apc7 q19 q20 q21 q22 q23 q19 q25)
  have apc19 : forall (q29 q30 q31:G), (q31 ◇ q31) = (q30 ◇ q29):=by
    intro q29 q30 q31
    exact (((apc17 q29 q29 q29 q29 q30 q31 q29).symm).trans ((apc15 q30 q31 q29).symm)).symm
  exact (apc19 (x ◇ x) (x ◇ x) x).trans (apc19 z (((y ◇ z) ◇ y) ◇ z) (x ◇ x))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_338_to_53083 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_338_to_53083
