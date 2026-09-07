-- Equation59001 → Equation58400
-- Recorded verdict: true
-- Premise: (x * y) * z = w * (z * (u * y))
-- Conclusion: (x * y) * x = x * (x * (y * z))
-- Original submission SHA-256: 040d3d4679218bf384a9c5c6ab6483501a620638e2b28526c0aeb003d701b732
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), (x ◇ y) ◇ z = w ◇ (z ◇ (u ◇ y))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ x = x ◇ (x ◇ (y ◇ z))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (x y z w u:G), ((y ◇ y) ◇ z) = ((x ◇ y) ◇ z):=by
    intro x y z w u
    exact ((h x y z x x).trans ((h y y z x x).symm)).symm
  have apc1 : forall (q0 q1 q2 q3:G), ((q1 ◇ q2) ◇ q3) = ((q0 ◇ q2) ◇ q3):=by
    intro q0 q1 q2 q3
    exact ((h q0 q2 q3 q0 q0).trans ((h q1 q2 q3 q0 q0).symm)).symm
  have apc3 : forall (q4 q0 q5 q6 q7 q1 q3:G), (q7 ◇ ((q0 ◇ q5) ◇ q6)) = ((q1 ◇ (q4 ◇ q5)) ◇ q3):=by
    intro q4 q0 q5 q6 q7 q1 q3
    exact ((congrArg (fun t => q7 ◇ t) ((h q0 q5 q6 q3 q4).symm)).symm).trans ((h q1 (q4 ◇ q5) q3 q7 q6).symm)
  have apc5 : forall (q8 q9 q10 q11:G), (((q8 ◇ q9) ◇ q10) ◇ q11) = ((q10 ◇ q10) ◇ q11):=by
    intro q8 q9 q10 q11
    exact ((congrArg (fun t => t ◇ q11) (apc0 q8 q9 q10 q8 q8)).symm).trans ((apc0 (q9 ◇ q9) q10 q11 q8 q8).symm)
  have apc6 : forall (q12 q13 q14 q15:G), (q13 ◇ (q15 ◇ (q12 ◇ q14))) = ((q14 ◇ q14) ◇ q15):=by
    intro q12 q13 q14 q15
    exact ((apc0 q12 q14 q15 q12 q12).trans (h q12 q14 q15 q13 q12)).symm
  have apc7 : forall (q16 q17 q18 q19:G), ((q17 ◇ q17) ◇ q18) = ((q16 ◇ q16) ◇ q19):=by
    intro q16 q17 q18 q19
    exact ((apc6 (q16 ◇ q16) q16 q17 q18).symm).trans ((((congrArg (fun t => q16 ◇ t) ((apc3 q16 q16 q16 q17 q18 q19 (q16 ◇ q16)).symm)).symm).trans (apc6 q16 q16 q16 (q19 ◇ (q16 ◇ q16)))).trans (apc6 q16 (q16 ◇ q16) q16 q19))
  have apc11 : forall (q20 q21 q22 q23:G), ((q21 ◇ q22) ◇ q23) = ((q20 ◇ q20) ◇ q23):=by
    intro q20 q21 q22 q23
    exact (((apc5 q20 q20 q20 q23).symm).trans (((congrArg (fun t => t ◇ q23) (apc7 q20 q20 q22 q20)).symm).trans (apc1 q21 (q20 ◇ q20) q22 q23))).symm
  have apc16 : forall (q24 q25 q26 q27 q28:G), ((q26 ◇ q27) ◇ q28) = ((q24 ◇ q25) ◇ q28):=by
    intro q24 q25 q26 q27 q28
    exact ((apc11 q27 q24 q25 q28).trans (apc0 q26 q27 q28 q24 q24)).symm
  exact (calc
    ((x ◇ y) ◇ x) = ((x ◇ z) ◇ x):=apc16 x z x y x
    _ = (x ◇ (x ◇ (y ◇ z))):=((h x z x x y).symm).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_59001_to_58400 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_59001_to_58400
