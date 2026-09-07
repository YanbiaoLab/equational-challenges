-- Equation3750 → Equation60617
-- Recorded verdict: true
-- Premise: x * y = (y * x) * (x * z)
-- Conclusion: (x * y) * z = (z * x) * (w * x)
-- Original submission SHA-256: 845f37484accf2582c452c9fccfcbe640e6c125e23acd8633a04c649e172f6dd
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (y ◇ x) ◇ (x ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ z = (z ◇ x) ◇ (w ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z:G), ((y ◇ x) ◇ (x ◇ z)) = ((y ◇ x) ◇ (x ◇ x)):=by
    intro x y z
    exact ((h x y z).symm).trans (h x y x)
  have apc1 : forall (q0 q1:G), ((q1 ◇ q0) ◇ (q0 ◇ q0)) = (q0 ◇ q1):=by
    intro q0 q1
    exact ((apc0 q0 q1 q0).symm).trans ((h q0 q1 q0).symm)
  have apc2 : forall (q2 q3 q4:G), ((q4 ◇ (q3 ◇ q2)) ◇ (q2 ◇ q3)) = ((q3 ◇ q2) ◇ q4):=by
    intro q2 q3 q4
    exact ((congrArg (fun t => (q4 ◇ (q3 ◇ q2)) ◇ t) ((h q2 q3 q2).symm)).symm).trans ((h (q3 ◇ q2) q4 (q2 ◇ q2)).symm)
  have apc3 : forall (q5 q6 q7:G), ((q7 ◇ q6) ◇ (q5 ◇ q7)) = ((q7 ◇ q5) ◇ (q6 ◇ q7)):=by
    intro q5 q6 q7
    exact (((congrArg (fun t => t ◇ (q6 ◇ q7)) ((h q7 q5 q6).symm)).symm).trans (apc2 q6 q7 (q5 ◇ q7))).symm
  have apc5 : forall (q2 q3 q8 q9:G), ((q2 ◇ q3) ◇ ((q2 ◇ q8) ◇ q9)) = ((q2 ◇ q3) ◇ (q8 ◇ q2)):=by
    intro q2 q3 q8 q9
    exact (((congrArg (fun t => t ◇ ((q2 ◇ q8) ◇ q9)) ((h q2 q3 q8).symm)).symm).trans ((h (q2 ◇ q8) (q3 ◇ q2) q9).symm)).trans (apc3 q3 q8 q2)
  have apc6 : forall (q10 q11 q12 q13:G), ((q11 ◇ q12) ◇ (q13 ◇ q11)) = ((q11 ◇ q10) ◇ (q12 ◇ q11)):=by
    intro q10 q11 q12 q13
    exact ((((apc5 q11 q12 q10 (q13 ◇ q11)).trans (apc3 q10 q12 q11)).symm).trans (((congrArg (fun t => (q11 ◇ q12) ◇ t) (apc3 q10 q13 q11)).symm).trans (apc5 q11 q12 q13 (q10 ◇ q11)))).symm
  have apc7 : forall (q14 q15 q16:G), ((q16 ◇ q14) ◇ (q15 ◇ q16)) = ((q16 ◇ q15) ◇ q16):=by
    intro q14 q15 q16
    exact ((apc3 q14 q15 q16).symm).trans ((apc6 (q16 ◇ q15) q16 q15 q14).trans (apc2 q15 q16 q16))
  have apc8 : forall (q17 q18 q19:G), ((q17 ◇ q19) ◇ q17) = ((q17 ◇ q18) ◇ q17):=by
    intro q17 q18 q19
    exact ((((apc2 q18 q17 q17).symm).trans ((apc6 (q17 ◇ q18) q17 q18 q19).symm)).trans (apc7 q18 q19 q17)).symm
  have apc9 : forall (q17 q18 q19:G), ((q17 ◇ q18) ◇ q17) = ((q17 ◇ q17) ◇ q17):=by
    intro q17 q18 q19
    exact ((apc8 q17 q18 q19).symm).trans (apc8 q17 q17 q19)
  have apc10 : forall (q20 q21 q22 q23:G), ((q20 ◇ q21) ◇ ((q20 ◇ q22) ◇ q23)) = ((q20 ◇ q20) ◇ q20):=by
    intro q20 q21 q22 q23
    exact ((congrArg (fun t => t ◇ ((q20 ◇ q22) ◇ q23)) (apc1 q20 q21)).symm).trans ((((congrArg (fun t => t ◇ ((q20 ◇ q22) ◇ q23)) (apc0 q20 q21 q22)).symm).trans (apc0 (q20 ◇ q22) (q21 ◇ q20) q23)).trans (((apc1 (q20 ◇ q22) (q21 ◇ q20)).trans (apc7 q22 q21 q20)).trans (apc9 q20 q21 ((q20 ◇ q21) ◇ q20))))
  have apc11 : forall (q24 q14 q15 q16:G), (((q15 ◇ q14) ◇ q15) ◇ (q15 ◇ q16)) = ((q16 ◇ q15) ◇ (q15 ◇ q24)):=by
    intro q24 q14 q15 q16
    exact ((congrArg (fun t => t ◇ (q15 ◇ q16)) (apc7 q16 q14 q15)).symm).trans (((congrArg (fun t => t ◇ (q15 ◇ q16)) ((apc6 q24 q15 q16 q14).symm)).symm).trans (apc2 q15 q16 (q15 ◇ q24)))
  have apc12 : forall (q24 q14 q15 q16:G), ((q16 ◇ q15) ◇ (q15 ◇ q14)) = ((q16 ◇ q15) ◇ (q15 ◇ q24)):=by
    intro q24 q14 q15 q16
    exact (((apc11 q24 q14 q15 q16).symm).trans (apc11 q14 q14 q15 q16)).symm
  have apc13 : forall (q25 q26 q27:G), ((q27 ◇ q26) ◇ (q26 ◇ q25)) = ((q27 ◇ q26) ◇ q27):=by
    intro q25 q26 q27
    exact ((apc12 q25 q27 q26 q27).symm).trans (apc7 q26 q26 q27)
  have apc14 : forall (q28 q29 q30:G), ((q30 ◇ q30) ◇ q30) = ((q29 ◇ q28) ◇ q30):=by
    intro q28 q29 q30
    exact (((apc13 q29 (q29 ◇ q28) q30).trans (apc9 q30 (q29 ◇ q28) ((q30 ◇ (q29 ◇ q28)) ◇ q30))).symm).trans (((congrArg (fun t => (q30 ◇ (q29 ◇ q28)) ◇ t) (apc13 q28 q28 q29)).symm).trans ((h (q29 ◇ q28) q30 (q28 ◇ q28)).symm))
  have apc15 : forall (q31 q32 q33 q34:G), ((q34 ◇ q33) ◇ (q32 ◇ q31)) = ((q34 ◇ q34) ◇ q34):=by
    intro q31 q32 q33 q34
    exact ((apc2 q33 q34 (q32 ◇ q31)).symm).trans ((((congrArg (fun t => t ◇ (q33 ◇ q34)) (apc14 q31 q32 (q34 ◇ q33))).symm).trans (apc2 q33 q34 ((q34 ◇ q33) ◇ (q34 ◇ q33)))).trans (apc10 q34 q33 q33 (q34 ◇ q33)))
  have apc16 : forall (q35 q36 q37 q38 q39:G), ((q38 ◇ q37) ◇ q39) = ((q36 ◇ q35) ◇ q39):=by
    intro q35 q36 q37 q38 q39
    exact (((apc14 q35 q36 q39).symm).trans (apc14 q37 q38 q39)).symm
  have apc18 : forall (q40 q41 q42:G), ((q41 ◇ q41) ◇ q41) = ((q40 ◇ q40) ◇ q40):=by
    intro q40 q41 q42
    exact (((apc15 q40 q40 q40 q40).symm).trans ((((congrArg (fun t => t ◇ (q40 ◇ q40)) ((h q40 q40 q40).symm)).symm).trans (apc14 q42 q41 (q40 ◇ q40))).trans (apc15 q40 q40 q42 q41))).symm
  have apc19 : forall (q43 q44 q45 q46:G), ((q45 ◇ q44) ◇ q46) = ((q43 ◇ q43) ◇ q43):=by
    intro q43 q44 q45 q46
    exact (((apc18 q43 q46 q43).symm).trans (apc16 q44 q45 q46 q46 q46)).symm
  exact (apc19 ((x ◇ y) ◇ z) y x z).trans ((apc19 ((x ◇ y) ◇ z) x z (w ◇ x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_3750_to_60617 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_3750_to_60617
