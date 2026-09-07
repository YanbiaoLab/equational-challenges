-- Equation46249 → Equation56070
-- Recorded verdict: true
-- Premise: x * y = (x * z) * (w * (y * z))
-- Conclusion: x * (y * z) = (x * x) * (y * x)
-- Original submission SHA-256: dc28c8a578206b76c32f63a0ccc4bb6ccf9f179d677f4083056dece0cb522860
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (x ◇ z) ◇ (w ◇ (y ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ z) = (x ◇ x) ◇ (y ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3 q4:G), ((q3 ◇ (q1 ◇ q2)) ◇ (q0 ◇ q1)) = (q3 ◇ q4):=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => (q3 ◇ (q1 ◇ q2)) ◇ t) ((h q0 q1 q2 q4).symm)).symm).trans ((h q3 q4 (q1 ◇ q2) (q0 ◇ q2)).symm)
  have apc1 : forall (q5 q6 q7 q8 q9:G), ((q7 ◇ q9) ◇ (q5 ◇ q6)) = (q7 ◇ q8):=by
    intro q5 q6 q7 q8 q9
    exact ((congrArg (fun t => (q7 ◇ q9) ◇ t) (apc0 q8 q9 q5 q5 q6)).symm).trans ((h q7 q8 q9 (q5 ◇ (q9 ◇ q5))).symm)
  have apc2 : forall (q5 q6 q7 q8 q9:G), ((q7 ◇ q9) ◇ (q5 ◇ q6)) = ((q7 ◇ q7) ◇ (q7 ◇ q7)):=by
    intro q5 q6 q7 q8 q9
    exact (apc1 q5 q6 q7 q8 q9).trans ((apc1 q7 q7 q7 q8 q7).symm)
  have apc3 : forall (q10 q11 q12 q13 q14 q15:G), ((q12 ◇ q12) ◇ (q12 ◇ q12)) = (q12 ◇ (q10 ◇ q11)):=by
    intro q10 q11 q12 q13 q14 q15
    exact ((apc2 q13 ((q10 ◇ q10) ◇ (q10 ◇ q10)) q12 ((q12 ◇ (q14 ◇ q15)) ◇ (q13 ◇ ((q10 ◇ q10) ◇ (q10 ◇ q10)))) (q14 ◇ q15)).symm).trans (((congrArg (fun t => (q12 ◇ (q14 ◇ q15)) ◇ t) (congrArg (fun t => q13 ◇ t) (apc2 q14 q15 q10 q14 q11))).symm).trans ((h q12 (q10 ◇ q11) (q14 ◇ q15) q13).symm))
  have apc4 : forall (q16 q17 q18 q19 q20:G), ((q17 ◇ q17) ◇ (q17 ◇ q17)) = (q17 ◇ (q16 ◇ q16)):=by
    intro q16 q17 q18 q19 q20
    exact ((apc2 q18 (q16 ◇ (q19 ◇ q20)) q17 ((q17 ◇ (q16 ◇ q16)) ◇ (q18 ◇ (q16 ◇ (q19 ◇ q20)))) (q16 ◇ q16)).symm).trans (((congrArg (fun t => (q17 ◇ (q16 ◇ q16)) ◇ t) (congrArg (fun t => q18 ◇ t) (apc3 q19 q20 q16 q19 q19 q19))).symm).trans ((h q17 (q16 ◇ q16) (q16 ◇ q16) q18).symm))
  have apc6 : forall (q14 q15 q10 q11 q13 q12:G), (q12 ◇ (q12 ◇ q12)) = (q12 ◇ (q10 ◇ q11)):=by
    intro q14 q15 q10 q11 q13 q12
    exact (((apc3 q10 q11 q12 q13 q14 q15).symm).trans (apc3 q12 q12 q12 q13 q14 q15)).symm
  have apc7 : forall (q21:G), ((q21 ◇ q21) ◇ (q21 ◇ q21)) = (q21 ◇ (q21 ◇ q21)):=by
    intro q21
    exact ((apc6 q21 q21 q21 q21 q21 q21).trans ((apc3 q21 q21 q21 q21 q21 q21).symm)).symm
  have apc8 : forall (q5 q6 q7 q8 q9 q21:G), ((q7 ◇ q9) ◇ (q5 ◇ q6)) = (q7 ◇ (q7 ◇ q7)):=by
    intro q5 q6 q7 q8 q9 q21
    exact (apc2 q5 q6 q7 q8 q9).trans (apc7 q7)
  have apc10 : forall (q0 q2 q4 q22 q23 q1:G), (q0 ◇ (q0 ◇ q0)) = ((q0 ◇ q2) ◇ q4):=by
    intro q0 q2 q4 q22 q23 q1
    exact ((apc8 q22 (q4 ◇ (q23 ◇ (q1 ◇ q2))) q0 ((q0 ◇ q1) ◇ (q22 ◇ (q4 ◇ (q23 ◇ (q1 ◇ q2))))) q1 ((q0 ◇ q1) ◇ (q22 ◇ (q4 ◇ (q23 ◇ (q1 ◇ q2)))))).symm).trans (((congrArg (fun t => t ◇ (q22 ◇ (q4 ◇ (q23 ◇ (q1 ◇ q2))))) ((h q0 q1 q2 q23).symm)).symm).trans ((h (q0 ◇ q2) q4 (q23 ◇ (q1 ◇ q2)) q22).symm))
  have apc11 : forall (q24 q25 q26 q27:G), (q27 ◇ (q25 ◇ q26)) = (q27 ◇ (q24 ◇ q24)):=by
    intro q24 q25 q26 q27
    exact (((apc4 q24 q27 q24 q24 q24).symm).trans (apc3 q25 q26 q27 q24 q24 q24)).symm
  have apc12 : forall (q28 q29 q30 q31 q32:G), (q32 ◇ (q30 ◇ q31)) = ((q32 ◇ q28) ◇ q29):=by
    intro q28 q29 q30 q31 q32
    exact (((apc10 q32 q28 q29 q28 q28 q28).symm).trans (apc6 q28 q28 q30 q31 q28 q32)).symm
  have apc26 : forall (q33 q34 q35 q36:G), (q33 ◇ (q33 ◇ q33)) = (q33 ◇ q33):=by
    intro q33 q34 q35 q36
    exact ((apc8 q34 q35 q33 ((q33 ◇ q36) ◇ (q34 ◇ q35)) q36 ((q33 ◇ q36) ◇ (q34 ◇ q35))).symm).trans (((apc6 q34 q34 q34 q35 q34 (q33 ◇ q36)).symm).trans ((h q33 q33 q36 (q33 ◇ q36)).symm))
  have apc27 : forall (q37 q38 q39 q40:G), ((q40 ◇ q37) ◇ (q40 ◇ q37)) = (q40 ◇ (q38 ◇ q39)):=by
    intro q37 q38 q39 q40
    exact ((apc26 (q40 ◇ q37) q37 q37 q37).symm).trans ((apc12 q37 ((q40 ◇ q37) ◇ (q40 ◇ q37)) q38 q39 q40).symm)
  have apc28 : forall (q41 q42 q43 q44 q45:G), ((q43 ◇ q43) ◇ (q44 ◇ q45)) = (q43 ◇ (q41 ◇ q42)):=by
    intro q41 q42 q43 q44 q45
    exact (((apc27 q43 q41 q42 q43).symm).trans ((apc11 q43 q44 q45 (q43 ◇ q43)).symm)).symm
  exact (apc28 y z x y x).symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_46249_to_56070 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_46249_to_56070
