-- Equation19816 → Equation54028
-- Recorded verdict: true
-- Premise: x = (y ◇ x) ◇ ((x ◇ (x ◇ z)) ◇ w)
-- Conclusion: x ◇ (y ◇ x) = x ◇ (y ◇ (z ◇ z))
-- Original submission SHA-256: 5de0dab0cad48b62f012c0bd575c692b53c23324b54f96441b107bde32dca2ad
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ x) ◇ ((x ◇ (x ◇ z)) ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ x) = x ◇ (y ◇ (z ◇ z))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2:G), ((q1 ◇ q0) ◇ (q0 ◇ q2)) = q0:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => (q1 ◇ q0) ◇ t) ((h (q0 ◇ q2) q0 q0 q0).symm)).symm).trans ((h q0 q1 q2 (((q0 ◇ q2) ◇ ((q0 ◇ q2) ◇ q0)) ◇ q0)).symm)
  have apc1 : forall (q3 q4 q5:G), (q3 ◇ ((q3 ◇ q4) ◇ q5)) = (q3 ◇ q4):=by
    intro q3 q4 q5
    exact ((congrArg (fun t => t ◇ ((q3 ◇ q4) ◇ q5)) (apc0 q3 q3 q4)).symm).trans (apc0 (q3 ◇ q4) (q3 ◇ q3) q5)
  have apc2 : forall (q3 q6 q7:G), ((q7 ◇ (q6 ◇ q3)) ◇ q3) = (q6 ◇ q3):=by
    intro q3 q6 q7
    exact ((congrArg (fun t => (q7 ◇ (q6 ◇ q3)) ◇ t) (apc0 q3 q6 q3)).symm).trans (apc0 (q6 ◇ q3) q7 (q3 ◇ q3))
  have apc3 : forall (q8 q9 q10:G), ((q8 ◇ (q8 ◇ q9)) ◇ q10) = (q8 ◇ q10):=by
    intro q8 q9 q10
    exact (((congrArg (fun t => t ◇ q10) ((h q8 q8 q9 q10).symm)).symm).trans (apc2 q10 (q8 ◇ (q8 ◇ q9)) (q8 ◇ q8))).symm
  have apc4 : forall (q11 q12 q13:G), (q12 ◇ (q12 ◇ q13)) = (q12 ◇ (q12 ◇ q11)):=by
    intro q11 q12 q13
    exact ((congrArg (fun t => q12 ◇ t) (apc3 q12 q11 q13)).symm).trans (apc1 q12 (q12 ◇ q11) q13)
  have apc5 : forall (q14 q15 q16:G), (q16 ◇ (q16 ◇ (q16 ◇ q14))) = (q16 ◇ (q16 ◇ q15)):=by
    intro q14 q15 q16
    exact ((congrArg (fun t => q16 ◇ t) (apc4 q14 q16 q14)).symm).trans (apc4 q15 q16 (q16 ◇ q14))
  have apc6 : forall (q11 q12 q13:G), (q12 ◇ (q12 ◇ q12)) = (q12 ◇ (q12 ◇ q11)):=by
    intro q11 q12 q13
    exact (((apc4 q11 q12 q13).symm).trans (apc4 q12 q12 q13)).symm
  have apc7 : forall (q17 q18:G), (q18 ◇ (q18 ◇ (q18 ◇ q17))) = (q18 ◇ (q18 ◇ q18)):=by
    intro q17 q18
    exact ((apc6 q17 q18 q17).trans ((apc5 q17 q17 q18).symm)).symm
  have apc8 : forall (q19 q20 q21 q1:G), ((q1 ◇ (q20 ◇ q19)) ◇ (((q20 ◇ q19) ◇ q19) ◇ q21)) = (q20 ◇ q19):=by
    intro q19 q20 q21 q1
    exact ((congrArg (fun t => (q1 ◇ (q20 ◇ q19)) ◇ t) (congrArg (fun t => t ◇ q21) (congrArg (fun t => (q20 ◇ q19) ◇ t) ((h q19 q20 q19 q19).symm)))).symm).trans ((h (q20 ◇ q19) q1 ((q19 ◇ (q19 ◇ q19)) ◇ q19) q21).symm)
  have apc9 : forall (q22 q23 q24:G), ((q24 ◇ (q23 ◇ (q23 ◇ q23))) ◇ (q23 ◇ (q23 ◇ q22))) = (q23 ◇ (q23 ◇ q23)):=by
    intro q22 q23 q24
    exact (((congrArg (fun t => t ◇ (q23 ◇ (q23 ◇ q22))) (congrArg (fun t => q24 ◇ t) (apc7 q22 q23))).symm).trans (apc2 (q23 ◇ (q23 ◇ q22)) q23 q24)).trans (apc7 q22 q23)
  have apc10 : forall (q25 q26 q27 q28:G), ((q28 ◇ (q27 ◇ (q27 ◇ q25))) ◇ (q27 ◇ (q27 ◇ q26))) = (q27 ◇ (q27 ◇ q27)):=by
    intro q25 q26 q27 q28
    exact ((congrArg (fun t => t ◇ (q27 ◇ (q27 ◇ q26))) (congrArg (fun t => q28 ◇ t) (apc6 q25 q27 q25))).symm).trans (apc9 q26 q27 q28)
  have apc11 : forall (q29 q30 q31:G), (q31 ◇ (q30 ◇ (q30 ◇ q30))) = (q31 ◇ (q30 ◇ (q30 ◇ q29))):=by
    intro q29 q30 q31
    exact ((congrArg (fun t => q31 ◇ t) (apc10 q29 q29 q30 q31)).symm).trans (apc1 q31 (q30 ◇ (q30 ◇ q29)) (q30 ◇ (q30 ◇ q29)))
  have apc13 : forall (q32 q33 q34:G), (q34 ◇ (q34 ◇ (q33 ◇ (q33 ◇ q32)))) = (q34 ◇ (q34 ◇ q34)):=by
    intro q32 q33 q34
    exact ((congrArg (fun t => q34 ◇ t) (apc11 q32 q33 q34)).symm).trans ((apc6 (q33 ◇ (q33 ◇ q33)) q34 q32).symm)
  have apc14 : forall (q35 q36 q37 q38:G), (q37 ◇ (q36 ◇ (q36 ◇ q35))) = (q37 ◇ (q36 ◇ q38)):=by
    intro q35 q36 q37 q38
    exact (((((congrArg (fun t => (q37 ◇ (q37 ◇ q37)) ◇ t) (congrArg (fun t => t ◇ q38) (apc10 q35 q35 q36 q37))).trans (congrArg (fun t => (q37 ◇ (q37 ◇ q37)) ◇ t) (apc3 q36 q36 q38))).trans (apc3 q37 q37 (q36 ◇ q38))).symm).trans (((congrArg (fun t => t ◇ (((q37 ◇ (q36 ◇ (q36 ◇ q35))) ◇ (q36 ◇ (q36 ◇ q35))) ◇ q38)) (apc13 q35 q36 q37)).symm).trans (apc8 (q36 ◇ (q36 ◇ q35)) q37 q38 q37))).symm
  exact ((apc14 (x ◇ (y ◇ x)) y x x).symm).trans (apc14 (x ◇ (y ◇ x)) y x (z ◇ z))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_19816_to_54028 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_19816_to_54028
