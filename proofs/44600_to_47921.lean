-- Equation44600 → Equation47921
-- Recorded verdict: true
-- Premise: x * y = y * ((z * (x * w)) * x)
-- Conclusion: x * y = (x * (y * y)) * (y * x)
-- Original submission SHA-256: 5c76ad39b0172199935e68a5f79320f963ded2918ef962d9b00600b3280acc3c
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = y ◇ ((z ◇ (x ◇ w)) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ y = (x ◇ (y ◇ y)) ◇ (y ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (q0 q1 q2 q3:G), (q2 ◇ ((q3 ◇ (q0 ◇ q1)) ◇ q1)) = (q1 ◇ q2):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => q2 ◇ t) (congrArg (fun t => t ◇ q1) (congrArg (fun t => q3 ◇ t) ((h q0 q1 q0 q0).symm)))).symm).trans ((h q1 q2 q3 ((q0 ◇ (q0 ◇ q0)) ◇ q0)).symm)
  have apc1 : forall (q4 q5 q6:G), (q5 ◇ ((q4 ◇ q6) ◇ q4)) = (q4 ◇ q5):=by
    intro q4 q5 q6
    exact ((congrArg (fun t => q5 ◇ t) (congrArg (fun t => t ◇ q4) ((h q4 q6 q4 q4).symm))).symm).trans (apc0 (q4 ◇ (q4 ◇ q4)) q4 q5 q6)
  have apc3 : forall (q7 q8 q9 q2 q3:G), (q2 ◇ ((q9 ◇ q3) ◇ (q8 ◇ (q9 ◇ q7)))) = ((q8 ◇ (q9 ◇ q7)) ◇ q2):=by
    intro q7 q8 q9 q2 q3
    exact ((congrArg (fun t => q2 ◇ t) (congrArg (fun t => t ◇ (q8 ◇ (q9 ◇ q7))) ((h q9 q3 q8 q7).symm))).symm).trans ((h (q8 ◇ (q9 ◇ q7)) q2 q3 q9).symm)
  have apc7 : forall (q10 q11 q12 q13:G), (q12 ◇ ((q11 ◇ q13) ◇ (q11 ◇ q10))) = ((q11 ◇ q10) ◇ q12):=by
    intro q10 q11 q12 q13
    exact ((congrArg (fun t => q12 ◇ t) (congrArg (fun t => t ◇ (q11 ◇ q10)) (apc1 q11 q13 q10))).symm).trans ((h (q11 ◇ q10) q12 q13 q11).symm)
  have apc8 : forall (q14 q15 q16 q17 q18:G), (((q16 ◇ q14) ◇ (q16 ◇ q15)) ◇ q17) = ((q16 ◇ q18) ◇ q17):=by
    intro q14 q15 q16 q17 q18
    exact (((apc7 q18 q16 q17 q15).symm).trans (((congrArg (fun t => q17 ◇ t) (apc7 q15 q16 (q16 ◇ q18) q14)).symm).trans (apc3 q15 (q16 ◇ q14) q16 q17 q18))).symm
  have apc9 : forall (q19 q20 q21 q22:G), (q22 ◇ ((q20 ◇ q19) ◇ q21)) = (q21 ◇ q22):=by
    intro q19 q20 q21 q22
    exact ((congrArg (fun t => q22 ◇ t) (apc8 q19 q21 q20 q21 q19)).symm).trans (apc0 q20 q21 q22 (q20 ◇ q19))
  have apc10 : forall (q7 q0 q8 q9 q2 q3:G), (((q8 ◇ (q0 ◇ q7)) ◇ q0) ◇ q2) = (q2 ◇ (q0 ◇ (q9 ◇ q3))):=by
    intro q7 q0 q8 q9 q2 q3
    exact (((congrArg (fun t => q2 ◇ t) (congrArg (fun t => q0 ◇ t) (apc9 q0 (q8 ◇ (q0 ◇ q7)) q9 q3))).symm).trans (((congrArg (fun t => q2 ◇ t) ((h q0 (q3 ◇ (((q8 ◇ (q0 ◇ q7)) ◇ q0) ◇ q9)) q8 q7).symm)).symm).trans ((h ((q8 ◇ (q0 ◇ q7)) ◇ q0) q2 q3 q9).symm))).symm
  have apc11 : forall (q23 q24 q25 q26 q27 q28 q29 q30 q31 q32:G), ((q26 ◇ (q27 ◇ q28)) ◇ (q23 ◇ (q24 ◇ q25))) = (q26 ◇ q23):=by
    intro q23 q24 q25 q26 q27 q28 q29 q30 q31 q32
    exact (((apc10 q29 q23 q30 q24 (q26 ◇ (q27 ◇ q28)) q25).symm).trans ((apc10 q31 q26 q32 q27 ((q30 ◇ (q23 ◇ q29)) ◇ q23) q28).symm)).trans ((apc9 (q23 ◇ q29) q30 q23 ((q32 ◇ (q26 ◇ q31)) ◇ q26)).trans (apc9 (q26 ◇ q31) q32 q26 q23))
  have apc12 : forall (q33 q34 q35 q36 q37:G), ((q35 ◇ (q36 ◇ q37)) ◇ (q34 ◇ q33)) = (q35 ◇ q33):=by
    intro q33 q34 q35 q36 q37
    exact ((congrArg (fun t => (q35 ◇ (q36 ◇ q37)) ◇ t) ((h q34 q33 q33 q33).symm)).symm).trans (apc11 q33 (q33 ◇ (q34 ◇ q33)) q34 q35 q36 q37 q33 q33 q33 q33)
  have apc13 : forall (q38 q39 q40 q41:G), ((q41 ◇ q40) ◇ (q39 ◇ q38)) = (q40 ◇ q38):=by
    intro q38 q39 q40 q41
    exact ((congrArg (fun t => t ◇ (q39 ◇ q38)) ((h q41 q40 q38 q38).symm)).symm).trans (apc12 q38 q39 q40 (q38 ◇ (q41 ◇ q38)) q41)
  have apc17 : forall (q42 q43 q44:G), (q44 ◇ (q43 ◇ q42)) = (q42 ◇ q44):=by
    intro q42 q43 q44
    exact (((apc13 q44 (q42 ◇ (q44 ◇ q42)) q42 q43).symm).trans ((h q44 (q43 ◇ q42) q42 q42).symm)).symm
  have apc21 : forall (q45 q46 q47 q48 q49 q50 q51:G), (q47 ◇ q46) = (q45 ◇ q47):=by
    intro q45 q46 q47 q48 q49 q50 q51
    exact ((((congrArg (fun t => t ◇ (q45 ◇ q46)) (apc17 q48 q49 q47)).trans (apc17 q46 q45 (q48 ◇ q47))).trans (apc17 q47 q48 q46)).symm).trans ((((congrArg (fun t => (q47 ◇ (q49 ◇ q48)) ◇ t) (apc11 q46 q45 q45 q45 q50 q51 q45 q45 q45 q45)).symm).trans (apc11 (q45 ◇ (q50 ◇ q51)) q46 (q45 ◇ q45) q47 q49 q48 q45 q45 q45 q45)).trans ((congrArg (fun t => q47 ◇ t) (apc17 q51 q50 q45)).trans (apc17 q45 q51 q47)))
  exact (apc21 (y ◇ x) y x (x ◇ y) (x ◇ y) (x ◇ y) (x ◇ y)).trans (apc21 (x ◇ (y ◇ y)) x (y ◇ x) (x ◇ y) (x ◇ y) (x ◇ y) (x ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_44600_to_47921 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_44600_to_47921
