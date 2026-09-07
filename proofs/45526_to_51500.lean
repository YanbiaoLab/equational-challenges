-- Equation45526 → Equation51500
-- Recorded verdict: true
-- Premise: x * y = y * (((z * w) * z) * x)
-- Conclusion: x * y = ((x * z) * (z * w)) * y
-- Original submission SHA-256: 900c9c11d711359eca9ecc260b830191b34d21700e064e33a340d24639d950a4
-- Generator: equational-challenges standalone v1
-- All project definitions are embedded in this file.
import Mathlib.Tactic

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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = y ◇ (((z ◇ w) ◇ z) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((x ◇ z) ◇ (z ◇ w)) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1 q2 q3:G), (q2 ◇ (((q0 ◇ q3) ◇ q3) ◇ q1)) = (q1 ◇ q2):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => q2 ◇ t) (cg (fun t => t ◇ q1) (cg (fun t => t ◇ q3) ((h q0 q3 q0 q0).symm)))).symm).trans ((h q1 q2 q3 (((q0 ◇ q0) ◇ q0) ◇ q0)).symm)
  have apc1 : forall (q4 q5 q6 q7 q8 q9:G), (q7 ◇ ((q4 ◇ (q4 ◇ q5)) ◇ q6)) = (q6 ◇ q7):=by
    intro q4 q5 q6 q7 q8 q9
    exact ((cg (fun t => q7 ◇ t) (cg (fun t => t ◇ q6) (cg (fun t => q4 ◇ t) (apc0 q8 q4 q5 q9)))).symm).trans (((cg (fun t => q7 ◇ t) (cg (fun t => t ◇ q6) (apc0 q8 q4 (q5 ◇ (((q8 ◇ q9) ◇ q9) ◇ q4)) q9))).symm).trans (apc0 q5 q6 q7 (((q8 ◇ q9) ◇ q9) ◇ q4)))
  have apc2 : forall (q10 q11 q12 q13:G), (q13 ◇ ((q11 ◇ (q10 ◇ q11)) ◇ q12)) = (q12 ◇ q13):=by
    intro q10 q11 q12 q13
    exact ((cg (fun t => q13 ◇ t) (cg (fun t => t ◇ q12) (cg (fun t => q11 ◇ t) ((h q10 q11 q10 q10).symm)))).symm).trans (apc1 q11 (((q10 ◇ q10) ◇ q10) ◇ q10) q12 q13 q10 q10)
  have apc3 : forall (q14 q15 q16:G), (q16 ◇ ((q14 ◇ q14) ◇ q15)) = (q15 ◇ q16):=by
    intro q14 q15 q16
    exact ((cg (fun t => q16 ◇ t) (cg (fun t => t ◇ q15) ((h q14 q14 q14 q14).symm))).symm).trans (apc2 ((q14 ◇ q14) ◇ q14) q14 q15 q16)
  have apc4 : forall (q17 q18 q19 q20:G), (q20 ◇ (q18 ◇ (q19 ◇ q19))) = (((q17 ◇ q17) ◇ q18) ◇ q20):=by
    intro q17 q18 q19 q20
    exact ((cg (fun t => q20 ◇ t) (apc3 q17 q18 (q19 ◇ q19))).symm).trans (apc3 q19 ((q17 ◇ q17) ◇ q18) q20)
  have apc5 : forall (q21 q22 q23 q24:G), (((q21 ◇ q21) ◇ q22) ◇ q23) = (q22 ◇ q23):=by
    intro q21 q22 q23 q24
    exact (((apc3 q24 q22 q23).symm).trans (((cg (fun t => q23 ◇ t) (apc3 q24 (q24 ◇ q24) q22)).symm).trans (apc4 q21 q22 (q24 ◇ q24) q23))).symm
  have apc6 : forall (q25 q26 q27 q28:G), ((q25 ◇ (q26 ◇ q26)) ◇ q27) = (q25 ◇ q27):=by
    intro q25 q26 q27 q28
    exact (((cg (fun t => t ◇ q27) (apc3 q28 q25 (q26 ◇ q26))).symm).trans (apc5 q26 ((q28 ◇ q28) ◇ q25) q27 q28)).trans (apc5 q28 q25 q27 (((q28 ◇ q28) ◇ q25) ◇ q27))
  have apc7 : forall (q29 q30 q31 q32:G), (q30 ◇ q29) = (q29 ◇ q30):=by
    intro q29 q30 q31 q32
    exact ((apc3 q31 q30 q29).symm).trans ((((apc5 q32 q29 ((q31 ◇ q31) ◇ q30) q32).symm).trans (apc3 q31 q30 ((q32 ◇ q32) ◇ q29))).trans (apc3 q32 q29 q30))
  have apc8 : forall (q33 q34 q35 q36:G), ((((q33 ◇ q34) ◇ q34) ◇ q35) ◇ q36) = (q35 ◇ q36):=by
    intro q33 q34 q35 q36
    exact ((cg (fun t => t ◇ q36) (apc0 q33 ((q33 ◇ q34) ◇ q34) q35 q34)).symm).trans (apc6 q35 ((q33 ◇ q34) ◇ q34) q36 q33)
  have apc9 : forall (q37 q38 q39 q40:G), (((q37 ◇ q38) ◇ q39) ◇ q40) = (q39 ◇ q40):=by
    intro q37 q38 q39 q40
    exact ((apc7 ((q37 ◇ q38) ◇ q39) q40 (q40 ◇ ((q37 ◇ q38) ◇ q39)) (q40 ◇ ((q37 ◇ q38) ◇ q39))).symm).trans (((cg (fun t => q40 ◇ t) (apc8 q37 q38 (q37 ◇ q38) q39)).symm).trans ((h q39 q40 (q37 ◇ q38) q38).symm))
  have apc10 : forall (q0 q41 q2 q3 q42 q43:G), ((q0 ◇ q3) ◇ q2) = ((q0 ◇ q41) ◇ q2):=by
    intro q0 q41 q2 q3 q42 q43
    exact ((((((cg (fun t => q2 ◇ t) (cg (fun t => q0 ◇ t) (cg (fun t => t ◇ q3) (apc7 q42 q3 (q3 ◇ q42) (q3 ◇ q42))))).trans (cg (fun t => q2 ◇ t) (apc7 ((q42 ◇ q3) ◇ q3) q0 (q0 ◇ ((q42 ◇ q3) ◇ q3)) (q0 ◇ ((q42 ◇ q3) ◇ q3))))).trans (cg (fun t => q2 ◇ t) (apc9 q42 q3 q3 q0))).trans (cg (fun t => q2 ◇ t) (apc7 q0 q3 (q3 ◇ q0) (q3 ◇ q0)))).trans (apc7 (q0 ◇ q3) q2 (q2 ◇ (q0 ◇ q3)) (q2 ◇ (q0 ◇ q3)))).symm).trans ((((cg (fun t => q2 ◇ t) ((h q0 ((q3 ◇ q42) ◇ q3) q41 q43).symm)).symm).trans ((h (((q41 ◇ q43) ◇ q41) ◇ q0) q2 q3 q42).symm)).trans (((cg (fun t => t ◇ q2) (cg (fun t => t ◇ q0) (cg (fun t => t ◇ q41) (apc7 q43 q41 (q41 ◇ q43) (q41 ◇ q43))))).trans (cg (fun t => t ◇ q2) (apc9 q43 q41 q41 q0))).trans (cg (fun t => t ◇ q2) (apc7 q0 q41 (q41 ◇ q0) (q41 ◇ q0)))))
  have apc11 : forall (q44 q45 q46:G), ((q44 ◇ q45) ◇ q46) = (q45 ◇ q46):=by
    intro q44 q45 q46
    exact ((cg (fun t => t ◇ q46) (apc5 q44 q44 q45 q44)).symm).trans (apc8 q44 q44 q45 q46)
  have apc12 : forall (q47 q48 q49 q50 q51:G), (q48 ◇ q49) = (q47 ◇ q49):=by
    intro q47 q48 q49 q50 q51
    exact (((((cg (fun t => t ◇ q49) (apc11 q50 q47 q51)).trans (cg (fun t => t ◇ q49) (apc7 q51 q47 (q47 ◇ q51) (q47 ◇ q51)))).trans (apc11 q51 q47 q49)).symm).trans (((apc10 (q50 ◇ q47) q51 q49 q48 q51 q51).symm).trans (apc9 q50 q47 q48 q49))).symm
  exact (apc12 (x ◇ y) x y (x ◇ y) (x ◇ y)).trans ((apc12 (x ◇ y) ((x ◇ z) ◇ (z ◇ w)) y (x ◇ y) (x ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_45526_to_51500 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_45526_to_51500
