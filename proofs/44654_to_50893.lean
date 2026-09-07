-- Equation44654 → Equation50893
-- Recorded verdict: true
-- Premise: x * y = y * ((z * (w * w)) * x)
-- Conclusion: x * y = (z * ((y * x) * w)) * x
-- Original submission SHA-256: 3c8f6877b7297dd295fcae24c69b19f2fc7616bd802e290b2391f0af35e210f9
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = y ◇ ((z ◇ (w ◇ w)) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ ((y ◇ x) ◇ w)) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1 q2 q3 q4:G), (q3 ◇ (((q1 ◇ (q0 ◇ q0)) ◇ q4) ◇ q2)) = (q2 ◇ q3):=by
    intro q0 q1 q2 q3 q4
    exact ((cg (fun t => q3 ◇ t) (cg (fun t => t ◇ q2) ((h (q1 ◇ (q0 ◇ q0)) q4 q1 q0).symm))).symm).trans ((h q2 q3 q4 (q1 ◇ (q0 ◇ q0))).symm)
  have apc1 : forall (q5 q6 q7 q8 q9:G), (q9 ◇ ((q5 ◇ (q7 ◇ (q6 ◇ q6))) ◇ q8)) = (q8 ◇ q9):=by
    intro q5 q6 q7 q8 q9
    exact ((cg (fun t => q9 ◇ t) (cg (fun t => t ◇ q8) ((h q5 (q7 ◇ (q6 ◇ q6)) q5 q5).symm))).symm).trans (apc0 q6 q7 q8 q9 ((q5 ◇ (q5 ◇ q5)) ◇ q5))
  have apc2 : forall (q10 q11 q12 q13 q14 q15 q16:G), (q13 ◇ ((q11 ◇ q10) ◇ q12)) = (q12 ◇ q13):=by
    intro q10 q11 q12 q13 q14 q15 q16
    exact ((cg (fun t => q13 ◇ t) (cg (fun t => t ◇ q12) (apc0 q14 q15 q11 q10 q16))).symm).trans (((cg (fun t => q13 ◇ t) (cg (fun t => t ◇ q12) (cg (fun t => q10 ◇ t) (apc0 q14 q15 ((q15 ◇ (q14 ◇ q14)) ◇ q16) q11 q16)))).symm).trans (apc1 q10 ((q15 ◇ (q14 ◇ q14)) ◇ q16) q11 q12 q13))
  have apc3 : forall (q17 q18 q19 q20 q21 q22:G), (q22 ◇ (q19 ◇ (q21 ◇ q20))) = (((q18 ◇ q17) ◇ q19) ◇ q22):=by
    intro q17 q18 q19 q20 q21 q22
    exact ((cg (fun t => q22 ◇ t) (apc2 q17 q18 q19 (q21 ◇ q20) q17 q17 q17)).symm).trans (apc2 q20 q21 ((q18 ◇ q17) ◇ q19) q22 q17 q17 q17)
  have apc4 : forall (q23 q24 q25 q26 q27 q28 q29 q30:G), ((q23 ◇ (q25 ◇ q24)) ◇ q28) = ((q27 ◇ q26) ◇ q28):=by
    intro q23 q24 q25 q26 q27 q28 q29 q30
    exact (((apc2 q23 (q29 ◇ q30) (q27 ◇ q26) q28 (q28 ◇ (((q29 ◇ q30) ◇ q23) ◇ (q27 ◇ q26))) (q28 ◇ (((q29 ◇ q30) ◇ q23) ◇ (q27 ◇ q26))) (q28 ◇ (((q29 ◇ q30) ◇ q23) ◇ (q27 ◇ q26)))).symm).trans (((cg (fun t => q28 ◇ t) (apc3 q30 q29 q23 q24 q25 (q27 ◇ q26))).symm).trans (apc2 q26 q27 (q23 ◇ (q25 ◇ q24)) q28 q30 q30 q30))).symm
  have apc5 : forall (q30 q29 q23 q24 q25 q26 q27 q28:G), ((q27 ◇ q26) ◇ q28) = ((q23 ◇ q23) ◇ q28):=by
    intro q30 q29 q23 q24 q25 q26 q27 q28
    exact ((apc4 q23 q24 q25 q26 q27 q28 q29 q30).symm).trans (apc4 q23 q24 q25 q23 q23 q28 q29 q30)
  have apc6 : forall (q31 q32 q33 q34 q35:G), ((q32 ◇ (q34 ◇ q33)) ◇ q35) = ((q31 ◇ q31) ◇ q35):=by
    intro q31 q32 q33 q34 q35
    exact (((apc5 q31 q31 q31 q31 q31 q31 q31 q35).symm).trans ((apc4 q32 q33 q34 q31 q31 q35 q31 q31).symm)).symm
  have apc7 : forall (q36 q37 q38 q39 q40 q41 q42:G), (((q37 ◇ q36) ◇ q38) ◇ q39) = (q38 ◇ q39):=by
    intro q36 q37 q38 q39 q40 q41 q42
    exact (((apc2 q40 (q41 ◇ q42) q38 q39 (q39 ◇ (((q41 ◇ q42) ◇ q40) ◇ q38)) (q39 ◇ (((q41 ◇ q42) ◇ q40) ◇ q38)) (q39 ◇ (((q41 ◇ q42) ◇ q40) ◇ q38))).symm).trans (((cg (fun t => q39 ◇ t) (apc3 q42 q41 q40 q42 q42 q38)).symm).trans (apc3 q36 q37 q38 (q42 ◇ q42) q40 q39))).symm
  have apc8 : forall (q43 q44 q45 q46 q47:G), ((q43 ◇ (q45 ◇ q44)) ◇ q47) = (q46 ◇ q47):=by
    intro q43 q44 q45 q46 q47
    exact (((apc7 q43 q43 q46 q47 q43 q43 q43).symm).trans ((apc4 q43 q44 q45 q46 (q43 ◇ q43) q47 q43 q43).symm)).symm
  have apc11 : forall (q48 q49 q50 q51 q52 q53:G), ((q48 ◇ (q50 ◇ q49)) ◇ q51) = (q48 ◇ q51):=by
    intro q48 q49 q50 q51 q52 q53
    exact (((cg (fun t => t ◇ q51) (apc2 q52 q53 q48 (q50 ◇ q49) q52 q52 q52)).symm).trans (apc7 q49 q50 ((q53 ◇ q52) ◇ q48) q51 q52 q52 q52)).trans (apc7 q52 q53 q48 q51 (((q53 ◇ q52) ◇ q48) ◇ q51) (((q53 ◇ q52) ◇ q48) ◇ q51) (((q53 ◇ q52) ◇ q48) ◇ q51))
  have apc12 : forall (q54 q55 q56 q57 q58 q59 q60:G), (q55 ◇ q56) = (q54 ◇ q56):=by
    intro q54 q55 q56 q57 q58 q59 q60
    exact ((((cg (fun t => t ◇ q56) (apc11 q54 q57 q58 (q59 ◇ q60) ((q54 ◇ (q58 ◇ q57)) ◇ (q59 ◇ q60)) ((q54 ◇ (q58 ◇ q57)) ◇ (q59 ◇ q60)))).trans (apc11 q54 q60 q59 q56 ((q54 ◇ (q59 ◇ q60)) ◇ q56) ((q54 ◇ (q59 ◇ q60)) ◇ q56))).symm).trans (((cg (fun t => t ◇ q56) ((apc8 q54 q57 q58 q54 (q59 ◇ q60)).symm)).symm).trans (apc8 q54 q60 q59 q55 q56))).symm
  have apc13 : forall (q61 q62 q63 q64:G), ((q61 ◇ q62) ◇ q63) = (q62 ◇ q63):=by
    intro q61 q62 q63 q64
    exact ((cg (fun t => t ◇ q63) (apc7 q64 q64 q61 q62 (((q64 ◇ q64) ◇ q61) ◇ q62) (((q64 ◇ q64) ◇ q61) ◇ q62) (((q64 ◇ q64) ◇ q61) ◇ q62))).symm).trans (((cg (fun t => t ◇ q63) (cg (fun t => t ◇ q62) (apc6 q64 q64 q64 q64 q61))).symm).trans (apc7 q61 (q64 ◇ (q64 ◇ q64)) q62 q63 q64 q64 q64))
  have apc14 : forall (q65 q66 q67 q68 q69 q70:G), (q68 ◇ (q65 ◇ q66)) = (q66 ◇ (q67 ◇ q68)):=by
    intro q65 q66 q67 q68 q69 q70
    exact (((cg (fun t => q66 ◇ t) (apc13 q69 q67 q68 ((q69 ◇ q67) ◇ q68))).symm).trans ((((apc7 q65 q70 q66 ((q69 ◇ q67) ◇ q68) q65 q65 q65).symm).trans (apc2 q67 q69 q68 ((q70 ◇ q65) ◇ q66) q65 q65 q65)).trans (cg (fun t => q68 ◇ t) (apc13 q70 q65 q66 ((q70 ◇ q65) ◇ q66))))).symm
  have apc15 : forall (q71 q2 q3 q4 q1 q0:G), (q3 ◇ (q71 ◇ q2)) = (q2 ◇ q3):=by
    intro q71 q2 q3 q4 q1 q0
    exact ((((((cg (fun t => q3 ◇ t) (cg (fun t => t ◇ q2) (cg (fun t => q4 ◇ t) (cg (fun t => q71 ◇ t) (apc13 q1 (q0 ◇ q0) q71 ((q1 ◇ (q0 ◇ q0)) ◇ q71)))))).trans (cg (fun t => q3 ◇ t) (cg (fun t => t ◇ q2) (cg (fun t => q4 ◇ t) (cg (fun t => q71 ◇ t) (apc13 q0 q0 q71 ((q0 ◇ q0) ◇ q71))))))).trans (cg (fun t => q3 ◇ t) (apc13 q4 (q71 ◇ (q0 ◇ q71)) q2 ((q4 ◇ (q71 ◇ (q0 ◇ q71))) ◇ q2)))).trans (cg (fun t => q3 ◇ t) (apc13 q71 (q0 ◇ q71) q2 ((q71 ◇ (q0 ◇ q71)) ◇ q2)))).trans (cg (fun t => q3 ◇ t) (apc13 q0 q71 q2 ((q0 ◇ q71) ◇ q2)))).symm).trans (((cg (fun t => q3 ◇ t) (cg (fun t => t ◇ q2) (cg (fun t => q4 ◇ t) ((h q71 ((q1 ◇ (q0 ◇ q0)) ◇ q71) q1 q0).symm)))).symm).trans ((h q2 q3 q4 ((q1 ◇ (q0 ◇ q0)) ◇ q71)).symm))
  have apc16 : forall (q0 q71 q1 q2 q3 q4 q65 q70 q66 q67 q69 q68:G), (q68 ◇ q66) = (q66 ◇ q68):=by
    intro q0 q71 q1 q2 q3 q4 q65 q70 q66 q67 q69 q68
    exact (((apc15 q65 q66 q68 (q68 ◇ (q65 ◇ q66)) (q68 ◇ (q65 ◇ q66)) (q68 ◇ (q65 ◇ q66))).symm).trans ((apc14 q65 q66 q67 q68 q69 q70).trans (apc15 q67 q68 q66 (q66 ◇ (q67 ◇ q68)) (q66 ◇ (q67 ◇ q68)) (q66 ◇ (q67 ◇ q68))))).symm
  have apc17 : forall (q72 q73 q74 q75 q76:G), (q73 ◇ q74) = (q72 ◇ q73):=by
    intro q72 q73 q74 q75 q76
    exact (((((((cg (fun t => q72 ◇ t) (cg (fun t => t ◇ q73) (apc16 (q75 ◇ q76) (q75 ◇ q76) (q75 ◇ q76) (q75 ◇ q76) (q75 ◇ q76) (q75 ◇ q76) (q75 ◇ q76) (q75 ◇ q76) q76 (q75 ◇ q76) (q75 ◇ q76) q75))).trans (cg (fun t => q72 ◇ t) (apc13 q76 q75 q73 ((q76 ◇ q75) ◇ q73)))).trans (apc16 (q72 ◇ (q75 ◇ q73)) (q72 ◇ (q75 ◇ q73)) (q72 ◇ (q75 ◇ q73)) (q72 ◇ (q75 ◇ q73)) (q72 ◇ (q75 ◇ q73)) (q72 ◇ (q75 ◇ q73)) (q72 ◇ (q75 ◇ q73)) (q72 ◇ (q75 ◇ q73)) (q75 ◇ q73) (q72 ◇ (q75 ◇ q73)) (q72 ◇ (q75 ◇ q73)) q72)).trans (apc13 q75 q73 q72 ((q75 ◇ q73) ◇ q72))).trans (apc16 (q73 ◇ q72) (q73 ◇ q72) (q73 ◇ q72) (q73 ◇ q72) (q73 ◇ q72) (q73 ◇ q72) (q73 ◇ q72) (q73 ◇ q72) q72 (q73 ◇ q72) (q73 ◇ q72) q73)).symm).trans (((apc12 q72 q74 ((q75 ◇ q76) ◇ q73) q72 q72 q72 q72).symm).trans (apc2 q76 q75 q73 q74 q72 q72 q72))).symm
  exact (apc17 x x y (x ◇ y) (x ◇ y)).trans (apc17 (z ◇ ((y ◇ x) ◇ w)) x x (x ◇ y) (x ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_44654_to_50893 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_44654_to_50893
