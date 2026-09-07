-- Equation23730 → Equation57745
-- Recorded verdict: true
-- Premise: x = ((y ◇ z) ◇ y) ◇ (z ◇ (x ◇ z))
-- Conclusion: x ◇ (y ◇ y) = ((z ◇ x) ◇ x) ◇ z
-- Original submission SHA-256: 84aa139d7f64c29db38e76539c2f7c501e8607e3c1bacd01c4ad3c97f70017c6
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ z) ◇ y) ◇ (z ◇ (x ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ y) = ((z ◇ x) ◇ x) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1:G), (((q1 ◇ ((q0 ◇ q0) ◇ q0)) ◇ q1) ◇ (q0 ◇ q0)) = q0:=by
    intro q0 q1
    exact ((cg (fun t => ((q1 ◇ ((q0 ◇ q0) ◇ q0)) ◇ q1) ◇ t) ((h (q0 ◇ q0) q0 q0).symm)).symm).trans ((h q0 q1 ((q0 ◇ q0) ◇ q0)).symm)
  have apc3 : forall (q2 q3 q4:G), (((q4 ◇ (q2 ◇ q2)) ◇ q4) ◇ ((q2 ◇ q2) ◇ q2)) = ((q3 ◇ ((q2 ◇ q2) ◇ q2)) ◇ q3):=by
    intro q2 q3 q4
    exact ((cg (fun t => ((q4 ◇ (q2 ◇ q2)) ◇ q4) ◇ t) (cg (fun t => (q2 ◇ q2) ◇ t) (apc0 q2 q3))).symm).trans ((h ((q3 ◇ ((q2 ◇ q2) ◇ q2)) ◇ q3) q4 (q2 ◇ q2)).symm)
  have apc4 : forall (q2 q3 q4:G), ((q3 ◇ ((q2 ◇ q2) ◇ q2)) ◇ q3) = ((q2 ◇ ((q2 ◇ q2) ◇ q2)) ◇ q2):=by
    intro q2 q3 q4
    exact ((apc3 q2 q3 q2).symm).trans (apc3 q2 q2 q2)
  have apc5 : forall (q0 q1 q2 q3 q4:G), (((q0 ◇ ((q0 ◇ q0) ◇ q0)) ◇ q0) ◇ (q0 ◇ q0)) = q0:=by
    intro q0 q1 q2 q3 q4
    exact ((cg (fun t => t ◇ (q0 ◇ q0)) (apc4 q0 q0 ((q0 ◇ ((q0 ◇ q0) ◇ q0)) ◇ q0))).symm).trans (apc0 q0 q0)
  have apc7 : forall (q5 q0 q6 q1:G), (((q1 ◇ (q6 ◇ (q5 ◇ q6))) ◇ q1) ◇ ((q6 ◇ (q5 ◇ q6)) ◇ q5)) = ((q0 ◇ q6) ◇ q0):=by
    intro q5 q0 q6 q1
    exact ((cg (fun t => ((q1 ◇ (q6 ◇ (q5 ◇ q6))) ◇ q1) ◇ t) (cg (fun t => (q6 ◇ (q5 ◇ q6)) ◇ t) ((h q5 q0 q6).symm))).symm).trans ((h ((q0 ◇ q6) ◇ q0) q1 (q6 ◇ (q5 ◇ q6))).symm)
  have apc8 : forall (q5 q0 q6 q1:G), ((q0 ◇ q6) ◇ q0) = ((q5 ◇ q6) ◇ q5):=by
    intro q5 q0 q6 q1
    exact ((apc7 q5 q0 q6 q5).symm).trans (apc7 q5 q5 q6 q5)
  have apc9 : forall (q7 q8 q9 q10:G), (((q7 ◇ q8) ◇ q7) ◇ (q10 ◇ q8)) = ((q9 ◇ q10) ◇ q9):=by
    intro q7 q8 q9 q10
    exact ((cg (fun t => t ◇ (q10 ◇ q8)) (apc8 q7 q10 q8 q7)).symm).trans (apc8 q9 (q10 ◇ q8) q10 q7)
  have apc10 : forall (q11 q12 q13 q14:G), ((q14 ◇ (q13 ◇ (q11 ◇ q13))) ◇ q14) = (q11 ◇ ((q12 ◇ q13) ◇ q12)):=by
    intro q11 q12 q13 q14
    exact (((cg (fun t => t ◇ ((q12 ◇ q13) ◇ q12)) ((h q11 q12 q13).symm)).symm).trans (apc8 q14 ((q12 ◇ q13) ◇ q12) (q13 ◇ (q11 ◇ q13)) q11)).symm
  have apc11 : forall (q11 q12 q13 q14:G), (q11 ◇ ((q12 ◇ q13) ◇ q12)) = (q11 ◇ ((q11 ◇ q13) ◇ q11)):=by
    intro q11 q12 q13 q14
    exact ((apc10 q11 q12 q13 q11).symm).trans (apc10 q11 q11 q13 q11)
  have apc19 : forall (q15 q16 q17:G), ((q17 ◇ ((q15 ◇ q16) ◇ q15)) ◇ q17) = ((q16 ◇ ((q16 ◇ q16) ◇ q16)) ◇ q16):=by
    intro q15 q16 q17
    exact ((cg (fun t => t ◇ q17) (cg (fun t => q17 ◇ t) (apc8 q15 q16 q16 q15))).symm).trans (apc4 q16 q17 q15)
  have apc20 : forall (q11 q12 q13 q14:G), ((q14 ◇ (q13 ◇ (q11 ◇ q13))) ◇ q14) = ((q11 ◇ (q13 ◇ (q11 ◇ q13))) ◇ q11):=by
    intro q11 q12 q13 q14
    exact (apc10 q11 q11 q13 q14).trans ((apc10 q11 q11 q13 q11).symm)
  have apc21 : forall (q11 q12 q13 q14:G), ((q11 ◇ (q13 ◇ (q11 ◇ q13))) ◇ q11) = (q11 ◇ ((q11 ◇ q13) ◇ q11)):=by
    intro q11 q12 q13 q14
    exact ((apc20 q11 ((q14 ◇ (q13 ◇ (q11 ◇ q13))) ◇ q14) q13 q14).symm).trans ((apc10 q11 q11 q13 q14).trans (apc11 q11 q11 q13 (q11 ◇ ((q11 ◇ q13) ◇ q11))))
  have apc26 : forall (q11 q12 q13 q14:G), ((q14 ◇ (q13 ◇ (q11 ◇ q13))) ◇ q14) = (q11 ◇ ((q11 ◇ q13) ◇ q11)):=by
    intro q11 q12 q13 q14
    exact (apc20 q11 q11 q13 q14).trans (apc21 q11 ((q11 ◇ (q13 ◇ (q11 ◇ q13))) ◇ q11) q13 ((q11 ◇ (q13 ◇ (q11 ◇ q13))) ◇ q11))
  have apc35 : forall (q18 q19 q20 q21 q22:G), (((q20 ◇ q21) ◇ q20) ◇ ((q18 ◇ q19) ◇ q18)) = ((q22 ◇ (q21 ◇ q19)) ◇ q22):=by
    intro q18 q19 q20 q21 q22
    exact ((cg (fun t => t ◇ ((q18 ◇ q19) ◇ q18)) (apc9 q18 q19 q20 q21)).symm).trans (apc8 q22 ((q18 ◇ q19) ◇ q18) (q21 ◇ q19) q18)
  have apc36 : forall (q18 q19 q20 q21 q22:G), ((q22 ◇ (q21 ◇ q19)) ◇ q22) = ((q18 ◇ (q21 ◇ q19)) ◇ q18):=by
    intro q18 q19 q20 q21 q22
    exact ((apc35 q18 q19 q18 q21 q22).symm).trans (apc35 q18 q19 q18 q21 q18)
  have apc37 : forall (q18 q19 q20 q21 q22:G), ((q19 ◇ (q21 ◇ q19)) ◇ q19) = ((q18 ◇ (q21 ◇ q19)) ◇ q18):=by
    intro q18 q19 q20 q21 q22
    exact (((apc36 q18 q19 q18 q21 q18).symm).trans (apc36 q19 q19 q18 q21 q18)).symm
  have apc38 : forall (q23 q24 q25 q26:G), (q26 ◇ ((q26 ◇ (q24 ◇ q23)) ◇ q26)) = (q26 ◇ ((q25 ◇ (q24 ◇ q23)) ◇ q25)):=by
    intro q23 q24 q25 q26
    exact (((cg (fun t => q26 ◇ t) (apc35 q24 q23 (q24 ◇ q23) q24 q25)).symm).trans (apc11 q26 ((q24 ◇ q23) ◇ q24) (q24 ◇ q23) q23)).symm
  have apc39 : forall (q27 q28:G), (((q27 ◇ q27) ◇ q27) ◇ (q27 ◇ q27)) = ((q28 ◇ q27) ◇ q28):=by
    intro q27 q28
    exact (((cg (fun t => t ◇ (q27 ◇ q27)) (cg (fun t => (q27 ◇ q27) ◇ t) (apc5 q27 q27 q27 q27 q27))).symm).trans (apc37 q28 (q27 ◇ q27) q27 ((q27 ◇ ((q27 ◇ q27) ◇ q27)) ◇ q27) q27)).trans (cg (fun t => t ◇ q28) (cg (fun t => q28 ◇ t) (apc5 q27 (((q27 ◇ ((q27 ◇ q27) ◇ q27)) ◇ q27) ◇ (q27 ◇ q27)) (((q27 ◇ ((q27 ◇ q27) ◇ q27)) ◇ q27) ◇ (q27 ◇ q27)) (((q27 ◇ ((q27 ◇ q27) ◇ q27)) ◇ q27) ◇ (q27 ◇ q27)) (((q27 ◇ ((q27 ◇ q27) ◇ q27)) ◇ q27) ◇ (q27 ◇ q27)))))
  have apc40 : forall (q27 q28:G), ((q28 ◇ q27) ◇ q28) = ((q27 ◇ q27) ◇ q27):=by
    intro q27 q28
    exact ((apc39 q27 q28).symm).trans (apc39 q27 q27)
  have apc41 : forall (q23 q24 q25 q26:G), (q26 ◇ ((q25 ◇ (q24 ◇ q23)) ◇ q25)) = (q26 ◇ ((q23 ◇ (q24 ◇ q23)) ◇ q23)):=by
    intro q23 q24 q25 q26
    exact ((apc38 q23 q24 q25 q26).symm).trans (apc38 q23 q24 q23 q26)
  have apc46 : forall (q29 q30 q31 q32:G), (((q31 ◇ q32) ◇ q31) ◇ (q32 ◇ ((q29 ◇ q30) ◇ q29))) = (q32 ◇ q30):=by
    intro q29 q30 q31 q32
    exact ((cg (fun t => ((q31 ◇ q32) ◇ q31) ◇ t) (cg (fun t => q32 ◇ t) (apc8 q29 q32 q30 q29))).symm).trans ((h (q32 ◇ q30) q31 q32).symm)
  have apc50 : forall (q33 q34:G), ((q34 ◇ ((q34 ◇ q34) ◇ q34)) ◇ q34) = (((q33 ◇ q34) ◇ q33) ◇ q34):=by
    intro q33 q34
    exact ((((apc46 q33 q34 ((q33 ◇ q34) ◇ q33) ((q33 ◇ q34) ◇ q33)).symm).trans (apc8 q33 (((q33 ◇ q34) ◇ q33) ◇ ((q33 ◇ q34) ◇ q33)) ((q33 ◇ q34) ◇ q33) q33)).trans (apc19 q33 q34 q33)).symm
  have apc51 : forall (q35 q36:G), (q36 ◇ ((q36 ◇ q36) ◇ q36)) = ((q35 ◇ q36) ◇ q35):=by
    intro q35 q36
    exact ((apc46 q36 ((q36 ◇ q36) ◇ q36) q35 q36).symm).trans (((cg (fun t => ((q35 ◇ q36) ◇ q35) ◇ t) (cg (fun t => q36 ◇ t) ((apc50 q35 q36).symm))).symm).trans ((h ((q35 ◇ q36) ◇ q35) q35 q36).symm))
  have apc52 : forall (q37:G), (((q37 ◇ q37) ◇ q37) ◇ q37) = q37:=by
    intro q37
    exact (((cg (fun t => t ◇ (((q37 ◇ q37) ◇ q37) ◇ ((q37 ◇ q37) ◇ q37))) (apc19 q37 q37 q37)).trans (apc46 q37 q37 q37 ((q37 ◇ q37) ◇ q37))).symm).trans (((cg (fun t => ((q37 ◇ ((q37 ◇ q37) ◇ q37)) ◇ q37) ◇ t) (cg (fun t => ((q37 ◇ q37) ◇ q37) ◇ t) (apc51 q37 q37))).symm).trans ((h q37 q37 ((q37 ◇ q37) ◇ q37)).symm))
  have apc53 : forall (q38 q39:G), (((q38 ◇ q39) ◇ q38) ◇ q39) = q39:=by
    intro q38 q39
    exact ((cg (fun t => t ◇ q39) (apc8 q38 q39 q39 q38)).symm).trans (apc52 q39)
  have apc56 : forall (q40 q41:G), ((q41 ◇ (q40 ◇ q40)) ◇ q41) = (q40 ◇ q40):=by
    intro q40 q41
    exact (((cg (fun t => t ◇ q41) (cg (fun t => q41 ◇ t) (cg (fun t => q40 ◇ t) (apc52 q40)))).symm).trans (apc26 ((q40 ◇ q40) ◇ q40) q40 q40 q41)).trans ((cg (fun t => ((q40 ◇ q40) ◇ q40) ◇ t) (cg (fun t => t ◇ ((q40 ◇ q40) ◇ q40)) (apc53 q40 q40))).trans (apc46 q40 q40 q40 q40))
  have apc58 : forall (q42 q43:G), (q43 ◇ ((q42 ◇ q43) ◇ q42)) = ((q42 ◇ q43) ◇ q42):=by
    intro q42 q43
    exact ((cg (fun t => t ◇ ((q42 ◇ q43) ◇ q42)) (apc53 q42 q43)).symm).trans (((cg (fun t => t ◇ ((q42 ◇ q43) ◇ q42)) (apc46 q42 q43 ((q42 ◇ q43) ◇ q42) ((q42 ◇ q43) ◇ q42))).symm).trans (apc53 (((q42 ◇ q43) ◇ q42) ◇ ((q42 ◇ q43) ◇ q42)) ((q42 ◇ q43) ◇ q42)))
  have apc59 : forall (q44 q45:G), ((q44 ◇ ((q44 ◇ q45) ◇ q44)) ◇ q44) = q45:=by
    intro q44 q45
    exact ((cg (fun t => t ◇ q44) (apc11 q44 q44 q45 (q44 ◇ ((q44 ◇ q45) ◇ q44)))).symm).trans ((((apc8 q44 (((q44 ◇ q45) ◇ q44) ◇ ((q44 ◇ q45) ◇ q44)) ((q44 ◇ q45) ◇ q44) q44).symm).trans (apc46 q44 q45 ((q44 ◇ q45) ◇ q44) ((q44 ◇ q45) ◇ q44))).trans (apc53 q44 q45))
  have apc60 : forall (q46 q47:G), (q47 ◇ (q46 ◇ q46)) = q47:=by
    intro q46 q47
    exact (((apc26 q47 (((q47 ◇ (q46 ◇ q46)) ◇ ((q46 ◇ q46) ◇ (q47 ◇ (q46 ◇ q46)))) ◇ (q47 ◇ (q46 ◇ q46))) (q46 ◇ q46) (q47 ◇ (q46 ◇ q46))).trans (cg (fun t => q47 ◇ t) (apc56 q46 q47))).symm).trans (((cg (fun t => t ◇ (q47 ◇ (q46 ◇ q46))) (cg (fun t => (q47 ◇ (q46 ◇ q46)) ◇ t) (cg (fun t => t ◇ (q47 ◇ (q46 ◇ q46))) (apc56 q46 q47)))).symm).trans (apc59 (q47 ◇ (q46 ◇ q46)) q47))
  have apc66 : forall (q48 q49:G), ((q48 ◇ q49) ◇ ((q48 ◇ q48) ◇ q48)) = (q49 ◇ (q48 ◇ q49)):=by
    intro q48 q49
    exact ((((cg (fun t => t ◇ ((q48 ◇ q49) ◇ q48)) (cg (fun t => ((q48 ◇ q49) ◇ q48) ◇ t) (apc11 q48 q48 q49 (q48 ◇ ((q48 ◇ q49) ◇ q48))))).trans (apc26 (q48 ◇ q49) ((((q48 ◇ q49) ◇ q48) ◇ (q48 ◇ ((q48 ◇ q49) ◇ q48))) ◇ ((q48 ◇ q49) ◇ q48)) q48 ((q48 ◇ q49) ◇ q48))).trans (cg (fun t => (q48 ◇ q49) ◇ t) (apc40 q48 (q48 ◇ q49)))).symm).trans (((cg (fun t => t ◇ ((q48 ◇ q49) ◇ q48)) (cg (fun t => ((q48 ◇ q49) ◇ q48) ◇ t) (cg (fun t => t ◇ ((q48 ◇ q49) ◇ q48)) ((h q48 q48 q49).symm)))).symm).trans (apc59 ((q48 ◇ q49) ◇ q48) (q49 ◇ (q48 ◇ q49))))
  have apc67 : forall (q50 q51:G), ((q50 ◇ (q51 ◇ q50)) ◇ (q51 ◇ q50)) = q51:=by
    intro q50 q51
    exact (((cg (fun t => t ◇ (q51 ◇ q50)) (apc66 q51 q50)).symm).trans (apc36 q50 q51 q50 (q51 ◇ q51) (q51 ◇ q50))).trans ((cg (fun t => t ◇ q50) (apc11 q50 q51 q51 (q50 ◇ ((q51 ◇ q51) ◇ q51)))).trans (apc59 q50 q51))
  have apc68 : forall (q52 q53:G), (q53 ◇ ((q52 ◇ q52) ◇ q52)) = ((q53 ◇ q52) ◇ q52):=by
    intro q52 q53
    exact ((((((cg (fun t => (q53 ◇ q52) ◇ t) (cg (fun t => t ◇ q53) (cg (fun t => q53 ◇ t) (apc40 q52 q53)))).trans (apc41 q52 (q52 ◇ q52) q53 (q53 ◇ q52))).trans (cg (fun t => (q53 ◇ q52) ◇ t) (cg (fun t => t ◇ q52) (apc58 q52 q52)))).trans (cg (fun t => (q53 ◇ q52) ◇ t) (apc53 q52 q52))).symm).trans ((((cg (fun t => t ◇ ((q53 ◇ ((q53 ◇ q52) ◇ q53)) ◇ q53)) (cg (fun t => q53 ◇ t) (apc59 q53 q52))).symm).trans (apc67 q53 (q53 ◇ ((q53 ◇ q52) ◇ q53)))).trans (cg (fun t => q53 ◇ t) (apc40 q52 q53)))).symm
  have apc70 : forall (q54 q55:G), (((q55 ◇ q54) ◇ q54) ◇ q55) = q54:=by
    intro q54 q55
    exact (((cg (fun t => t ◇ q55) (apc68 q54 q55)).symm).trans (apc40 ((q54 ◇ q54) ◇ q54) q55)).trans ((((cg (fun t => t ◇ ((q54 ◇ q54) ◇ q54)) (apc68 q54 ((q54 ◇ q54) ◇ q54))).trans (cg (fun t => t ◇ ((q54 ◇ q54) ◇ q54)) (cg (fun t => t ◇ q54) (apc53 q54 q54)))).trans (apc68 q54 (q54 ◇ q54))).trans (apc53 q54 q54))
  exact (calc
    (x ◇ (y ◇ y)) = x:=apc60 y x
    _ = (((z ◇ x) ◇ x) ◇ z):=(apc70 x z).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_23730_to_57745 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_23730_to_57745
