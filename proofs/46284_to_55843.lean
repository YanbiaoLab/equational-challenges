-- Equation46284 → Equation55843
-- Recorded verdict: true
-- Premise: x * y = (y * x) * (y * (z * x))
-- Conclusion: x * (y * x) = (z * x) * (y * y)
-- Original submission SHA-256: 06cb14c6c53c8b0bc7d246cabeb32bc222cf9e6cadf5af0f224b6a582c4937f6
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (y ◇ x) ◇ (y ◇ (z ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ x) = (z ◇ x) ◇ (y ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a=b → f a=f b:=by
    intro f a b p
    exact congrArg f p
  have apc0:=fun (x y z:G)=>by
    exact ((h x y z).symm).trans (h x y x)
  have apc1:=fun (x y z:G)=>by
    exact ((h x y x).trans (apc0 x y x)).symm
  have apc2:=fun (q0 q1 q2:G)=>by
    exact ((cg (fun t => ((q2 ◇ q0) ◇ (q1 ◇ q0)) ◇ t) ((h q0 q2 q1).symm)).symm).trans ((h (q1 ◇ q0) (q2 ◇ q0) q2).symm)
  have apc3:=fun (q0 q3 q1 q4:G)=>by
    exact ((cg (fun t => (q4 ◇ (q3 ◇ (q1 ◇ q0))) ◇ t) (cg (fun t => q4 ◇ t) ((h q0 q3 q1).symm))).symm).trans ((h (q3 ◇ (q1 ◇ q0)) q4 (q3 ◇ q0)).symm)
  have apc4:=fun (q5 q6 q7:G)=>by
    exact ((cg (fun t => t ◇ ((q6 ◇ q5) ◇ (q5 ◇ q6))) ((h q5 q6 q7).symm)).symm).trans (apc3 q5 q6 q7 (q6 ◇ q5))
  have apc5:=fun (q5 q6 q7:G)=>by
    exact ((apc4 q5 q6 q7).symm).trans (apc4 q5 q6 q5)
  have apc6:=fun (q8 q9:G)=>by
    exact ((cg (fun t => t ◇ ((q9 ◇ q8) ◇ (q8 ◇ q9))) (apc1 q8 q9 q8)).symm).trans (apc3 q8 q9 q8 (q9 ◇ q8))
  have apc7:=fun (q10 q11 q12 q13:G)=>by
    exact ((cg (fun t => (q13 ◇ (q10 ◇ q12)) ◇ t) (cg (fun t => q13 ◇ t) (apc2 q10 q11 q12))).symm).trans ((h (q10 ◇ q12) q13 ((q12 ◇ q10) ◇ (q11 ◇ q10))).symm)
  have apc8:=fun (q0 q3 q1 q2:G)=>by
    exact (((cg (fun t => t ◇ ((q3 ◇ q0) ◇ (q2 ◇ (q3 ◇ (q1 ◇ q0))))) ((h q0 q3 q1).symm)).symm).trans ((h (q3 ◇ (q1 ◇ q0)) (q3 ◇ q0) q2).symm)).trans (apc5 q0 q3 q1)
  have apc9:=fun (q14 q15 q16 q17:G)=>by
    exact ((cg (fun t => (q15 ◇ q16) ◇ t) (cg (fun t => (q16 ◇ q15) ◇ t) (apc3 q17 q15 q14 q16))).symm).trans (apc8 q15 q16 q17 (q16 ◇ (q15 ◇ (q14 ◇ q17))))
  have apc10:=fun (q18 q19 q7 q20:G)=>by
    exact (((apc7 q18 q19 q7 q20).symm).trans (((cg (fun t => t ◇ (q20 ◇ ((q19 ◇ q18) ◇ (q7 ◇ q18)))) (cg (fun t => q20 ◇ t) ((h q18 q7 q19).symm))).symm).trans (apc3 (q19 ◇ q18) (q7 ◇ q18) q7 q20))).symm
  have apc12:=fun (q21 q22 q23 q24:G)=>by
    exact ((((cg (fun t => ((q21 ◇ q23) ◇ q24) ◇ t) (apc10 q21 q22 q23 (q24 ◇ q24))).trans (apc1 q24 (q21 ◇ q23) (((q21 ◇ q23) ◇ q24) ◇ ((q21 ◇ q23) ◇ (q24 ◇ q24))))).symm).trans (((cg (fun t => t ◇ (((q23 ◇ q21) ◇ (q23 ◇ (q22 ◇ q21))) ◇ (q24 ◇ q24))) (apc10 q21 q22 q23 q24)).symm).trans (apc1 q24 ((q23 ◇ q21) ◇ (q23 ◇ (q22 ◇ q21))) q21))).symm
  have apc13:=fun (q25 q26 q27 q28:G)=>by
    exact ((cg (fun t => (q27 ◇ (q25 ◇ q26)) ◇ t) (cg (fun t => q27 ◇ t) (apc12 q25 q25 q26 q28))).symm).trans ((((cg (fun t => t ◇ (q27 ◇ (q28 ◇ ((q26 ◇ q25) ◇ (q26 ◇ (q25 ◇ q25)))))) (apc12 q25 q25 q26 q27)).symm).trans ((h ((q26 ◇ q25) ◇ (q26 ◇ (q25 ◇ q25))) q27 q28).symm)).trans (apc10 q25 q25 q26 q27))
  have apc14:=fun (q29 q30 q31 q32:G)=>by
    exact ((cg (fun t => ((q29 ◇ q30) ◇ q31) ◇ t) (apc10 q29 q29 q30 (q32 ◇ q31))).symm).trans ((((cg (fun t => t ◇ (((q30 ◇ q29) ◇ (q30 ◇ (q29 ◇ q29))) ◇ (q32 ◇ q31))) (apc10 q29 q29 q30 q31)).symm).trans ((h q31 ((q30 ◇ q29) ◇ (q30 ◇ (q29 ◇ q29))) q32).symm)).trans (apc12 q29 q29 q30 q31))
  have apc16:=fun (q18 q19 q5 q7:G)=>by
    exact ((cg (fun t => ((q5 ◇ q18) ◇ ((q19 ◇ q18) ◇ (q7 ◇ q5))) ◇ t) ((h q18 q5 q19).symm)).symm).trans (apc3 q5 (q19 ◇ q18) q7 (q5 ◇ q18))
  have apc17:=fun (q33:G)=>by
    exact (((cg (fun t => t ◇ (q33 ◇ q33)) (apc6 q33 q33)).symm).trans (apc16 q33 q33 q33 q33)).trans (apc2 q33 q33 q33)
  have apc18:=fun (q34 q35 q36:G)=>by
    exact (((apc17 q36).symm).trans ((((cg (fun t => t ◇ (q36 ◇ q36)) (apc9 q34 q36 q36 q35)).symm).trans (apc16 q36 q36 q36 (q36 ◇ (q34 ◇ q35)))).trans (apc2 q36 (q36 ◇ (q34 ◇ q35)) q36))).symm
  have apc20:=fun (q37 q38:G)=>by
    exact ((apc5 (q37 ◇ q37) q38 q37).symm).trans (apc3 q37 q37 q37 q38)
  have apc25:=fun (q39 q40:G)=>by
    exact ((cg (fun t => ((q39 ◇ q40) ◇ (q39 ◇ q40)) ◇ t) (apc5 q39 q40 q39)).symm).trans (((cg (fun t => ((q39 ◇ q40) ◇ (q39 ◇ q40)) ◇ t) (apc4 q39 q40 q39)).symm).trans ((h (q39 ◇ q40) (q39 ◇ q40) (q40 ◇ q39)).symm))
  have apc26:=fun (q41 q42:G)=>by
    exact ((cg (fun t => t ◇ ((q41 ◇ q42) ◇ (q41 ◇ q42))) (apc2 q42 q41 q41)).symm).trans (((cg (fun t => (((q41 ◇ q42) ◇ (q41 ◇ q42)) ◇ (q42 ◇ q41)) ◇ t) (apc25 q41 q42)).symm).trans ((h (q42 ◇ q41) ((q41 ◇ q42) ◇ (q41 ◇ q42)) (q42 ◇ (q41 ◇ q41))).symm))
  have apc27:=fun (q43 q44 q45 q46:G)=>by
    exact (((cg (fun t => (q45 ◇ (q46 ◇ (q43 ◇ q44))) ◇ t) (apc12 q43 q43 q44 q45)).symm).trans ((((cg (fun t => t ◇ (q45 ◇ ((q44 ◇ q43) ◇ (q44 ◇ (q43 ◇ q43))))) (cg (fun t => q45 ◇ t) (apc12 q43 q43 q44 q46))).symm).trans (apc5 ((q44 ◇ q43) ◇ (q44 ◇ (q43 ◇ q43))) q45 q46)).trans (((cg (fun t => t ◇ (q45 ◇ ((q44 ◇ q43) ◇ (q44 ◇ (q43 ◇ q43))))) (cg (fun t => q45 ◇ t) (apc10 q43 q43 q44 ((q44 ◇ q43) ◇ (q44 ◇ (q43 ◇ q43)))))).trans (cg (fun t => t ◇ (q45 ◇ ((q44 ◇ q43) ◇ (q44 ◇ (q43 ◇ q43))))) (cg (fun t => q45 ◇ t) (apc12 q43 q43 q44 (q43 ◇ q44))))).trans (cg (fun t => (q45 ◇ ((q43 ◇ q44) ◇ (q43 ◇ q44))) ◇ t) (apc12 q43 q43 q44 q45))))).symm
  have apc29:=fun (q47 q48 q49:G)=>by
    exact ((apc27 q48 q48 q49 q47).symm).trans (apc20 q48 q49)
  have apc30:=fun (q50:G)=>by
    exact (((((cg (fun t => ((q50 ◇ q50) ◇ (q50 ◇ q50)) ◇ t) (apc2 q50 q50 q50)).trans (apc26 q50 q50)).trans (apc6 q50 q50)).symm).trans (((cg (fun t => t ◇ (((q50 ◇ q50) ◇ (q50 ◇ q50)) ◇ (q50 ◇ q50))) (apc25 q50 q50)).symm).trans (apc29 (q50 ◇ (q50 ◇ q50)) q50 ((q50 ◇ q50) ◇ (q50 ◇ q50))))).symm
  have apc31:=fun (q51 q52:G)=>by
    exact (((((cg (fun t => (q52 ◇ ((q51 ◇ (q51 ◇ q51)) ◇ (q51 ◇ q51))) ◇ t) (cg (fun t => q52 ◇ t) (apc1 q51 q51 ((q51 ◇ q51) ◇ (q51 ◇ (q51 ◇ q51)))))).trans (apc5 (q51 ◇ q51) q52 (q51 ◇ (q51 ◇ q51)))).trans (apc29 (q51 ◇ q51) q51 q52)).symm).trans ((((cg (fun t => t ◇ (q52 ◇ ((q51 ◇ q51) ◇ (q51 ◇ (q51 ◇ q51))))) (cg (fun t => q52 ◇ t) (apc30 q51))).symm).trans (apc3 (q51 ◇ q51) (q51 ◇ (q51 ◇ q51)) (q51 ◇ q51) q52)).trans (cg (fun t => t ◇ q52) (apc30 q51)))).symm
  have apc32:=fun (q51 q52 q33:G)=>by
    exact ((apc31 q33 (q33 ◇ q33)).symm).trans (apc17 q33)
  have apc33:=fun (q51 q52 q33:G)=>by
    exact ((cg (fun t => t ◇ q52) (apc32 ((q51 ◇ (q51 ◇ q51)) ◇ (q51 ◇ q51)) ((q51 ◇ (q51 ◇ q51)) ◇ (q51 ◇ q51)) q51)).symm).trans (apc31 q51 q52)
  have apc34:=fun (q53 q54:G)=>by
    exact ((((cg (fun t => ((q53 ◇ (q53 ◇ q53)) ◇ q54) ◇ t) (apc33 q53 (q53 ◇ q54) (((q53 ◇ q53) ◇ (q53 ◇ q53)) ◇ (q53 ◇ q54)))).trans (apc14 q53 (q53 ◇ q53) q54 q53)).symm).trans (((cg (fun t => t ◇ (((q53 ◇ q53) ◇ (q53 ◇ q53)) ◇ (q53 ◇ q54))) (apc33 q53 q54 q53)).symm).trans ((h q54 ((q53 ◇ q53) ◇ (q53 ◇ q53)) q53).symm))).symm
  have apc35:=fun (q55:G)=>by
    exact (((apc1 q55 q55 ((q55 ◇ q55) ◇ (q55 ◇ (q55 ◇ q55)))).symm).trans ((((apc34 q55 (q55 ◇ q55)).symm).trans (apc6 q55 q55)).trans (apc32 ((q55 ◇ (q55 ◇ q55)) ◇ (q55 ◇ q55)) ((q55 ◇ (q55 ◇ q55)) ◇ (q55 ◇ q55)) q55))).symm
  have apc36:=fun (q51 q52 q55 q33:G)=>by
    exact (((cg (fun t => t ◇ q52) (apc35 q51)).symm).trans (apc33 q51 q52 q51)).symm
  have apc37:=fun (q56:G)=>by
    exact ((((cg (fun t => (q56 ◇ q56) ◇ t) (cg (fun t => q56 ◇ t) (apc35 q56))).trans (apc1 q56 q56 ((q56 ◇ q56) ◇ (q56 ◇ (q56 ◇ q56))))).symm).trans (((apc36 q56 (q56 ◇ ((q56 ◇ q56) ◇ (q56 ◇ q56))) q56 q56).symm).trans (apc1 (q56 ◇ q56) q56 q56))).symm
  have apc39:=fun (q57 q58:G)=>by
    exact ((apc2 q57 q58 q57).symm).trans ((((cg (fun t => ((q57 ◇ q57) ◇ (q58 ◇ q57)) ◇ t) (apc37 q57)).symm).trans (apc5 q57 (q57 ◇ q57) q58)).trans (((cg (fun t => ((q57 ◇ q57) ◇ (q57 ◇ q57)) ◇ t) (apc37 q57)).trans (cg (fun t => t ◇ (q57 ◇ q57)) (apc35 q57))).trans (apc35 q57)))
  have apc40:=fun (q59 q60:G)=>by
    exact (((apc39 q60 (q59 ◇ q60)).symm).trans (((cg (fun t => ((q59 ◇ q60) ◇ q60) ◇ t) (apc39 q60 q59)).symm).trans ((h q60 (q59 ◇ q60) q60).symm))).symm
  have apc42:=fun (q61 q62:G)=>by
    exact ((apc40 q62 (q62 ◇ q61)).symm).trans ((h q61 q62 q62).symm)
  have apc43:=fun (q63 q64:G)=>by
    exact ((((cg (fun t => (q63 ◇ q64) ◇ t) (apc40 q63 (q64 ◇ q63))).trans (cg (fun t => (q63 ◇ q64) ◇ t) (apc42 q63 q64))).trans (apc42 q64 q63)).symm).trans ((((cg (fun t => t ◇ ((q64 ◇ q63) ◇ (q63 ◇ (q64 ◇ q63)))) (apc42 q63 q64)).symm).trans ((h (q64 ◇ q63) (q64 ◇ q63) q63).symm)).trans (apc42 q63 q64))
  have apc44:=fun (q65 q66:G)=>by
    exact (((cg (fun t => (q66 ◇ q66) ◇ t) (apc43 (q65 ◇ q66) q66)).trans (apc43 ((q65 ◇ q66) ◇ q66) (q66 ◇ q66))).symm).trans (((cg (fun t => t ◇ (q66 ◇ (q65 ◇ q66))) (apc40 q65 q66)).symm).trans (apc42 (q65 ◇ q66) q66))
  have apc50:=fun (q67 q68 q69 q70:G)=>by
    exact ((((((cg (fun t => ((q67 ◇ q67) ◇ (q68 ◇ q69)) ◇ t) (cg (fun t => t ◇ (q70 ◇ (q68 ◇ q69))) (apc43 (q67 ◇ q67) q67))).trans (cg (fun t => ((q67 ◇ q67) ◇ (q68 ◇ q69)) ◇ t) (cg (fun t => t ◇ (q70 ◇ (q68 ◇ q69))) (apc37 q67)))).trans (cg (fun t => ((q67 ◇ q67) ◇ (q68 ◇ q69)) ◇ t) (cg (fun t => (q67 ◇ q67) ◇ t) (apc43 (q68 ◇ q69) q70)))).trans (cg (fun t => ((q67 ◇ q67) ◇ (q68 ◇ q69)) ◇ t) (apc43 ((q68 ◇ q69) ◇ q70) (q67 ◇ q67)))).trans (apc43 (((q68 ◇ q69) ◇ q70) ◇ (q67 ◇ q67)) ((q67 ◇ q67) ◇ (q68 ◇ q69)))).symm).trans ((((cg (fun t => t ◇ ((q67 ◇ (q67 ◇ q67)) ◇ (q70 ◇ (q68 ◇ q69)))) (apc36 q67 (q68 ◇ q69) q67 q67)).symm).trans (apc13 q68 q69 (q67 ◇ (q67 ◇ q67)) q70)).trans (((cg (fun t => (q68 ◇ q69) ◇ t) (apc43 (q67 ◇ q67) q67)).trans (cg (fun t => (q68 ◇ q69) ◇ t) (apc37 q67))).trans (apc43 (q67 ◇ q67) (q68 ◇ q69))))
  have apc52:=fun (q61 q62 q63 q64:G)=>by
    exact (((cg (fun t => t ◇ (q62 ◇ q61)) (apc43 q61 q62)).trans (cg (fun t => (q61 ◇ q62) ◇ t) (apc43 q61 q62))).symm).trans (apc42 q61 q62)
  have apc53:=fun (q71 q72:G)=>by
    exact (((((((cg (fun t => t ◇ ((q71 ◇ q71) ◇ (q71 ◇ (q71 ◇ q71)))) (cg (fun t => q72 ◇ t) (apc43 (q71 ◇ q71) q71))).trans (cg (fun t => t ◇ ((q71 ◇ q71) ◇ (q71 ◇ (q71 ◇ q71)))) (cg (fun t => q72 ◇ t) (apc37 q71)))).trans (cg (fun t => (q72 ◇ (q71 ◇ q71)) ◇ t) (cg (fun t => (q71 ◇ q71) ◇ t) (apc43 (q71 ◇ q71) q71)))).trans (cg (fun t => (q72 ◇ (q71 ◇ q71)) ◇ t) (cg (fun t => (q71 ◇ q71) ◇ t) (apc37 q71)))).trans (cg (fun t => t ◇ ((q71 ◇ q71) ◇ (q71 ◇ q71))) (apc43 (q71 ◇ q71) q72))).trans (cg (fun t => ((q71 ◇ q71) ◇ q72) ◇ t) (apc52 q71 q71 ((q71 ◇ q71) ◇ (q71 ◇ q71)) ((q71 ◇ q71) ◇ (q71 ◇ q71))))).symm).trans ((((cg (fun t => (q72 ◇ (q71 ◇ (q71 ◇ q71))) ◇ t) (apc36 q71 (q71 ◇ (q71 ◇ q71)) q71 q71)).symm).trans (apc39 (q71 ◇ (q71 ◇ q71)) q72)).trans (((((cg (fun t => t ◇ (q71 ◇ (q71 ◇ q71))) (apc43 (q71 ◇ q71) q71)).trans (cg (fun t => t ◇ (q71 ◇ (q71 ◇ q71))) (apc37 q71))).trans (cg (fun t => (q71 ◇ q71) ◇ t) (apc43 (q71 ◇ q71) q71))).trans (cg (fun t => (q71 ◇ q71) ◇ t) (apc37 q71))).trans (apc52 q71 q71 ((q71 ◇ q71) ◇ (q71 ◇ q71)) ((q71 ◇ q71) ◇ (q71 ◇ q71)))))
  have apc55:=fun (q34 q35 q36 q55:G)=>by
    exact (((cg (fun t => t ◇ (q36 ◇ q36)) (cg (fun t => t ◇ q36) (apc43 (q34 ◇ q35) q36))).trans (apc44 (q34 ◇ q35) q36)).symm).trans ((apc18 q34 q35 q36).trans (apc35 q36))
  have apc56:=fun (q73 q74 q75:G)=>by
    exact (((((cg (fun t => t ◇ ((q73 ◇ q73) ◇ (q74 ◇ q75))) (apc52 q73 q73 ((q73 ◇ q73) ◇ (q73 ◇ q73)) ((q73 ◇ q73) ◇ (q73 ◇ q73)))).trans (apc43 ((q73 ◇ q73) ◇ (q74 ◇ q75)) (q73 ◇ q73))).trans (apc53 q73 (q74 ◇ q75))).symm).trans (((cg (fun t => t ◇ ((q73 ◇ q73) ◇ (q74 ◇ q75))) (apc55 q74 q75 (q73 ◇ q73) q73)).symm).trans (apc50 q73 q74 q75 (q73 ◇ q73)))).symm
  have apc57:=fun (q76 q77:G)=>by
    exact ((((apc43 (q76 ◇ q76) (q77 ◇ q77)).trans (apc56 q76 q77 q77)).symm).trans (((cg (fun t => (q77 ◇ q77) ◇ t) (apc56 q76 q76 q76)).symm).trans (apc56 q77 (q76 ◇ q76) (q76 ◇ q76)))).symm
  have apc58:=fun (q78 q79 q80:G)=>by
    exact (((apc56 q78 q79 q80).symm).trans ((((cg (fun t => t ◇ (q79 ◇ q80)) (apc57 q78 (q79 ◇ q80))).symm).trans (apc55 q79 q80 (q79 ◇ q80) q78)).trans (apc52 q79 q80 ((q79 ◇ q80) ◇ (q79 ◇ q80)) ((q79 ◇ q80) ◇ (q79 ◇ q80))))).symm
  exact (apc58 (x ◇ (y ◇ x)) x (y ◇ x)).trans ((apc58 (x ◇ (y ◇ x)) (z ◇ x) (y ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_46284_to_55843 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_46284_to_55843
