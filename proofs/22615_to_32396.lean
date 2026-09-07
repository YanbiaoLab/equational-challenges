-- Equation22615 → Equation32396
-- Recorded verdict: true
-- Premise: x = (y ◇ (y ◇ x)) ◇ ((z ◇ y) ◇ z)
-- Conclusion: x = (y ◇ ((z ◇ (x ◇ x)) ◇ z)) ◇ y
-- Original submission SHA-256: 8b4ed66f24ddb8c1e7ff780b84d48fa989199feeec8a5f8584db15355860cf29
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ (y ◇ x)) ◇ ((z ◇ y) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ ((z ◇ (x ◇ x)) ◇ z)) ◇ y
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
    exact ((h x y z).symm).trans (h x x x)
  have apc1:=fun (x y z:G)=>by
    exact ((h x x x).trans (apc0 x x x)).symm
  have apc2:=fun (q0 q1 q2 q3:G)=>by
    exact ((cg (fun t => t ◇ ((q3 ◇ (q1 ◇ (q1 ◇ q0))) ◇ q3)) (cg (fun t => (q1 ◇ (q1 ◇ q0)) ◇ t) ((h q0 q1 q2).symm))).symm).trans ((h ((q2 ◇ q1) ◇ q2) (q1 ◇ (q1 ◇ q0)) q3).symm)
  have apc3:=fun (q0 q1 q2 q3:G)=>by
    exact ((apc2 q0 q1 q2 q0).symm).trans (apc2 q0 q1 q0 q0)
  have apc4:=fun (q0 q1 q2 q3:G)=>by
    exact (((apc3 q0 q1 q0 q0).symm).trans (apc3 q1 q1 q0 q0)).symm
  have apc5:=fun (q4 q5 q6 q7:G)=>by
    exact ((cg (fun t => t ◇ (q7 ◇ q5)) (apc3 q4 q5 q7 q4)).symm).trans (apc3 q6 q7 (q7 ◇ q5) q4)
  have apc6:=fun (q8 q9 q10 q11:G)=>by
    exact (((cg (fun t => t ◇ (q9 ◇ (q9 ◇ q8))) ((h q8 q9 q10).symm)).symm).trans (apc3 q11 ((q10 ◇ q9) ◇ q10) (q9 ◇ (q9 ◇ q8)) q8)).symm
  have apc7:=fun (q8 q9 q10 q11:G)=>by
    exact (((apc6 q8 q9 q8 q8).symm).trans (apc6 q9 q9 q8 q8)).symm
  have apc8:=fun (q12 q13 q14:G)=>by
    exact (((cg (fun t => t ◇ (q14 ◇ (q14 ◇ q12))) ((h q12 q14 q12).symm)).symm).trans (apc6 q13 q14 q12 (q14 ◇ (q14 ◇ q12)))).symm
  have apc11:=fun (q15 q16 q17:G)=>by
    exact ((cg (fun t => t ◇ (q17 ◇ q15)) ((apc4 q17 q15 q15 q15).symm)).symm).trans (apc3 q16 q17 (q17 ◇ q15) q15)
  have apc13:=fun (q18 q19:G)=>by
    exact ((cg (fun t => (q19 ◇ (q19 ◇ q19)) ◇ t) (apc3 q18 q19 q19 q18)).symm).trans (apc1 q19 q18 q18)
  have apc14:=fun (q20 q21:G)=>by
    exact ((cg (fun t => (q21 ◇ (q21 ◇ q20)) ◇ t) ((apc4 q20 q21 q20 q20).symm)).symm).trans ((h q20 q21 q20).symm)
  have apc17:=fun (q22 q23 q24:G)=>by
    exact ((apc7 q22 q22 q22 q22).trans ((apc6 q22 q22 q23 q24).symm)).symm
  have apc18:=fun (q25 q26 q27:G)=>by
    exact (((cg (fun t => t ◇ q27) (apc7 q25 q27 q25 q25)).symm).trans (apc3 q26 (q27 ◇ (q27 ◇ q27)) q27 q25)).symm
  have apc19:=fun (q28 q26 q27:G)=>by
    exact (((cg (fun t => t ◇ q27) ((apc7 q27 q28 q28 q28).symm)).symm).trans (apc3 q26 (q28 ◇ (q28 ◇ q27)) q27 q28)).symm
  have apc24:=fun (q29 q30:G)=>by
    exact ((cg (fun t => t ◇ q30) ((apc7 q30 q30 q29 q29).symm)).symm).trans (apc18 q29 q30 q30)
  have apc26:=fun (q31 q32 q33 q34 q35:G)=>by
    exact ((cg (fun t => t ◇ ((q31 ◇ q32) ◇ q31)) (apc5 q31 q32 q33 q34)).symm).trans (apc3 q35 (q34 ◇ q32) ((q31 ◇ q32) ◇ q31) q31)
  have apc27:=fun (q31 q32 q33 q34 q35:G)=>by
    exact ((apc26 q31 q32 q31 q34 q35).symm).trans (apc26 q31 q32 q31 q34 q31)
  have apc28:=fun (q31 q32 q33 q34 q35:G)=>by
    exact (((apc27 q31 q32 q31 q34 q31).symm).trans (apc27 q32 q32 q31 q34 q31)).symm
  have apc29:=fun (q36 q37 q38 q39:G)=>by
    exact ((cg (fun t => ((q37 ◇ q38) ◇ q37) ◇ t) (apc4 q36 q38 q36 q36)).symm).trans (apc5 q37 q38 q39 (q38 ◇ q38))
  have apc31:=fun (q40 q41:G)=>by
    exact (((apc29 q41 (q41 ◇ q41) q41 q40).symm).trans ((apc28 ((q41 ◇ q41) ◇ q41) q41 q40 q41 q40).symm)).symm
  have apc42:=fun (q42 q43:G)=>by
    exact ((cg (fun t => (q43 ◇ q43) ◇ t) (apc7 q42 q43 q42 q42)).symm).trans ((apc7 (q43 ◇ q43) q43 q42 q42).symm)
  have apc45:=fun (q44 q45 q46 q47 q48:G)=>by
    exact (((cg (fun t => q46 ◇ t) (cg (fun t => (q46 ◇ q45) ◇ t) (apc3 q44 q45 q46 q44))).symm).trans ((apc6 q46 (q46 ◇ q45) q47 q48).symm)).symm
  have apc48:=fun (q49:G)=>by
    exact (((cg (fun t => q49 ◇ t) (apc17 q49 q49 q49)).symm).trans ((((cg (fun t => q49 ◇ t) (apc11 q49 q49 ((q49 ◇ q49) ◇ q49))).symm).trans ((apc6 q49 ((q49 ◇ q49) ◇ q49) q49 q49).symm)).trans ((cg (fun t => t ◇ q49) (cg (fun t => q49 ◇ t) (apc17 q49 q49 q49))).trans (apc19 q49 q49 (q49 ◇ q49))))).symm
  have apc54:=fun (q50 q51 q52:G)=>by
    exact ((cg (fun t => t ◇ ((q52 ◇ q51) ◇ q52)) (apc7 q50 q51 q50 q50)).symm).trans ((h (q51 ◇ q51) q51 q52).symm)
  have apc65:=fun (q53 q54 q55 q56:G)=>by
    exact ((cg (fun t => q56 ◇ t) (cg (fun t => (q56 ◇ q54) ◇ t) (apc3 q53 q54 q56 q53))).symm).trans (apc8 q55 q56 (q56 ◇ q54))
  have apc67:=fun (q57 q58 q59:G)=>by
    exact ((cg (fun t => q59 ◇ t) (cg (fun t => (q59 ◇ q57) ◇ t) ((apc4 q59 q57 q57 q57).symm))).symm).trans (apc8 q58 q59 (q59 ◇ q57))
  have apc73:=fun (q60 q61 q62:G)=>by
    exact (((cg (fun t => (q62 ◇ q60) ◇ t) (apc26 q60 q62 q62 q60 q61)).symm).trans ((apc45 q60 q62 (q62 ◇ q60) q60 q60).symm)).trans (((cg (fun t => t ◇ q60) (cg (fun t => q60 ◇ t) (apc17 q60 q62 q60))).trans (apc19 q60 q60 (q60 ◇ q60))).trans (apc48 q60))
  have apc81:=fun (q63 q64 q65 q66:G)=>by
    exact ((cg (fun t => t ◇ ((q66 ◇ q65) ◇ q64)) (apc3 q63 q64 (q66 ◇ q65) q63)).symm).trans ((apc28 ((q66 ◇ q65) ◇ q64) q65 q63 q66 q63).symm)
  have apc84:=fun (q67 q68 q69 q70:G)=>by
    exact ((apc28 q67 q68 q67 q70 q67).trans ((apc26 q67 q68 q69 q70 q67).symm)).symm
  have apc88:=fun (q57 q58 q59:G)=>by
    exact ((apc67 q57 q58 q59).symm).trans (apc67 q57 q57 q59)
  have apc92:=fun (q53 q54 q55 q56 q57 q58 q59:G)=>by
    exact (apc65 q53 q54 q53 q56).trans (apc88 q54 q53 q56)
  have apc104:=fun (q71 q72 q73:G)=>by
    exact (((cg (fun t => t ◇ q73) (cg (fun t => q73 ◇ t) ((apc28 q71 q71 q71 q72 q71).symm))).symm).trans (apc45 q71 q71 q72 q71 q73)).trans (apc92 q71 q71 (q72 ◇ ((q72 ◇ q71) ◇ ((q71 ◇ q71) ◇ q71))) q72 (q72 ◇ ((q72 ◇ q71) ◇ ((q71 ◇ q71) ◇ q71))) (q72 ◇ ((q72 ◇ q71) ◇ ((q71 ◇ q71) ◇ q71))) (q72 ◇ ((q72 ◇ q71) ◇ ((q71 ◇ q71) ◇ q71))))
  have apc105:=fun (q74 q75 q76 q77:G)=>by
    exact ((((cg (fun t => t ◇ ((q75 ◇ (q75 ◇ q74)) ◇ q74)) (apc2 q74 q75 q76 q74)).symm).trans (apc3 q77 ((q74 ◇ (q75 ◇ (q75 ◇ q74))) ◇ q74) ((q75 ◇ (q75 ◇ q74)) ◇ q74) q74)).trans (cg (fun t => t ◇ q77) (cg (fun t => q77 ◇ t) (apc19 q75 q74 q74)))).symm
  have apc106:=fun (q78:G)=>by
    exact (((apc14 (q78 ◇ (q78 ◇ q78)) q78).symm).trans ((((cg (fun t => t ◇ ((q78 ◇ q78) ◇ q78)) (apc73 q78 q78 (q78 ◇ q78))).symm).trans (apc105 q78 q78 q78 ((q78 ◇ q78) ◇ q78))).trans ((apc81 q78 q78 (q78 ◇ q78) q78).trans (apc19 q78 (q78 ◇ q78) q78)))).symm
  have apc107:=fun (q78 q29 q30:G)=>by
    exact (((apc106 q30).symm).trans (apc24 q29 q30)).symm
  have apc111:=fun (q79 q80 q81 q82 q83 q84:G)=>by
    exact ((cg (fun t => ((q82 ◇ q83) ◇ q82) ◇ t) (apc6 q79 q80 q81 q83)).symm).trans (apc5 q82 q83 q84 (q83 ◇ ((q81 ◇ q80) ◇ q81)))
  have apc112:=fun (q79 q80 q81 q82 q83 q84:G)=>by
    exact ((apc111 q79 q80 q81 q79 q83 q84).symm).trans (apc111 q79 q80 q79 q79 q83 q79)
  have apc115:=fun (q85:G)=>by
    exact (((cg (fun t => t ◇ q85) (cg (fun t => q85 ◇ t) (apc84 q85 q85 q85 q85))).trans (apc104 q85 q85 q85)).symm).trans ((((apc112 q85 q85 q85 q85 ((q85 ◇ q85) ◇ q85) q85).symm).trans ((apc31 q85 ((q85 ◇ q85) ◇ q85)).symm)).trans (((((cg (fun t => t ◇ ((q85 ◇ q85) ◇ q85)) (cg (fun t => ((q85 ◇ q85) ◇ q85) ◇ t) (apc84 q85 q85 q85 q85))).trans (cg (fun t => t ◇ ((q85 ◇ q85) ◇ q85)) (apc81 q85 q85 (q85 ◇ q85) q85))).trans (cg (fun t => t ◇ ((q85 ◇ q85) ◇ q85)) (apc19 q85 (q85 ◇ q85) q85))).trans (cg (fun t => t ◇ ((q85 ◇ q85) ◇ q85)) (apc107 ((q85 ◇ (q85 ◇ (q85 ◇ q85))) ◇ q85) q85 q85))).trans (apc13 q85 q85)))
  have apc116:=fun (q86:G)=>by
    exact (((cg (fun t => ((q86 ◇ q86) ◇ (q86 ◇ q86)) ◇ t) (apc115 q86)).symm).trans (apc42 q86 (q86 ◇ q86))).trans ((apc88 q86 (q86 ◇ q86) q86).trans (apc115 q86))
  have apc120:=fun (q87 q88:G)=>by
    exact ((cg (fun t => t ◇ ((q88 ◇ (q87 ◇ q87)) ◇ q88)) (apc115 q87)).symm).trans (apc54 q87 (q87 ◇ q87) q88)
  have apc124:=fun (q89 q90 q91:G)=>by
    exact (((apc116 q91).symm).trans (((cg (fun t => t ◇ q91) (apc120 q91 q89)).symm).trans (apc3 q90 ((q89 ◇ (q91 ◇ q91)) ◇ q89) q91 q89))).symm
  exact (calc
    x=x:=rfl
    _=((y ◇ ((z ◇ (x ◇ x)) ◇ z)) ◇ y):=(apc124 z y x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_22615_to_32396 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_22615_to_32396
