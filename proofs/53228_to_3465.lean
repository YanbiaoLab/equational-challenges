-- Equation53228 → Equation3465
-- Recorded verdict: true
-- Premise: x ◇ y = (((x ◇ z) ◇ y) ◇ y) ◇ x
-- Conclusion: x ◇ x = x ◇ ((y ◇ y) ◇ y)
-- Original submission SHA-256: ef01114b0bf62b87ff1e01db30e9ce09d8f7528d78dc1fd040588c3544227a72
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (((x ◇ z) ◇ y) ◇ y) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ x = x ◇ ((y ◇ y) ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have cg : ∀ (f:G → G) {a b:G}, a=b → f a=f b:=by
    intro f a b p
    exact congrArg f p
  have apc0:=fun (q0 q1:G)=>by
    exact ((cg (fun t => t ◇ (q1 ◇ q0)) ((h q1 q1 q0).symm)).symm).trans ((h (q1 ◇ q0) q1 q1).symm)
  have apc1:=fun (x y z:G)=>by
    exact ((h x y z).symm).trans (h x y x)
  have apc2:=fun (x y z:G)=>by
    exact ((h x y x).trans (apc1 x y x)).symm
  have apc3:=fun (q0 q1 q2:G)=>by
    exact ((cg (fun t => t ◇ ((q1 ◇ q0) ◇ q2)) (cg (fun t => t ◇ q1) ((h q1 q2 q0).symm))).symm).trans ((h ((q1 ◇ q0) ◇ q2) q1 q2).symm)
  have apc4:=fun (q3 q4:G)=>by
    exact ((cg (fun t => t ◇ q4) (cg (fun t => t ◇ (q4 ◇ q3)) (apc0 q3 q4))).symm).trans ((h q4 (q4 ◇ q3) q4).symm)
  have apc5:=fun (q5 q6:G)=>by
    exact ((cg (fun t => t ◇ ((q5 ◇ q5) ◇ q6)) (apc0 q5 q5)).symm).trans (apc0 q6 (q5 ◇ q5))
  have apc6:=fun (q7 q8:G)=>by
    exact (((apc3 q7 q8 q8).symm).trans ((((cg (fun t => ((q8 ◇ q8) ◇ q8) ◇ t) (apc0 q7 q8)).symm).trans (apc5 q8 (q8 ◇ q7))).trans (cg (fun t => t ◇ (q8 ◇ q8)) (apc0 q7 q8)))).symm
  have apc7:=fun (q9:G)=>by
    exact (((apc2 q9 q9 ((((q9 ◇ q9) ◇ q9) ◇ q9) ◇ q9)).symm).trans (((cg (fun t => t ◇ q9) (apc6 q9 q9)).symm).trans (apc4 q9 q9))).symm
  have apc8:=fun (q10:G)=>by
    exact ((((((cg (fun t => t ◇ q10) (cg (fun t => t ◇ ((q10 ◇ q10) ◇ (q10 ◇ q10))) (apc0 q10 q10))).trans (cg (fun t => t ◇ q10) (cg (fun t => ((q10 ◇ q10) ◇ q10) ◇ t) (apc0 q10 q10)))).trans (cg (fun t => t ◇ q10) (apc3 q10 q10 q10))).trans (apc2 q10 q10 ((((q10 ◇ q10) ◇ q10) ◇ q10) ◇ q10))).symm).trans ((((cg (fun t => t ◇ q10) (cg (fun t => t ◇ ((q10 ◇ q10) ◇ (q10 ◇ q10))) (apc7 (q10 ◇ q10)))).symm).trans (apc2 q10 ((q10 ◇ q10) ◇ (q10 ◇ q10)) q10)).trans (cg (fun t => q10 ◇ t) (apc0 q10 q10)))).symm
  have apc9:=fun (q11:G)=>by
    exact (((cg (fun t => (q11 ◇ q11) ◇ t) (apc0 q11 q11)).symm).trans (apc7 (q11 ◇ q11))).trans (apc0 q11 q11)
  have apc10:=fun (q3 q12 q13:G)=>by
    exact ((cg (fun t => t ◇ (q12 ◇ q12)) (cg (fun t => t ◇ q13) (cg (fun t => t ◇ q13) (apc0 q3 q12)))).symm).trans ((h (q12 ◇ q12) q13 (q12 ◇ q3)).symm)
  have apc12:=fun (q14 q15:G)=>by
    exact (((cg (fun t => ((q15 ◇ (q15 ◇ q14)) ◇ q15) ◇ t) (apc0 q14 q15)).symm).trans (apc3 q15 q15 (q15 ◇ q14))).trans (cg (fun t => t ◇ q15) (apc0 q14 q15))
  have apc13:=fun (q16:G)=>by
    exact (((cg (fun t => ((q16 ◇ q16) ◇ q16) ◇ t) (apc3 q16 q16 q16)).symm).trans (apc7 ((q16 ◇ q16) ◇ q16))).trans (apc3 q16 q16 q16)
  have apc14:=fun (q17 q0 q1 q2:G)=>by
    exact ((cg (fun t => t ◇ (((q2 ◇ q0) ◇ q17) ◇ q17)) (cg (fun t => t ◇ q1) (cg (fun t => t ◇ q1) ((h q2 q17 q0).symm)))).symm).trans ((h (((q2 ◇ q0) ◇ q17) ◇ q17) q1 q2).symm)
  have apc15:=fun (q18 q19 q20:G)=>by
    exact (((apc10 q18 q19 q20).symm).trans (((cg (fun t => ((((q19 ◇ q18) ◇ q19) ◇ q20) ◇ q20) ◇ t) ((h q19 q19 q18).symm)).symm).trans (apc14 q19 q19 q20 (q19 ◇ q18)))).symm
  have apc16:=fun (q18 q21 q20:G)=>by
    exact (((cg (fun t => t ◇ ((((q20 ◇ q18) ◇ q21) ◇ q20) ◇ q20)) ((h q20 q20 q18).symm)).symm).trans (apc14 q20 q21 q20 (q20 ◇ q18))).symm
  have apc20:=fun (q22 q23:G)=>by
    exact (((cg (fun t => t ◇ ((((q23 ◇ q23) ◇ q22) ◇ q23) ◇ q23)) (apc2 q23 q23 q22)).symm).trans (apc14 q23 q22 q23 (q23 ◇ q23))).symm
  have apc23:=fun (q24 q25:G)=>by
    exact ((cg (fun t => t ◇ q24) (apc0 (q24 ◇ q25) (q24 ◇ q25))).symm).trans (((cg (fun t => t ◇ q24) (cg (fun t => t ◇ ((q24 ◇ q25) ◇ (q24 ◇ q25))) (apc7 (q24 ◇ q25)))).symm).trans ((h q24 ((q24 ◇ q25) ◇ (q24 ◇ q25)) q25).symm))
  have apc24:=fun (q26 q27:G)=>by
    exact ((apc23 q26 q27).symm).trans ((h q26 (q26 ◇ q27) q27).symm)
  have apc26:=fun (q26 q27 q24 q25:G)=>by
    exact (apc23 q24 q25).trans (apc24 q24 q25)
  have apc27:=fun (q28 q29:G)=>by
    exact (((cg (fun t => t ◇ (q29 ◇ q29)) (cg (fun t => t ◇ (q29 ◇ q29)) (apc6 q28 q29))).symm).trans (apc10 q28 q29 (q29 ◇ q29))).trans (apc0 q29 q29)
  have apc28:=fun (q30 q31:G)=>by
    exact ((((cg (fun t => t ◇ (((q31 ◇ q30) ◇ q31) ◇ q31)) (apc6 q31 q31)).trans (apc14 q31 q30 q31 q31)).symm).trans (((cg (fun t => t ◇ (((q31 ◇ q30) ◇ q31) ◇ q31)) (cg (fun t => t ◇ (q31 ◇ q31)) (apc27 q30 q31))).symm).trans ((h (((q31 ◇ q30) ◇ q31) ◇ q31) (q31 ◇ q31) (q31 ◇ q31)).symm))).symm
  have apc29:=fun (q32 q33:G)=>by
    exact ((((cg (fun t => t ◇ (((q32 ◇ q33) ◇ q32) ◇ q32)) (apc3 q32 q32 q32)).trans (apc14 q32 q33 q32 q32)).symm).trans (((cg (fun t => t ◇ (((q32 ◇ q33) ◇ q32) ◇ q32)) (cg (fun t => t ◇ ((q32 ◇ q32) ◇ q32)) (apc9 q32))).symm).trans (apc14 q32 q33 ((q32 ◇ q32) ◇ q32) q32))).symm
  have apc30:=fun (q34 q35:G)=>by
    exact (((((cg (fun t => t ◇ ((q35 ◇ q34) ◇ q35)) (apc15 q34 q35 ((q35 ◇ q35) ◇ q35))).trans (cg (fun t => t ◇ ((q35 ◇ q34) ◇ q35)) (apc9 q35))).trans (apc3 q34 q35 q35)).symm).trans (((cg (fun t => t ◇ ((q35 ◇ q34) ◇ q35)) (cg (fun t => t ◇ ((q35 ◇ q35) ◇ q35)) (apc29 q35 q34))).symm).trans ((h ((q35 ◇ q34) ◇ q35) ((q35 ◇ q35) ◇ q35) q35).symm))).symm
  have apc31:=fun (q36 q37:G)=>by
    exact (((((cg (fun t => t ◇ (q37 ◇ q36)) (apc29 q37 q36)).trans (apc15 q36 q37 (q37 ◇ q36))).trans (apc0 q36 q37)).symm).trans (((cg (fun t => t ◇ (q37 ◇ q36)) (cg (fun t => t ◇ ((q37 ◇ q37) ◇ q37)) (apc30 q36 q37))).symm).trans ((h (q37 ◇ q36) ((q37 ◇ q37) ◇ q37) q37).symm))).symm
  have apc32:=fun (q38 q39:G)=>by
    exact ((cg (fun t => t ◇ q38) (apc30 q39 q38)).symm).trans ((((cg (fun t => t ◇ q38) (cg (fun t => t ◇ ((q38 ◇ q38) ◇ q38)) (apc31 q39 q38))).symm).trans ((h q38 ((q38 ◇ q38) ◇ q38) q39).symm)).trans (apc8 q38))
  have apc34:=fun (q30 q31 q38 q39:G)=>by
    exact (apc28 q30 q31).trans (apc32 q31 q30)
  have apc35:=fun (q40 q41:G)=>by
    exact ((((cg (fun t => t ◇ (q41 ◇ q40)) (apc34 q40 q41 ((((q41 ◇ q40) ◇ q41) ◇ q41) ◇ (q41 ◇ q41)) ((((q41 ◇ q40) ◇ q41) ◇ q41) ◇ (q41 ◇ q41)))).trans (apc0 q40 q41)).symm).trans (((cg (fun t => t ◇ (q41 ◇ q40)) (cg (fun t => t ◇ (q41 ◇ q41)) (apc6 q40 q41))).symm).trans ((h (q41 ◇ q40) (q41 ◇ q41) q41).symm))).symm
  have apc36:=fun (q42 q43:G)=>by
    exact (((((cg (fun t => t ◇ (q43 ◇ q43)) (apc6 q43 (q43 ◇ q42))).trans (apc10 q42 q43 (q43 ◇ q42))).trans (apc0 q42 q43)).symm).trans (((cg (fun t => t ◇ (q43 ◇ q43)) (cg (fun t => t ◇ ((q43 ◇ q42) ◇ (q43 ◇ q42))) (apc35 q43 (q43 ◇ q42)))).symm).trans (apc10 q42 q43 ((q43 ◇ q42) ◇ (q43 ◇ q42))))).symm
  have apc38:=fun (q44 q45 q46:G)=>by
    exact ((((cg (fun t => t ◇ (((q46 ◇ q45) ◇ q44) ◇ q44)) (apc6 q44 q46)).trans (apc14 q44 q45 q46 q46)).symm).trans (((cg (fun t => t ◇ (((q46 ◇ q45) ◇ q44) ◇ q44)) (cg (fun t => t ◇ (q46 ◇ q46)) (apc35 q44 q46))).symm).trans (apc14 q44 q45 (q46 ◇ q46) q46))).symm
  have apc40:=fun (q47 q48:G)=>by
    exact (((cg (fun t => t ◇ (q48 ◇ q48)) (cg (fun t => t ◇ (q48 ◇ q47)) (apc0 q47 q48))).symm).trans (apc38 (q48 ◇ q47) q48 q48)).trans ((cg (fun t => t ◇ q48) (cg (fun t => t ◇ (q48 ◇ q47)) (apc0 q47 q48))).trans (apc4 q47 q48))
  have apc43:=fun (q49 q50 q51:G)=>by
    exact ((cg (fun t => ((((q51 ◇ q50) ◇ q49) ◇ q49) ◇ (((q51 ◇ q50) ◇ q49) ◇ q49)) ◇ t) ((h q51 q49 q50).symm)).symm).trans (apc0 q51 (((q51 ◇ q50) ◇ q49) ◇ q49))
  have apc45:=fun (q32 q33 q38 q39:G)=>by
    exact (apc29 q32 q33).trans (apc32 q32 q33)
  have apc46:=fun (q47 q52 q53:G)=>by
    exact ((cg (fun t => ((((q52 ◇ q47) ◇ q52) ◇ q53) ◇ q53) ◇ t) (apc0 q52 q52)).symm).trans ((((cg (fun t => t ◇ ((q52 ◇ q52) ◇ (q52 ◇ q52))) (cg (fun t => t ◇ q53) (cg (fun t => t ◇ q53) (apc0 q47 q52)))).symm).trans (apc38 q53 (q52 ◇ q47) (q52 ◇ q52))).trans ((cg (fun t => t ◇ (q52 ◇ q52)) (cg (fun t => t ◇ q53) (cg (fun t => t ◇ q53) (apc0 q47 q52)))).trans (apc10 q47 q52 q53)))
  have apc47:=fun (q54 q55:G)=>by
    exact (((((((cg (fun t => t ◇ ((((q54 ◇ q54) ◇ q54) ◇ ((q54 ◇ q54) ◇ q54)) ◇ ((q54 ◇ q54) ◇ q54))) (cg (fun t => t ◇ q55) (cg (fun t => t ◇ q55) (apc45 q54 q54 ((((q54 ◇ q54) ◇ q54) ◇ q54) ◇ ((q54 ◇ q54) ◇ q54)) ((((q54 ◇ q54) ◇ q54) ◇ q54) ◇ ((q54 ◇ q54) ◇ q54)))))).trans (cg (fun t => (((q54 ◇ q54) ◇ q55) ◇ q55) ◇ t) (cg (fun t => t ◇ ((q54 ◇ q54) ◇ q54)) (apc3 q54 q54 q54)))).trans (cg (fun t => (((q54 ◇ q54) ◇ q55) ◇ q55) ◇ t) (apc45 q54 q54 ((((q54 ◇ q54) ◇ q54) ◇ q54) ◇ ((q54 ◇ q54) ◇ q54)) ((((q54 ◇ q54) ◇ q54) ◇ q54) ◇ ((q54 ◇ q54) ◇ q54))))).trans (apc38 q55 q54 q54)).trans (apc2 q54 q55 ((((q54 ◇ q54) ◇ q55) ◇ q55) ◇ q54))).symm).trans ((((cg (fun t => t ◇ ((((q54 ◇ q54) ◇ q54) ◇ ((q54 ◇ q54) ◇ q54)) ◇ ((q54 ◇ q54) ◇ q54))) (cg (fun t => t ◇ q55) (cg (fun t => t ◇ q55) (cg (fun t => t ◇ ((q54 ◇ q54) ◇ q54)) (apc13 q54))))).symm).trans (apc46 (((q54 ◇ q54) ◇ q54) ◇ q54) ((q54 ◇ q54) ◇ q54) q55)).trans (cg (fun t => t ◇ q55) (apc3 q54 q54 q54)))).symm
  have apc48:=fun (q56 q57:G)=>by
    exact (((apc47 q57 (((q57 ◇ q56) ◇ q57) ◇ q57)).symm).trans (apc14 q57 q56 q57 q57)).trans (apc32 q57 q56)
  have apc49:=fun (q58 q59:G)=>by
    exact (((((cg (fun t => (q58 ◇ (((q58 ◇ q58) ◇ q58) ◇ q58)) ◇ t) (apc47 q58 q59)).trans (cg (fun t => t ◇ (q58 ◇ q59)) (apc48 q58 q58))).trans (apc0 q59 q58)).symm).trans ((((cg (fun t => t ◇ ((((q58 ◇ q58) ◇ q58) ◇ q58) ◇ q59)) (apc47 q58 (((q58 ◇ q58) ◇ q58) ◇ q58))).symm).trans (apc0 q59 (((q58 ◇ q58) ◇ q58) ◇ q58))).trans (cg (fun t => t ◇ (((q58 ◇ q58) ◇ q58) ◇ q58)) (apc47 q58 q59)))).symm
  have apc50:=fun (q60 q61:G)=>by
    exact ((cg (fun t => t ◇ ((q61 ◇ q61) ◇ q61)) (cg (fun t => t ◇ q60) (apc47 q61 q60))).symm).trans ((h ((q61 ◇ q61) ◇ q61) q60 q61).symm)
  have apc51:=fun (q62 q63 q64 q65:G)=>by
    exact ((cg (fun t => t ◇ ((q63 ◇ q64) ◇ q63)) (cg (fun t => t ◇ q65) (cg (fun t => t ◇ q65) (apc3 q62 q63 q64)))).symm).trans ((h ((q63 ◇ q64) ◇ q63) q65 ((q63 ◇ q62) ◇ q64)).symm)
  have apc54:=fun (q66 q67:G)=>by
    exact (((apc47 q66 (((q66 ◇ q66) ◇ q67) ◇ q66)).symm).trans (((cg (fun t => t ◇ (((q66 ◇ q66) ◇ q67) ◇ q66)) (apc6 q66 q66)).symm).trans (apc3 q67 (q66 ◇ q66) q66))).symm
  have apc60:=fun (q68 q69:G)=>by
    exact (((cg (fun t => t ◇ ((((q68 ◇ q68) ◇ q69) ◇ q68) ◇ q68)) (apc7 q68)).symm).trans (((cg (fun t => t ◇ ((((q68 ◇ q68) ◇ q69) ◇ q68) ◇ q68)) (apc40 q68 q68)).symm).trans (apc14 q68 q69 (q68 ◇ q68) (q68 ◇ q68)))).symm
  have apc61:=fun (q70 q71:G)=>by
    exact ((apc60 q70 q71).symm).trans ((h (q70 ◇ q70) q70 q71).symm)
  have apc62:=fun (q22 q23 q70 q71:G)=>by
    exact (apc20 q22 q23).trans (apc61 q23 q22)
  have apc63:=fun (q72 q73:G)=>by
    exact ((apc5 q73 q72).symm).trans (((cg (fun t => t ◇ ((q73 ◇ q73) ◇ q72)) (apc62 q72 q73 q72 q72)).symm).trans ((h ((q73 ◇ q73) ◇ q72) q73 q73).symm))
  have apc64:=fun (q72 q73:G)=>by
    exact (((apc47 q73 (((q73 ◇ q73) ◇ q72) ◇ q73)).symm).trans (((cg (fun t => t ◇ (((q73 ◇ q73) ◇ q72) ◇ q73)) (cg (fun t => t ◇ q73) (apc62 q72 q73 q72 q72))).symm).trans ((h (((q73 ◇ q73) ◇ q72) ◇ q73) q73 q73).symm))).symm
  have apc65:=fun (q74 q75:G)=>by
    exact ((((((cg (fun t => t ◇ ((((q75 ◇ q75) ◇ q74) ◇ q75) ◇ q75)) (cg (fun t => (((q75 ◇ q75) ◇ q75) ◇ q75) ◇ t) (cg (fun t => t ◇ q75) (apc62 q74 q75 (((((q75 ◇ q75) ◇ q74) ◇ q75) ◇ q75) ◇ q75) (((((q75 ◇ q75) ◇ q74) ◇ q75) ◇ q75) ◇ q75))))).trans (cg (fun t => t ◇ ((((q75 ◇ q75) ◇ q74) ◇ q75) ◇ q75)) (apc14 q75 q75 q75 q75))).trans (cg (fun t => t ◇ ((((q75 ◇ q75) ◇ q74) ◇ q75) ◇ q75)) (apc2 q75 q75 ((((q75 ◇ q75) ◇ q75) ◇ q75) ◇ q75)))).trans (apc61 q75 q74)).symm).trans ((((cg (fun t => t ◇ ((((q75 ◇ q75) ◇ q74) ◇ q75) ◇ q75)) (cg (fun t => t ◇ ((((((q75 ◇ q75) ◇ q74) ◇ q75) ◇ q75) ◇ q75) ◇ q75)) (cg (fun t => t ◇ q75) (apc62 q74 q75 q74 q74)))).symm).trans (apc43 q75 q75 (((q75 ◇ q75) ◇ q74) ◇ q75))).trans ((((cg (fun t => t ◇ ((((((q75 ◇ q75) ◇ q74) ◇ q75) ◇ q75) ◇ q75) ◇ q75)) (cg (fun t => t ◇ (((q75 ◇ q75) ◇ q74) ◇ q75)) (cg (fun t => t ◇ q75) (apc62 q74 q75 (((((q75 ◇ q75) ◇ q74) ◇ q75) ◇ q75) ◇ q75) (((((q75 ◇ q75) ◇ q74) ◇ q75) ◇ q75) ◇ q75))))).trans (cg (fun t => ((((q75 ◇ q75) ◇ q75) ◇ q75) ◇ (((q75 ◇ q75) ◇ q74) ◇ q75)) ◇ t) (cg (fun t => t ◇ q75) (apc62 q74 q75 (((((q75 ◇ q75) ◇ q74) ◇ q75) ◇ q75) ◇ q75) (((((q75 ◇ q75) ◇ q74) ◇ q75) ◇ q75) ◇ q75))))).trans (cg (fun t => t ◇ (((q75 ◇ q75) ◇ q75) ◇ q75)) (apc47 q75 (((q75 ◇ q75) ◇ q74) ◇ q75)))).trans (apc49 q75 (((q75 ◇ q75) ◇ q74) ◇ q75))))).symm
  have apc71:=fun (q76 q60 q61:G)=>by
    exact (((cg (fun t => t ◇ (((q76 ◇ q76) ◇ q76) ◇ q76)) (cg (fun t => t ◇ q60) (cg (fun t => t ◇ q60) (apc47 q76 q61)))).symm).trans ((h (((q76 ◇ q76) ◇ q76) ◇ q76) q60 q61).symm)).trans (apc47 q76 q60)
  have apc72:=fun (q77 q78 q79:G)=>by
    exact ((((cg (fun t => ((((q77 ◇ q77) ◇ q79) ◇ q78) ◇ q78) ◇ t) (cg (fun t => t ◇ (q77 ◇ q77)) (apc6 q77 q77))).trans (cg (fun t => ((((q77 ◇ q77) ◇ q79) ◇ q78) ◇ q78) ◇ t) (apc38 q77 q77 q77))).trans (cg (fun t => ((((q77 ◇ q77) ◇ q79) ◇ q78) ◇ q78) ◇ t) (apc2 q77 q77 ((((q77 ◇ q77) ◇ q77) ◇ q77) ◇ q77)))).symm).trans (((cg (fun t => ((((q77 ◇ q77) ◇ q79) ◇ q78) ◇ q78) ◇ t) (cg (fun t => t ◇ (q77 ◇ q77)) (cg (fun t => t ◇ (q77 ◇ q77)) (apc0 q77 q77)))).symm).trans (apc71 (q77 ◇ q77) q78 q79))
  have apc73:=fun (q80 q81 q82:G)=>by
    exact ((((cg (fun t => t ◇ ((q80 ◇ q81) ◇ q82)) (apc49 q80 q82)).trans (apc3 q81 q80 q82)).symm).trans (((cg (fun t => t ◇ ((q80 ◇ q81) ◇ q82)) (cg (fun t => t ◇ (((q80 ◇ q80) ◇ q80) ◇ q80)) (apc71 q80 q82 q81))).symm).trans ((h ((q80 ◇ q81) ◇ q82) (((q80 ◇ q80) ◇ q80) ◇ q80) q82).symm))).symm
  have apc77:=fun (q83 q84 q85:G)=>by
    exact ((((cg (fun t => t ◇ (((q85 ◇ q84) ◇ q83) ◇ q83)) (apc30 q83 q85)).trans (apc14 q83 q84 q85 q85)).symm).trans (((cg (fun t => t ◇ (((q85 ◇ q84) ◇ q83) ◇ q83)) (cg (fun t => t ◇ ((q85 ◇ q85) ◇ q85)) (apc31 q83 q85))).symm).trans (apc14 q83 q84 ((q85 ◇ q85) ◇ q85) q85))).symm
  have apc78:=fun (q86 q87:G)=>by
    exact ((((cg (fun t => ((q87 ◇ q86) ◇ q86) ◇ t) (cg (fun t => t ◇ ((q87 ◇ q87) ◇ q87)) (apc3 q87 q87 q87))).trans (cg (fun t => ((q87 ◇ q86) ◇ q86) ◇ t) (apc47 q87 ((q87 ◇ q87) ◇ q87)))).trans (cg (fun t => ((q87 ◇ q86) ◇ q86) ◇ t) (apc8 q87))).symm).trans ((((cg (fun t => t ◇ ((((q87 ◇ q87) ◇ q87) ◇ ((q87 ◇ q87) ◇ q87)) ◇ ((q87 ◇ q87) ◇ q87))) (cg (fun t => t ◇ q86) (apc47 q87 q86))).symm).trans (apc77 q86 q87 ((q87 ◇ q87) ◇ q87))).trans ((cg (fun t => t ◇ ((q87 ◇ q87) ◇ q87)) (cg (fun t => t ◇ q86) (apc47 q87 q86))).trans (apc50 q86 q87)))
  have apc79:=fun (q88 q89 q90:G)=>by
    exact ((((cg (fun t => t ◇ (((q90 ◇ q89) ◇ q88) ◇ q88)) (apc0 (q90 ◇ q88) (q90 ◇ q88))).trans (apc14 q88 q89 (q90 ◇ q88) q90)).symm).trans (((cg (fun t => t ◇ (((q90 ◇ q89) ◇ q88) ◇ q88)) (cg (fun t => t ◇ ((q90 ◇ q88) ◇ (q90 ◇ q88))) (apc7 (q90 ◇ q88)))).symm).trans (apc14 q88 q89 ((q90 ◇ q88) ◇ (q90 ◇ q88)) q90))).symm
  have apc81:=fun (q91 q92 q93:G)=>by
    exact ((cg (fun t => t ◇ (((q92 ◇ q93) ◇ q92) ◇ q92)) (cg (fun t => t ◇ (q92 ◇ q91)) (apc0 q91 q92))).symm).trans (apc14 q92 q93 (q92 ◇ q91) q92)
  have apc93:=fun (q18 q19 q21 q20:G)=>by
    exact (((cg (fun t => t ◇ (((((q20 ◇ q18) ◇ q19) ◇ q21) ◇ q19) ◇ q19)) (cg (fun t => t ◇ q20) ((h q20 q19 q18).symm))).symm).trans (apc14 q19 q21 q20 ((q20 ◇ q18) ◇ q19))).symm
  have apc94:=fun (q94 q95:G)=>by
    exact (((apc38 q94 q94 q95).symm).trans ((((cg (fun t => t ◇ (q95 ◇ q95)) (cg (fun t => t ◇ q94) (cg (fun t => t ◇ q94) (apc2 q95 q94 q94)))).symm).trans (apc93 q94 q94 q95 (q95 ◇ q95))).trans ((cg (fun t => (((q95 ◇ q95) ◇ q94) ◇ (q95 ◇ q95)) ◇ t) (cg (fun t => t ◇ q94) (cg (fun t => t ◇ q94) (apc2 q95 q94 ((((q95 ◇ q95) ◇ q94) ◇ q94) ◇ q95))))).trans (cg (fun t => t ◇ (((q95 ◇ q94) ◇ q94) ◇ q94)) (apc63 q94 q95))))).symm
  have apc95:=fun (q96 q97:G)=>by
    exact (((((cg (fun t => (((q96 ◇ (((q96 ◇ q96) ◇ q96) ◇ q96)) ◇ q97) ◇ (((q96 ◇ q96) ◇ q96) ◇ q96)) ◇ t) (cg (fun t => t ◇ q97) (cg (fun t => t ◇ q97) (apc47 q96 q97)))).trans (cg (fun t => t ◇ (((q96 ◇ q97) ◇ q97) ◇ q97)) (cg (fun t => t ◇ (((q96 ◇ q96) ◇ q96) ◇ q96)) (cg (fun t => t ◇ q97) (apc48 q96 q96))))).trans (cg (fun t => t ◇ (((q96 ◇ q97) ◇ q97) ◇ q97)) (apc73 q96 q96 q97))).trans (apc94 q97 q96)).symm).trans ((((cg (fun t => t ◇ ((((((q96 ◇ q96) ◇ q96) ◇ q96) ◇ q97) ◇ q97) ◇ q97)) (cg (fun t => t ◇ (((q96 ◇ q96) ◇ q96) ◇ q96)) (cg (fun t => t ◇ q97) (apc47 q96 (((q96 ◇ q96) ◇ q96) ◇ q96))))).symm).trans (apc94 q97 (((q96 ◇ q96) ◇ q96) ◇ q96))).trans ((cg (fun t => t ◇ (((q96 ◇ q96) ◇ q96) ◇ q96)) (cg (fun t => t ◇ q97) (cg (fun t => t ◇ q97) (apc47 q96 q97)))).trans (apc71 q96 q97 q97)))
  have apc96:=fun (q98 q99:G)=>by
    exact ((((cg (fun t => t ◇ (q99 ◇ q98)) (apc14 q98 q98 q98 q99)).trans (apc95 (q99 ◇ q98) q98)).symm).trans ((((cg (fun t => ((((q99 ◇ q98) ◇ q98) ◇ q98) ◇ (((q99 ◇ q98) ◇ q98) ◇ q98)) ◇ t) (apc95 q99 q98)).symm).trans (apc0 q99 (((q99 ◇ q98) ◇ q98) ◇ q98))).trans (cg (fun t => t ◇ (((q99 ◇ q98) ◇ q98) ◇ q98)) (apc95 q99 q98)))).symm
  have apc100:=fun (q94 q95 q96 q97:G)=>by
    exact (apc94 q94 q95).trans (apc95 q95 q94)
  have apc101:=fun (q100 q101:G)=>by
    exact ((cg (fun t => (q101 ◇ q100) ◇ t) (apc14 q100 q100 q100 q101)).symm).trans ((((cg (fun t => t ◇ ((((q101 ◇ q100) ◇ q100) ◇ q100) ◇ (((q101 ◇ q100) ◇ q100) ◇ q100))) (apc95 q101 q100)).symm).trans (apc35 q101 (((q101 ◇ q100) ◇ q100) ◇ q100))).trans ((cg (fun t => t ◇ (((q101 ◇ q100) ◇ q100) ◇ q100)) (apc95 q101 q100)).trans (apc96 q100 q101)))
  have apc102:=fun (q102 q103:G)=>by
    exact ((((cg (fun t => t ◇ q102) (apc96 q103 (q102 ◇ q103))).trans (apc95 q102 q103)).symm).trans (((cg (fun t => t ◇ q102) (cg (fun t => t ◇ ((((q102 ◇ q103) ◇ q103) ◇ q103) ◇ q103)) (apc101 q103 q102))).symm).trans ((h q102 ((((q102 ◇ q103) ◇ q103) ◇ q103) ◇ q103) q103).symm))).symm
  have apc104:=fun (q104 q105 q106:G)=>by
    exact ((((cg (fun t => t ◇ (((q105 ◇ q105) ◇ q105) ◇ q105)) (apc101 q104 (q105 ◇ q106))).trans (apc71 q105 q104 q106)).symm).trans (((cg (fun t => t ◇ (((q105 ◇ q105) ◇ q105) ◇ q105)) (cg (fun t => t ◇ (((((q105 ◇ q106) ◇ q104) ◇ q104) ◇ q104) ◇ q104)) (apc102 (q105 ◇ q106) q104))).symm).trans (apc71 q105 (((((q105 ◇ q106) ◇ q104) ◇ q104) ◇ q104) ◇ q104) q106))).symm
  have apc105:=fun (q107 q108 q109:G)=>by
    exact ((cg (fun t => ((q108 ◇ q107) ◇ q109) ◇ t) (apc32 q108 q109)).symm).trans (((cg (fun t => ((q108 ◇ q107) ◇ q109) ◇ t) (cg (fun t => t ◇ q108) (cg (fun t => t ◇ q108) (cg (fun t => t ◇ q108) ((h q108 q109 q107).symm))))).symm).trans (apc104 q108 ((q108 ◇ q107) ◇ q109) q109))
  have apc106:=fun (q18 q19 q21 q20:G)=>by
    exact (((apc51 q18 q19 q21 q20).symm).trans (((cg (fun t => (((((q19 ◇ q18) ◇ q21) ◇ q19) ◇ q20) ◇ q20) ◇ t) (cg (fun t => t ◇ q19) ((h q19 q21 q18).symm))).symm).trans (apc14 q19 q21 q20 ((q19 ◇ q18) ◇ q21)))).symm
  have apc107:=fun (q110 q111 q112:G)=>by
    exact (((cg (fun t => t ◇ ((((q112 ◇ q110) ◇ q111) ◇ q111) ◇ q112)) (apc32 q112 q111)).symm).trans (((cg (fun t => t ◇ ((((q112 ◇ q110) ◇ q111) ◇ q111) ◇ q112)) (cg (fun t => t ◇ q112) (apc106 q110 q112 q111 q112))).symm).trans (apc95 ((((q112 ◇ q110) ◇ q111) ◇ q111) ◇ q112) q112))).symm
  have apc108:=fun (q113 q114 q115:G)=>by
    exact (((cg (fun t => t ◇ q115) ((h q115 q114 q113).symm)).symm).trans (apc107 q113 q114 q115)).symm
  have apc109:=fun (q113 q114 q115 q110 q111 q112:G)=>by
    exact (apc107 q110 q111 q112).trans (apc108 q110 q111 q112)
  have apc129:=fun (q116 q117:G)=>by
    exact (((cg (fun t => (((q117 ◇ q116) ◇ q116) ◇ q116) ◇ t) (apc14 q116 q116 q116 q117)).symm).trans (apc7 (((q117 ◇ q116) ◇ q116) ◇ q116))).trans (apc14 q116 q116 q116 q117)
  have apc132:=fun (q118 q119:G)=>by
    exact (((apc79 q118 q118 q119).symm).trans (apc78 q118 (q119 ◇ q118))).symm
  have apc138:=fun (q120 q121:G)=>by
    exact (((apc96 q121 (q120 ◇ q121)).symm).trans (((cg (fun t => ((q120 ◇ q121) ◇ q121) ◇ t) (apc14 q121 q121 q121 q120)).symm).trans (apc24 ((q120 ◇ q121) ◇ q121) q121))).symm
  have apc144:=fun (q122 q123 q124:G)=>by
    exact ((cg (fun t => t ◇ ((q124 ◇ q122) ◇ q123)) (apc16 q122 q123 q124)).symm).trans ((h ((q124 ◇ q122) ◇ q123) q124 q124).symm)
  have apc148:=fun (q125 q126 q127:G)=>by
    exact ((cg (fun t => (((q127 ◇ q125) ◇ q126) ◇ q127) ◇ t) (apc62 ((((q127 ◇ q125) ◇ q126) ◇ q127) ◇ q127) q127 (((((q127 ◇ q127) ◇ ((((q127 ◇ q125) ◇ q126) ◇ q127) ◇ q127)) ◇ q127) ◇ q127) ◇ q127) (((((q127 ◇ q127) ◇ ((((q127 ◇ q125) ◇ q126) ◇ q127) ◇ q127)) ◇ q127) ◇ q127) ◇ q127))).symm).trans (((cg (fun t => (((q127 ◇ q125) ◇ q126) ◇ q127) ◇ t) (cg (fun t => t ◇ q127) (cg (fun t => t ◇ q127) (cg (fun t => t ◇ q127) (apc16 q125 q126 q127))))).symm).trans (apc104 q127 (((q127 ◇ q125) ◇ q126) ◇ q127) q127))
  have apc160:=fun (q128 q129:G)=>by
    exact (((cg (fun t => t ◇ (((q128 ◇ q128) ◇ q129) ◇ ((q128 ◇ q128) ◇ q129))) (apc0 q128 q128)).symm).trans (apc36 q129 (q128 ◇ q128))).trans (apc105 q128 q128 q129)
  have apc180:=fun (q130 q131 q132:G)=>by
    exact (((((cg (fun t => (((q130 ◇ q130) ◇ q131) ◇ q132) ◇ t) (cg (fun t => t ◇ (q130 ◇ q130)) (cg (fun t => t ◇ (q130 ◇ q130)) (apc105 q130 q130 q132)))).trans (cg (fun t => (((q130 ◇ q130) ◇ q131) ◇ q132) ◇ t) (cg (fun t => t ◇ (q130 ◇ q130)) (apc54 q130 q132)))).trans (cg (fun t => (((q130 ◇ q130) ◇ q131) ◇ q132) ◇ t) (apc35 (((q130 ◇ q130) ◇ q132) ◇ q130) q130))).trans (cg (fun t => (((q130 ◇ q130) ◇ q131) ◇ q132) ◇ t) (apc65 q132 q130))).symm).trans (((cg (fun t => (((q130 ◇ q130) ◇ q131) ◇ q132) ◇ t) (cg (fun t => t ◇ (q130 ◇ q130)) (cg (fun t => t ◇ (q130 ◇ q130)) (cg (fun t => t ◇ (q130 ◇ q130)) (apc72 q130 q132 q131))))).symm).trans (apc104 (q130 ◇ q130) (((q130 ◇ q130) ◇ q131) ◇ q132) q132))
  have apc181:=fun (q133 q134 q135:G)=>by
    exact (((apc148 q133 q134 q135).symm).trans ((((cg (fun t => t ◇ ((q135 ◇ q135) ◇ q135)) (apc144 q133 q134 q135)).symm).trans (apc180 q135 ((((q135 ◇ q133) ◇ q134) ◇ q135) ◇ q135) ((q135 ◇ q133) ◇ q134))).trans (cg (fun t => t ◇ (q135 ◇ q135)) (apc144 q133 q134 q135)))).symm
  have apc184:=fun (q136 q137 q138:G)=>by
    exact ((cg (fun t => t ◇ (((q137 ◇ q137) ◇ q136) ◇ q137)) (cg (fun t => t ◇ q138) (cg (fun t => t ◇ q138) (apc100 q136 q137 q136 q136)))).symm).trans ((h (((q137 ◇ q137) ◇ q136) ◇ q137) q138 (((q137 ◇ q136) ◇ q136) ◇ q136)).symm)
  have apc185:=fun (q139 q140:G)=>by
    exact (((cg (fun t => t ◇ (((q140 ◇ q140) ◇ q139) ◇ q140)) (apc138 q140 q139)).trans (apc184 q139 q140 q139)).symm).trans ((((cg (fun t => t ◇ (((q140 ◇ q140) ◇ q139) ◇ q140)) (cg (fun t => t ◇ (((q140 ◇ q139) ◇ q139) ◇ q139)) (apc96 q139 q140))).symm).trans (apc184 q139 q140 (((q140 ◇ q139) ◇ q139) ◇ q139))).trans (apc100 q139 q140 ((((q140 ◇ q140) ◇ q139) ◇ q140) ◇ (((q140 ◇ q139) ◇ q139) ◇ q139)) ((((q140 ◇ q140) ◇ q139) ◇ q140) ◇ (((q140 ◇ q139) ◇ q139) ◇ q139))))
  have apc186:=fun (q141 q142:G)=>by
    exact (((cg (fun t => t ◇ q142) (cg (fun t => t ◇ ((q141 ◇ q141) ◇ q141)) (apc47 q141 q142))).trans (cg (fun t => t ◇ q142) (apc31 q142 q141))).symm).trans (((cg (fun t => t ◇ q142) (cg (fun t => t ◇ ((q141 ◇ q141) ◇ q141)) (cg (fun t => t ◇ q142) (apc3 q141 q141 q141)))).symm).trans (apc185 q142 ((q141 ◇ q141) ◇ q141)))
  have apc198:=fun (q143 q144:G)=>by
    exact ((((cg (fun t => t ◇ q143) (apc138 q143 q144)).trans (apc95 q143 q144)).symm).trans (((cg (fun t => t ◇ q143) (cg (fun t => t ◇ (((q143 ◇ q144) ◇ q144) ◇ q144)) (apc96 q144 q143))).symm).trans ((h q143 (((q143 ◇ q144) ◇ q144) ◇ q144) q144).symm))).symm
  have apc199:=fun (q145 q146:G)=>by
    exact ((apc14 q146 q145 q145 q146).symm).trans ((((cg (fun t => (((q146 ◇ q146) ◇ q145) ◇ q145) ◇ t) (cg (fun t => t ◇ q146) (cg (fun t => t ◇ q146) (apc2 q146 q145 q145)))).symm).trans (apc198 (((q146 ◇ q146) ◇ q145) ◇ q145) q146)).trans (apc2 q146 q145 ((((q146 ◇ q146) ◇ q145) ◇ q145) ◇ q146)))
  have apc200:=fun (q147 q148 q149:G)=>by
    exact ((apc71 q147 (((q147 ◇ q149) ◇ q148) ◇ q148) q148).symm).trans ((((cg (fun t => t ◇ (((q147 ◇ q147) ◇ q147) ◇ q147)) (cg (fun t => t ◇ (((q147 ◇ q149) ◇ q148) ◇ q148)) (cg (fun t => t ◇ (((q147 ◇ q149) ◇ q148) ◇ q148)) (apc71 q147 q148 q149)))).symm).trans (apc199 (((q147 ◇ q147) ◇ q147) ◇ q147) (((q147 ◇ q149) ◇ q148) ◇ q148))).trans (apc71 q147 q148 q149))
  have apc201:=fun (q150 q151:G)=>by
    exact (((apc3 q150 q151 q150).symm).trans (((cg (fun t => ((q151 ◇ q150) ◇ q151) ◇ t) (cg (fun t => t ◇ q150) (apc199 q150 q151))).symm).trans (apc200 ((q151 ◇ q150) ◇ q151) q150 q151))).symm
  have apc204:=fun (q152 q153:G)=>by
    exact ((cg (fun t => t ◇ q153) (apc181 q152 q153 q152)).symm).trans (((cg (fun t => t ◇ q153) (cg (fun t => t ◇ (q152 ◇ q152)) (apc105 q152 q152 q153))).symm).trans (apc199 q153 (q152 ◇ q152)))
  have apc206:=fun (q154 q155 q156:G)=>by
    exact ((cg (fun t => ((q155 ◇ q154) ◇ q156) ◇ t) (cg (fun t => t ◇ q155) ((h q155 q156 q154).symm))).symm).trans (apc200 ((q155 ◇ q154) ◇ q156) q155 q156)
  have apc208:=fun (q157 q158 q159:G)=>by
    exact ((apc14 q157 q158 q159 (q159 ◇ q159)).symm).trans ((((cg (fun t => t ◇ ((((q159 ◇ q159) ◇ q158) ◇ q157) ◇ q157)) (cg (fun t => t ◇ q159) (cg (fun t => t ◇ q159) (apc200 (q159 ◇ q159) q157 q158)))).symm).trans (apc204 q159 ((((q159 ◇ q159) ◇ q158) ◇ q157) ◇ q157))).trans (apc200 (q159 ◇ q159) q157 q158))
  have apc210:=fun (q160 q161 q162:G)=>by
    exact ((cg (fun t => t ◇ q162) (cg (fun t => t ◇ q161) (cg (fun t => t ◇ q161) (apc0 q160 q162)))).symm).trans (apc208 q161 (q162 ◇ q160) q162)
  have apc214:=fun (q163 q164:G)=>by
    exact ((cg (fun t => t ◇ q164) (cg (fun t => t ◇ q163) (apc201 q163 q164))).symm).trans (apc210 q163 q163 q164)
  have apc217:=fun (q165 q166 q167:G)=>by
    exact (((cg (fun t => (((q166 ◇ q166) ◇ q165) ◇ q167) ◇ t) (apc208 q166 q167 q166)).trans (apc180 q166 q165 q167)).symm).trans (((cg (fun t => (((q166 ◇ q166) ◇ q165) ◇ q167) ◇ t) (cg (fun t => t ◇ q166) (cg (fun t => t ◇ q166) (cg (fun t => t ◇ q166) (apc208 q167 q165 q166))))).symm).trans (apc104 q166 (((q166 ◇ q166) ◇ q165) ◇ q167) q167))
  have apc231:=fun (q168 q169:G)=>by
    exact ((((cg (fun t => t ◇ ((((q169 ◇ q168) ◇ q168) ◇ q168) ◇ q168)) (apc14 q168 q168 q168 q169)).trans (apc14 q168 q168 q168 (q169 ◇ q168))).symm).trans ((((cg (fun t => ((((q169 ◇ q168) ◇ q168) ◇ q168) ◇ (((q169 ◇ q168) ◇ q168) ◇ q168)) ◇ t) (apc129 q168 q169)).symm).trans (apc0 ((((q169 ◇ q168) ◇ q168) ◇ q168) ◇ q168) (((q169 ◇ q168) ◇ q168) ◇ q168))).trans (cg (fun t => t ◇ (((q169 ◇ q168) ◇ q168) ◇ q168)) (apc138 (q169 ◇ q168) q168)))).symm
  have apc232:=fun (q170 q171:G)=>by
    exact (((cg (fun t => ((((q171 ◇ q170) ◇ q171) ◇ q171) ◇ q171) ◇ t) (cg (fun t => t ◇ q171) (apc109 (((((q171 ◇ q170) ◇ q170) ◇ q170) ◇ q171) ◇ q171) (((((q171 ◇ q170) ◇ q170) ◇ q170) ◇ q171) ◇ q171) (((((q171 ◇ q170) ◇ q170) ◇ q170) ◇ q171) ◇ q171) q170 q170 q171))).trans (cg (fun t => t ◇ (((q171 ◇ q170) ◇ q171) ◇ q171)) (apc32 q171 q170))).symm).trans ((((cg (fun t => t ◇ ((((((q171 ◇ q170) ◇ q170) ◇ q170) ◇ q171) ◇ q171) ◇ q171)) (cg (fun t => t ◇ q171) (cg (fun t => t ◇ q171) (cg (fun t => t ◇ q171) ((h q171 q170 q170).symm))))).symm).trans (apc231 q171 (((q171 ◇ q170) ◇ q170) ◇ q170))).trans ((cg (fun t => t ◇ q171) (cg (fun t => t ◇ q171) (cg (fun t => t ◇ q171) (apc109 (((((q171 ◇ q170) ◇ q170) ◇ q170) ◇ q171) ◇ q171) (((((q171 ◇ q170) ◇ q170) ◇ q170) ◇ q171) ◇ q171) (((((q171 ◇ q170) ◇ q170) ◇ q170) ◇ q171) ◇ q171) q170 q170 q171)))).trans (cg (fun t => t ◇ q171) (apc32 q171 q170))))
  have apc233:=fun (q172 q173:G)=>by
    exact (((((((cg (fun t => t ◇ (q173 ◇ q173)) (cg (fun t => t ◇ ((((q173 ◇ q173) ◇ q172) ◇ (q173 ◇ q173)) ◇ (q173 ◇ q173))) (cg (fun t => t ◇ (q173 ◇ q173)) (apc0 q173 q173)))).trans (cg (fun t => t ◇ (q173 ◇ q173)) (cg (fun t => (((q173 ◇ q173) ◇ q173) ◇ (q173 ◇ q173)) ◇ t) (cg (fun t => t ◇ (q173 ◇ q173)) (apc105 q173 q173 q172))))).trans (cg (fun t => t ◇ (q173 ◇ q173)) (cg (fun t => t ◇ ((((q173 ◇ q173) ◇ q172) ◇ q173) ◇ (q173 ◇ q173))) (apc105 q173 q173 q173)))).trans (cg (fun t => t ◇ (q173 ◇ q173)) (cg (fun t => (((q173 ◇ q173) ◇ q173) ◇ q173) ◇ t) (apc181 q173 q172 q173)))).trans (cg (fun t => t ◇ (q173 ◇ q173)) (apc47 q173 ((((q173 ◇ q173) ◇ q172) ◇ q173) ◇ q173)))).trans (apc35 ((((q173 ◇ q173) ◇ q172) ◇ q173) ◇ q173) q173)).symm).trans ((((cg (fun t => t ◇ (q173 ◇ q173)) (cg (fun t => t ◇ ((((q173 ◇ q173) ◇ q172) ◇ (q173 ◇ q173)) ◇ (q173 ◇ q173))) (apc232 q172 (q173 ◇ q173)))).symm).trans (apc72 q173 ((((q173 ◇ q173) ◇ q172) ◇ (q173 ◇ q173)) ◇ (q173 ◇ q173)) (q173 ◇ q173))).trans (((cg (fun t => (q173 ◇ q173) ◇ t) (cg (fun t => t ◇ (q173 ◇ q173)) (apc105 q173 q173 q172))).trans (cg (fun t => (q173 ◇ q173) ◇ t) (apc181 q173 q172 q173))).trans (apc200 (q173 ◇ q173) q173 q172)))
  have apc236:=fun (q174 q175:G)=>by
    exact (((((((cg (fun t => t ◇ (((((((q174 ◇ q174) ◇ q174) ◇ q175) ◇ q175) ◇ (q174 ◇ q174)) ◇ (q174 ◇ q174)) ◇ (q174 ◇ q174))) (cg (fun t => t ◇ (q174 ◇ q174)) (cg (fun t => t ◇ (q174 ◇ q174)) (apc105 q174 q174 q175)))).trans (cg (fun t => (((((q174 ◇ q174) ◇ q175) ◇ q174) ◇ (q174 ◇ q174)) ◇ (q174 ◇ q174)) ◇ t) (cg (fun t => t ◇ (q174 ◇ q174)) (cg (fun t => t ◇ (q174 ◇ q174)) (apc10 q174 q174 q175))))).trans (cg (fun t => (((((q174 ◇ q174) ◇ q175) ◇ q174) ◇ (q174 ◇ q174)) ◇ (q174 ◇ q174)) ◇ t) (cg (fun t => t ◇ (q174 ◇ q174)) (apc105 q174 q174 q175)))).trans (cg (fun t => t ◇ ((((q174 ◇ q174) ◇ q175) ◇ q174) ◇ (q174 ◇ q174))) (cg (fun t => t ◇ (q174 ◇ q174)) (apc181 q174 q175 q174)))).trans (cg (fun t => (((((q174 ◇ q174) ◇ q175) ◇ q174) ◇ q174) ◇ (q174 ◇ q174)) ◇ t) (apc181 q174 q175 q174))).trans (cg (fun t => t ◇ ((((q174 ◇ q174) ◇ q175) ◇ q174) ◇ q174)) (apc72 q174 q174 q175))).symm).trans ((((cg (fun t => t ◇ (((((((q174 ◇ q174) ◇ q174) ◇ q175) ◇ q175) ◇ (q174 ◇ q174)) ◇ (q174 ◇ q174)) ◇ (q174 ◇ q174))) (cg (fun t => t ◇ (q174 ◇ q174)) (cg (fun t => t ◇ (q174 ◇ q174)) (cg (fun t => t ◇ (q174 ◇ q174)) (apc10 q174 q174 q175))))).symm).trans (apc231 (q174 ◇ q174) ((((q174 ◇ q174) ◇ q174) ◇ q175) ◇ q175))).trans (((((cg (fun t => t ◇ (q174 ◇ q174)) (cg (fun t => t ◇ (q174 ◇ q174)) (cg (fun t => t ◇ (q174 ◇ q174)) (cg (fun t => t ◇ (q174 ◇ q174)) (apc10 q174 q174 q175))))).trans (cg (fun t => t ◇ (q174 ◇ q174)) (cg (fun t => t ◇ (q174 ◇ q174)) (cg (fun t => t ◇ (q174 ◇ q174)) (apc105 q174 q174 q175))))).trans (cg (fun t => t ◇ (q174 ◇ q174)) (cg (fun t => t ◇ (q174 ◇ q174)) (apc181 q174 q175 q174)))).trans (cg (fun t => t ◇ (q174 ◇ q174)) (apc72 q174 q174 q175))).trans (apc105 q174 q174 q174)))
  have apc241:=fun (q176 q177:G)=>by
    exact ((((((((cg (fun t => t ◇ ((q176 ◇ q176) ◇ q176)) (cg (fun t => t ◇ ((((q176 ◇ q176) ◇ q177) ◇ q176) ◇ q176)) (cg (fun t => t ◇ ((q176 ◇ q176) ◇ q176)) (apc47 q176 ((((q176 ◇ q176) ◇ q177) ◇ q176) ◇ q176))))).trans (cg (fun t => t ◇ ((q176 ◇ q176) ◇ q176)) (cg (fun t => t ◇ ((((q176 ◇ q176) ◇ q177) ◇ q176) ◇ q176)) (apc31 ((((q176 ◇ q176) ◇ q177) ◇ q176) ◇ q176) q176)))).trans (cg (fun t => t ◇ ((q176 ◇ q176) ◇ q176)) (cg (fun t => t ◇ ((((q176 ◇ q176) ◇ q177) ◇ q176) ◇ q176)) (apc233 q177 q176)))).trans (cg (fun t => t ◇ ((q176 ◇ q176) ◇ q176)) (apc236 q176 q177))).trans (apc47 q176 ((q176 ◇ q176) ◇ q176))).trans (apc8 q176)).symm).trans ((((cg (fun t => t ◇ ((q176 ◇ q176) ◇ q176)) (cg (fun t => t ◇ ((((q176 ◇ q176) ◇ q177) ◇ q176) ◇ q176)) (cg (fun t => t ◇ ((q176 ◇ q176) ◇ q176)) (cg (fun t => t ◇ ((((q176 ◇ q176) ◇ q177) ◇ q176) ◇ q176)) (apc236 q176 q177))))).symm).trans (apc214 ((((q176 ◇ q176) ◇ q177) ◇ q176) ◇ q176) ((q176 ◇ q176) ◇ q176))).trans ((cg (fun t => t ◇ ((((q176 ◇ q176) ◇ q177) ◇ q176) ◇ q176)) (apc3 q176 q176 q176)).trans (apc47 q176 ((((q176 ◇ q176) ◇ q177) ◇ q176) ◇ q176))))).symm
  have apc242:=fun (q178 q179:G)=>by
    exact ((cg (fun t => q178 ◇ t) (apc64 q179 q178)).symm).trans (apc241 q178 q179)
  have apc248:=fun (q14 q180 q15:G)=>by
    exact ((cg (fun t => t ◇ (((q180 ◇ q180) ◇ q15) ◇ (q180 ◇ q14))) (apc105 q14 q180 q180)).symm).trans ((((cg (fun t => t ◇ (((q180 ◇ q180) ◇ q15) ◇ (q180 ◇ q14))) (cg (fun t => t ◇ (q180 ◇ q180)) (apc0 q14 q180))).symm).trans (apc3 q15 (q180 ◇ q180) (q180 ◇ q14))).trans (apc217 q15 q180 (q180 ◇ q14)))
  have apc257:=fun (q181 q182:G)=>by
    exact ((cg (fun t => ((q181 ◇ q181) ◇ q181) ◇ t) (apc64 q182 q181)).symm).trans (apc236 q181 q182)
  have apc260:=fun (q183 q184:G)=>by
    exact ((((cg (fun t => (((q183 ◇ q183) ◇ q183) ◇ ((q183 ◇ q183) ◇ q183)) ◇ t) (cg (fun t => (((q183 ◇ q183) ◇ q184) ◇ q183) ◇ t) (apc160 q183 q184))).trans (cg (fun t => t ◇ ((((q183 ◇ q183) ◇ q184) ◇ q183) ◇ (((q183 ◇ q183) ◇ q184) ◇ q183))) (apc3 q183 q183 q183))).trans (apc47 q183 ((((q183 ◇ q183) ◇ q184) ◇ q183) ◇ (((q183 ◇ q183) ◇ q184) ◇ q183)))).symm).trans ((((cg (fun t => (((q183 ◇ q183) ◇ q183) ◇ ((q183 ◇ q183) ◇ q183)) ◇ t) (cg (fun t => t ◇ (((q183 ◇ q183) ◇ q183) ◇ (((q183 ◇ q183) ◇ q184) ◇ ((q183 ◇ q183) ◇ q184)))) (apc160 q183 q184))).symm).trans (apc36 (((q183 ◇ q183) ◇ q184) ◇ ((q183 ◇ q183) ◇ q184)) ((q183 ◇ q183) ◇ q183))).trans ((cg (fun t => t ◇ ((q183 ◇ q183) ◇ q183)) (apc160 q183 q184)).trans (apc148 q183 q184 q183)))
  have apc262:=fun (q185 q186 q187:G)=>by
    exact (((((((cg (fun t => t ◇ (((q186 ◇ q187) ◇ q186) ◇ q186)) (cg (fun t => t ◇ (q186 ◇ ((((q186 ◇ q186) ◇ q185) ◇ q186) ◇ (((q186 ◇ q186) ◇ q185) ◇ q186)))) (apc208 q186 q185 q186))).trans (cg (fun t => t ◇ (((q186 ◇ q187) ◇ q186) ◇ q186)) (cg (fun t => ((q186 ◇ q186) ◇ q186) ◇ t) (apc260 q186 q185)))).trans (cg (fun t => t ◇ (((q186 ◇ q187) ◇ q186) ◇ q186)) (apc236 q186 q185))).trans (apc14 q186 q187 q186 q186)).trans (apc32 q186 q187)).symm).trans ((((cg (fun t => t ◇ (((q186 ◇ q187) ◇ q186) ◇ q186)) (cg (fun t => t ◇ (q186 ◇ ((((q186 ◇ q186) ◇ q185) ◇ q186) ◇ (((q186 ◇ q186) ◇ q185) ◇ q186)))) (cg (fun t => t ◇ q186) (apc260 q186 q185)))).symm).trans (apc81 ((((q186 ◇ q186) ◇ q185) ◇ q186) ◇ (((q186 ◇ q186) ◇ q185) ◇ q186)) q186 q187)).trans (cg (fun t => (((q186 ◇ q187) ◇ q186) ◇ q186) ◇ t) (apc260 q186 q185)))).symm
  have apc263:=fun (q188 q189 q190:G)=>by
    exact ((((cg (fun t => t ◇ ((q190 ◇ q189) ◇ q190)) (apc200 (q190 ◇ q190) q190 q188)).trans (apc3 q189 q190 q190)).symm).trans (((cg (fun t => t ◇ ((q190 ◇ q189) ◇ q190)) (cg (fun t => t ◇ ((((q190 ◇ q190) ◇ q188) ◇ q190) ◇ q190)) (apc262 q188 q190 q189))).symm).trans ((h ((q190 ◇ q189) ◇ q190) ((((q190 ◇ q190) ◇ q188) ◇ q190) ◇ q190) q190).symm))).symm
  have apc264:=fun (q191 q192 q193:G)=>by
    exact ((((cg (fun t => t ◇ (q193 ◇ q192)) (apc262 q191 q193 q192)).trans (apc0 q192 q193)).symm).trans (((cg (fun t => t ◇ (q193 ◇ q192)) (cg (fun t => t ◇ ((((q193 ◇ q193) ◇ q191) ◇ q193) ◇ q193)) (apc263 q191 q192 q193))).symm).trans ((h (q193 ◇ q192) ((((q193 ◇ q193) ◇ q191) ◇ q193) ◇ q193) q193).symm))).symm
  have apc265:=fun (q194 q195 q196:G)=>by
    exact ((cg (fun t => (q196 ◇ q195) ◇ t) (apc64 q194 q196)).symm).trans (apc264 q194 q195 q196)
  have apc266:=fun (q197 q198 q199:G)=>by
    exact ((((((cg (fun t => t ◇ q199) (cg (fun t => t ◇ (q198 ◇ (((q198 ◇ q198) ◇ q197) ◇ q198))) (cg (fun t => t ◇ (q198 ◇ (((q198 ◇ q198) ◇ q197) ◇ q198))) (apc65 q197 q198)))).trans (cg (fun t => t ◇ q199) (cg (fun t => t ◇ (q198 ◇ (((q198 ◇ q198) ◇ q197) ◇ q198))) (apc257 q198 q197)))).trans (cg (fun t => t ◇ q199) (apc47 q198 (q198 ◇ (((q198 ◇ q198) ◇ q197) ◇ q198))))).trans (cg (fun t => t ◇ q199) (apc242 q198 q197))).symm).trans (((cg (fun t => t ◇ q199) (cg (fun t => t ◇ (q198 ◇ (((q198 ◇ q198) ◇ q197) ◇ q198))) (cg (fun t => t ◇ (q198 ◇ (((q198 ◇ q198) ◇ q197) ◇ q198))) (apc265 q197 (((q198 ◇ q198) ◇ q197) ◇ q198) q198)))).symm).trans (apc47 (q198 ◇ (((q198 ◇ q198) ◇ q197) ◇ q198)) q199))).symm
  have apc267:=fun (q200 q201 q202:G)=>by
    exact ((((cg (fun t => t ◇ q202) (cg (fun t => ((q200 ◇ q200) ◇ q200) ◇ t) (cg (fun t => t ◇ ((q200 ◇ q200) ◇ q200)) (apc47 q200 q201)))).trans (cg (fun t => t ◇ q202) (cg (fun t => ((q200 ◇ q200) ◇ q200) ◇ t) (apc31 q201 q200)))).trans (cg (fun t => t ◇ q202) (apc3 q201 q200 q200))).symm).trans ((((cg (fun t => t ◇ q202) (cg (fun t => ((q200 ◇ q200) ◇ q200) ◇ t) (cg (fun t => t ◇ ((q200 ◇ q200) ◇ q200)) (cg (fun t => t ◇ q201) (apc3 q200 q200 q200))))).symm).trans (apc266 q201 ((q200 ◇ q200) ◇ q200) q202)).trans ((cg (fun t => t ◇ q202) (apc3 q200 q200 q200)).trans (apc47 q200 q202)))
  have apc268:=fun (q203 q204:G)=>by
    exact (((cg (fun t => t ◇ q204) (apc267 q204 q203 ((q204 ◇ q203) ◇ q204))).symm).trans (apc186 ((q204 ◇ q203) ◇ q204) q204)).trans ((apc132 q204 (q204 ◇ q203)).trans (cg (fun t => t ◇ ((q204 ◇ q203) ◇ q204)) (apc267 q204 q203 q204)))
  have apc274:=fun (q14 q180 q15 q200 q201 q202:G)=>by
    exact (((apc267 q180 q14 (((q180 ◇ q180) ◇ q15) ◇ (q180 ◇ q14))).symm).trans (apc248 q14 q180 q15)).symm
  have apc275:=fun (q205 q206:G)=>by
    exact ((((cg (fun t => t ◇ q206) (apc185 (((q206 ◇ q206) ◇ q205) ◇ q206) q206)).trans (apc266 q205 q206 q206)).symm).trans (((cg (fun t => t ◇ q206) (cg (fun t => t ◇ (((q206 ◇ q206) ◇ q205) ◇ q206)) (cg (fun t => t ◇ q206) (apc266 q205 q206 (((q206 ◇ q206) ◇ q205) ◇ q206))))).symm).trans (apc214 (((q206 ◇ q206) ◇ q205) ◇ q206) q206))).symm
  have apc276:=fun (q207 q208:G)=>by
    exact (((((cg (fun t => (((q207 ◇ q207) ◇ q207) ◇ q207) ◇ t) (cg (fun t => t ◇ ((q207 ◇ q207) ◇ q207)) (cg (fun t => t ◇ q208) (apc3 q207 q207 q207)))).trans (cg (fun t => (((q207 ◇ q207) ◇ q207) ◇ q207) ◇ t) (cg (fun t => t ◇ ((q207 ◇ q207) ◇ q207)) (apc267 q207 q207 q208)))).trans (cg (fun t => (((q207 ◇ q207) ◇ q207) ◇ q207) ◇ t) (apc31 q208 q207))).trans (apc267 q207 q207 ((q207 ◇ q208) ◇ q207))).symm).trans ((((cg (fun t => t ◇ (((((q207 ◇ q207) ◇ q207) ◇ ((q207 ◇ q207) ◇ q207)) ◇ q208) ◇ ((q207 ◇ q207) ◇ q207))) (apc3 q207 q207 q207)).symm).trans (apc275 q208 ((q207 ◇ q207) ◇ q207))).trans (((cg (fun t => t ◇ ((q207 ◇ q207) ◇ q207)) (apc3 q207 q207 q207)).trans (apc77 q207 q207 q207)).trans (apc2 q207 q207 ((((q207 ◇ q207) ◇ q207) ◇ q207) ◇ q207))))
  have apc277:=fun (q203 q204 q207 q208:G)=>by
    exact (((cg (fun t => t ◇ q204) (apc276 q204 q203)).symm).trans (apc268 q203 q204)).symm
  have apc278:=fun (q209 q210:G)=>by
    exact ((((((cg (fun t => ((q210 ◇ q210) ◇ q210) ◇ t) (cg (fun t => t ◇ ((q210 ◇ q209) ◇ q210)) (cg (fun t => t ◇ ((q210 ◇ q209) ◇ q210)) (apc277 q209 q210 ((q210 ◇ q210) ◇ ((q210 ◇ q209) ◇ q210)) ((q210 ◇ q210) ◇ ((q210 ◇ q209) ◇ q210)))))).trans (cg (fun t => ((q210 ◇ q210) ◇ q210) ◇ t) (cg (fun t => t ◇ ((q210 ◇ q209) ◇ q210)) (apc3 q209 q210 q210)))).trans (cg (fun t => ((q210 ◇ q210) ◇ q210) ◇ t) (apc267 q210 q209 ((q210 ◇ q209) ◇ q210)))).trans (cg (fun t => ((q210 ◇ q210) ◇ q210) ◇ t) (apc276 q210 q209))).trans (apc105 q210 q210 q210)).symm).trans ((((cg (fun t => t ◇ ((((q210 ◇ q210) ◇ ((q210 ◇ q209) ◇ q210)) ◇ ((q210 ◇ q209) ◇ q210)) ◇ ((q210 ◇ q209) ◇ q210))) (apc277 q209 q210 q209 q209)).symm).trans (apc96 ((q210 ◇ q209) ◇ q210) (q210 ◇ q210))).trans ((cg (fun t => t ◇ ((q210 ◇ q209) ◇ q210)) (apc277 q209 q210 ((q210 ◇ q210) ◇ ((q210 ◇ q209) ◇ q210)) ((q210 ◇ q210) ◇ ((q210 ◇ q209) ◇ q210)))).trans (apc3 q209 q210 q210)))
  have apc279:=fun (q211 q212 q213:G)=>by
    exact ((((cg (fun t => t ◇ q213) (cg (fun t => t ◇ ((q212 ◇ q211) ◇ q212)) (apc267 q212 q212 ((q212 ◇ q211) ◇ q212)))).trans (cg (fun t => t ◇ q213) (cg (fun t => t ◇ ((q212 ◇ q211) ◇ q212)) (apc276 q212 q211)))).trans (cg (fun t => t ◇ q213) (apc277 q211 q212 ((q212 ◇ q212) ◇ ((q212 ◇ q211) ◇ q212)) ((q212 ◇ q212) ◇ ((q212 ◇ q211) ◇ q212))))).symm).trans (((cg (fun t => t ◇ q213) (cg (fun t => t ◇ ((q212 ◇ q211) ◇ q212)) (cg (fun t => t ◇ ((q212 ◇ q211) ◇ q212)) ((apc278 q211 q212).symm)))).symm).trans (apc267 ((q212 ◇ q211) ◇ q212) q212 q213))
  have apc287:=fun (q214 q215:G)=>by
    exact (((((cg (fun t => t ◇ q214) (cg (fun t => t ◇ (q214 ◇ q214)) (apc0 q214 q214))).trans (cg (fun t => t ◇ q214) (apc105 q214 q214 q214))).trans (apc2 q214 q214 ((((q214 ◇ q214) ◇ q214) ◇ q214) ◇ q214))).symm).trans (((apc279 q215 (q214 ◇ q214) q214).trans (apc274 q214 q214 q215 q214 q214 q214)).trans (cg (fun t => q214 ◇ t) (apc105 q214 q214 q215)))).symm
  have apc297:=fun (q216 q217 q218:G)=>by
    exact ((cg (fun t => t ◇ (((q218 ◇ q216) ◇ q218) ◇ (q218 ◇ q216))) (cg (fun t => t ◇ q217) (cg (fun t => t ◇ q217) (apc4 q216 q218)))).symm).trans ((h (((q218 ◇ q216) ◇ q218) ◇ (q218 ◇ q216)) q217 q218).symm)
  have apc298:=fun (q219 q220:G)=>by
    exact (((((cg (fun t => t ◇ (q220 ◇ (q220 ◇ q219))) (apc267 q220 q219 ((q220 ◇ q219) ◇ q220))).trans (cg (fun t => t ◇ (q220 ◇ (q220 ◇ q219))) (apc276 q220 q219))).trans (apc0 (q220 ◇ q219) q220)).symm).trans ((((cg (fun t => ((((q220 ◇ q219) ◇ q220) ◇ q220) ◇ ((q220 ◇ q219) ◇ q220)) ◇ t) (apc4 q219 q220)).symm).trans (apc3 (q220 ◇ q219) ((q220 ◇ q219) ◇ q220) q220)).trans (cg (fun t => t ◇ ((q220 ◇ q219) ◇ q220)) (apc4 q219 q220)))).symm
  have apc299:=fun (q221 q222:G)=>by
    exact (((((cg (fun t => t ◇ (((q222 ◇ q221) ◇ q222) ◇ (q222 ◇ q221))) (apc12 q221 q222)).trans (apc206 q222 (q222 ◇ q221) q222)).trans (apc267 q222 q221 (q222 ◇ q221))).symm).trans (((cg (fun t => t ◇ (((q222 ◇ q221) ◇ q222) ◇ (q222 ◇ q221))) (cg (fun t => t ◇ ((q222 ◇ q221) ◇ q222)) (apc298 q221 q222))).symm).trans (apc297 q221 ((q222 ◇ q221) ◇ q222) q222))).symm
  have apc300:=fun (q223 q224:G)=>by
    exact ((cg (fun t => t ◇ (q224 ◇ q223)) (apc299 q223 q224)).symm).trans (apc4 q224 (q224 ◇ q223))
  have apc302:=fun (q225 q226 q227:G)=>by
    exact ((cg (fun t => t ◇ q227) (apc298 q225 q226)).symm).trans (((cg (fun t => t ◇ q227) (cg (fun t => t ◇ ((q226 ◇ q225) ◇ q226)) (apc299 q225 q226))).symm).trans (apc267 ((q226 ◇ q225) ◇ q226) (q226 ◇ q225) q227))
  have apc337:=fun (q228 q229 q230:G)=>by
    exact ((cg (fun t => t ◇ q229) (apc300 q228 (q229 ◇ q230))).symm).trans ((h q229 ((q229 ◇ q230) ◇ q228) q230).symm)
  have apc338:=fun (q231 q232:G)=>by
    exact ((cg (fun t => ((q232 ◇ q231) ◇ ((q232 ◇ q231) ◇ q232)) ◇ t) (apc35 q231 q232)).symm).trans ((((cg (fun t => t ◇ ((q232 ◇ q231) ◇ (q232 ◇ q232))) (cg (fun t => (q232 ◇ q231) ◇ t) (apc35 q231 q232))).symm).trans (apc300 (q232 ◇ q232) (q232 ◇ q231))).trans ((cg (fun t => ((q232 ◇ q231) ◇ (q232 ◇ q232)) ◇ t) (cg (fun t => t ◇ (q232 ◇ q231)) (apc35 q231 q232))).trans (cg (fun t => t ◇ (((q232 ◇ q231) ◇ q232) ◇ (q232 ◇ q231))) (apc35 q231 q232))))
  have apc339:=fun (q233 q234:G)=>by
    exact ((((cg (fun t => ((((q234 ◇ q233) ◇ q234) ◇ (((q234 ◇ q233) ◇ q234) ◇ (q234 ◇ q233))) ◇ ((q234 ◇ q233) ◇ q234)) ◇ t) (apc299 q233 q234)).trans (apc302 (q234 ◇ q233) ((q234 ◇ q233) ◇ q234) (q234 ◇ (q234 ◇ q233)))).trans (cg (fun t => t ◇ (q234 ◇ (q234 ◇ q233))) (apc299 q233 q234))).symm).trans ((((cg (fun t => t ◇ ((((q234 ◇ q233) ◇ q234) ◇ (q234 ◇ q233)) ◇ ((q234 ◇ q233) ◇ q234))) (cg (fun t => t ◇ ((q234 ◇ q233) ◇ q234)) (apc338 q233 q234))).symm).trans (apc297 q234 ((q234 ◇ q233) ◇ q234) (q234 ◇ q233))).trans ((cg (fun t => t ◇ ((q234 ◇ q233) ◇ q234)) (apc299 q233 q234)).trans (apc298 q233 q234)))
  have apc340:=fun (q235 q236:G)=>by
    exact (((apc276 q236 (q236 ◇ q235)).symm).trans (((cg (fun t => q236 ◇ t) (apc339 q235 q236)).symm).trans (apc24 q236 (q236 ◇ q235)))).symm
  have apc342:=fun (q237 q238:G)=>by
    exact (((apc277 (q238 ◇ q237) q238 ((q238 ◇ q238) ◇ ((q238 ◇ (q238 ◇ q237)) ◇ q238)) ((q238 ◇ q238) ◇ ((q238 ◇ (q238 ◇ q237)) ◇ q238))).symm).trans (((cg (fun t => (q238 ◇ q238) ◇ t) (apc339 q237 q238)).symm).trans (apc36 (q238 ◇ q237) q238))).symm
  have apc345:=fun (q239 q240 q241:G)=>by
    exact (((((cg (fun t => t ◇ q240) (apc31 ((q240 ◇ q241) ◇ q239) (q240 ◇ q241))).trans (cg (fun t => t ◇ q240) (apc342 q239 (q240 ◇ q241)))).trans (apc26 ((((q240 ◇ q241) ◇ (q240 ◇ q241)) ◇ (q240 ◇ q241)) ◇ q240) ((((q240 ◇ q241) ◇ (q240 ◇ q241)) ◇ (q240 ◇ q241)) ◇ q240) q240 q241)).symm).trans (((cg (fun t => t ◇ q240) (cg (fun t => ((q240 ◇ q241) ◇ ((q240 ◇ q241) ◇ q239)) ◇ t) (apc342 q239 (q240 ◇ q241)))).symm).trans (apc337 ((q240 ◇ q241) ◇ q239) q240 q241))).symm
  have apc346:=fun (q242 q243:G)=>by
    exact (((apc96 q243 q242).symm).trans (((cg (fun t => (q242 ◇ q243) ◇ t) (apc138 q242 q243)).symm).trans (apc345 q243 (q242 ◇ q243) q243))).symm
  have apc347:=fun (q244 q245:G)=>by
    exact (((apc346 q244 q245).symm).trans (((cg (fun t => (q244 ◇ q245) ◇ t) (apc346 q244 q245)).symm).trans (apc340 q245 (q244 ◇ q245)))).symm
  have apc348:=fun (q246 q247:G)=>by
    exact ((((cg (fun t => (q247 ◇ q246) ◇ t) (apc2 q247 q246 ((((q247 ◇ q247) ◇ q246) ◇ q246) ◇ q247))).trans (apc347 q247 q246)).symm).trans ((((cg (fun t => t ◇ ((((q247 ◇ q247) ◇ q246) ◇ q246) ◇ q247)) (apc2 q247 q246 q246)).symm).trans (apc347 (((q247 ◇ q247) ◇ q246) ◇ q246) q247)).trans (cg (fun t => t ◇ q247) (apc2 q247 q246 ((((q247 ◇ q247) ◇ q246) ◇ q246) ◇ q247))))).symm
  have apc349:=fun (q248 q249:G)=>by
    exact ((apc2 q248 q249 ((((q248 ◇ q248) ◇ q249) ◇ q249) ◇ q248)).symm).trans ((((cg (fun t => t ◇ q248) (apc348 q249 (q248 ◇ q248))).symm).trans (apc274 q248 q248 q249 q248 q248 q248)).trans ((cg (fun t => q248 ◇ t) (apc105 q248 q248 q249)).trans (apc287 q248 q249)))
  exact (apc349 x x).trans ((apc349 x ((y ◇ y) ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_53228_to_3465 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_53228_to_3465
