-- Equation40762 → Equation60891
-- Recorded verdict: true
-- Premise: x = ((((x * y) * y) * z) * x) * y
-- Conclusion: (x * x) * y = (x * (y * z)) * x
-- Original submission SHA-256: cd07d0af6effbe8d68b50453dc9912e7f772436fc95309ad44c7056ed77c9329
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((((x ◇ y) ◇ y) ◇ z) ◇ x) ◇ y
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ x) ◇ y = (x ◇ (y ◇ z)) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a=b → f a=f b:=by
    intro f a b p
    exact congrArg f p
  have apc0:=fun (q0 q1:G)=>by
    exact ((cg (fun t => t ◇ q0) (cg (fun t => t ◇ ((q0 ◇ q1) ◇ q1)) ((h q0 q1 q0).symm))).symm).trans ((h ((q0 ◇ q1) ◇ q1) q0 q1).symm)
  have apc3:=fun (q2 q0 q1:G)=>by
    exact ((cg (fun t => t ◇ q0) (cg (fun t => t ◇ (((q0 ◇ q0) ◇ q0) ◇ q2)) (cg (fun t => t ◇ q1) ((h q0 q0 q2).symm)))).symm).trans ((h (((q0 ◇ q0) ◇ q0) ◇ q2) q0 q1).symm)
  have apc4:=fun (q3 q4:G)=>by
    exact ((cg (fun t => t ◇ (((q4 ◇ q4) ◇ q4) ◇ q3)) (cg (fun t => t ◇ q4) (apc3 q3 q4 (((q4 ◇ q4) ◇ q4) ◇ q3)))).symm).trans ((h q4 (((q4 ◇ q4) ◇ q4) ◇ q3) q4).symm)
  have apc5:=fun (q5 q2 q0 q1:G)=>by
    exact ((cg (fun t => t ◇ q0) (cg (fun t => t ◇ ((((q5 ◇ q0) ◇ q0) ◇ q2) ◇ q5)) (cg (fun t => t ◇ q1) (cg (fun t => t ◇ q0) ((h q5 q0 q2).symm))))).symm).trans ((h ((((q5 ◇ q0) ◇ q0) ◇ q2) ◇ q5) q0 q1).symm)
  have apc6:=fun (q6 q7:G)=>by
    exact ((cg (fun t => t ◇ q7) (apc5 q7 q6 q7 q7)).symm).trans ((h q7 q7 ((((q7 ◇ q7) ◇ q7) ◇ q6) ◇ q7)).symm)
  have apc8:=fun (q8 q9 q10:G)=>by
    exact ((cg (fun t => t ◇ q10) (cg (fun t => q10 ◇ t) (cg (fun t => t ◇ (((q10 ◇ q10) ◇ q10) ◇ q8)) (cg (fun t => t ◇ q9) (apc6 q8 q10))))).symm).trans ((((cg (fun t => t ◇ q10) (cg (fun t => t ◇ (((((((q10 ◇ q10) ◇ q10) ◇ q8) ◇ q10) ◇ q10) ◇ q9) ◇ (((q10 ◇ q10) ◇ q10) ◇ q8))) (apc6 q8 q10))).symm).trans (apc5 (((q10 ◇ q10) ◇ q10) ◇ q8) q9 q10 q10)).trans (cg (fun t => t ◇ (((q10 ◇ q10) ◇ q10) ◇ q8)) (cg (fun t => t ◇ q9) (apc6 q8 q10))))
  have apc9:=fun (q11 q12 q13:G)=>by
    exact ((cg (fun t => t ◇ q12) (cg (fun t => t ◇ (q12 ◇ ((q12 ◇ q11) ◇ q11))) (cg (fun t => t ◇ q13) (cg (fun t => t ◇ q12) (apc0 q12 q11))))).symm).trans ((h (q12 ◇ ((q12 ◇ q11) ◇ q11)) q12 q13).symm)
  have apc10:=fun (q14 q15:G)=>by
    exact (((apc9 q14 q15 q14).symm).trans (((cg (fun t => t ◇ q15) (cg (fun t => ((((q15 ◇ q14) ◇ q14) ◇ q15) ◇ q14) ◇ t) (cg (fun t => t ◇ ((q15 ◇ q14) ◇ q14)) ((h q15 q14 q15).symm)))).symm).trans (apc5 ((q15 ◇ q14) ◇ q14) q14 q15 q14))).symm
  have apc11:=fun (q16 q6 q17:G)=>by
    exact ((cg (fun t => t ◇ ((((q16 ◇ q17) ◇ q17) ◇ q6) ◇ q16)) (cg (fun t => t ◇ (q16 ◇ q17)) (apc5 q16 q6 q17 ((((q16 ◇ q17) ◇ q17) ◇ q6) ◇ q16)))).symm).trans ((h (q16 ◇ q17) ((((q16 ◇ q17) ◇ q17) ◇ q6) ◇ q16) q17).symm)
  have apc14:=fun (q8 q9 q18 q10:G)=>by
    exact ((cg (fun t => t ◇ q18) (cg (fun t => (q18 ◇ q10) ◇ t) (cg (fun t => t ◇ ((((q18 ◇ q18) ◇ q18) ◇ q8) ◇ q18)) (cg (fun t => t ◇ q9) (cg (fun t => t ◇ q18) (apc6 q8 q18)))))).symm).trans ((((cg (fun t => t ◇ q18) (cg (fun t => t ◇ ((((((((q18 ◇ q18) ◇ q18) ◇ q8) ◇ q18) ◇ q18) ◇ q18) ◇ q9) ◇ ((((q18 ◇ q18) ◇ q18) ◇ q8) ◇ q18))) (cg (fun t => t ◇ q10) (apc6 q8 q18)))).symm).trans (apc5 ((((q18 ◇ q18) ◇ q18) ◇ q8) ◇ q18) q9 q18 q10)).trans (cg (fun t => t ◇ ((((q18 ◇ q18) ◇ q18) ◇ q8) ◇ q18)) (cg (fun t => t ◇ q9) (cg (fun t => t ◇ q18) (apc6 q8 q18)))))
  have apc17:=fun (q19 q20 q21:G)=>by
    exact (((apc11 q19 q20 q21).symm).trans (((cg (fun t => t ◇ ((((q19 ◇ q21) ◇ q21) ◇ q20) ◇ q19)) (cg (fun t => ((((q19 ◇ q21) ◇ q21) ◇ q20) ◇ q19) ◇ t) (cg (fun t => t ◇ q21) ((h q19 q21 q20).symm)))).symm).trans (apc0 ((((q19 ◇ q21) ◇ q21) ◇ q20) ◇ q19) q21))).symm
  have apc19:=fun (q22 q23 q24 q25:G)=>by
    exact ((cg (fun t => t ◇ q24) (cg (fun t => t ◇ (((((q22 ◇ q24) ◇ q24) ◇ q23) ◇ q22) ◇ q24)) (cg (fun t => t ◇ q25) (cg (fun t => t ◇ q24) (apc17 q22 q23 q24))))).symm).trans ((h (((((q22 ◇ q24) ◇ q24) ◇ q23) ◇ q22) ◇ q24) q24 q25).symm)
  have apc20:=fun (q26 q27 q28 q29:G)=>by
    exact ((cg (fun t => t ◇ q28) (cg (fun t => (((q26 ◇ q28) ◇ q28) ◇ q29) ◇ t) ((h q26 q28 q27).symm))).symm).trans (apc19 q26 q27 q28 q29)
  have apc21:=fun (q26 q27 q28 q29:G)=>by
    exact ((apc20 q26 q27 q28 q26).symm).trans (apc20 q26 q26 q28 q26)
  have apc22:=fun (x y z q26 q27 q28 q29:G)=>by
    exact ((h x y x).trans (apc21 x x y (((((x ◇ y) ◇ y) ◇ x) ◇ x) ◇ y))).symm
  have apc23:=fun (q30 q31 q32:G)=>by
    exact ((cg (fun t => t ◇ ((q32 ◇ q31) ◇ q31)) (apc20 q32 q30 q31 q32)).symm).trans (apc10 q31 q32)
  have apc25:=fun (q33 q34 q35 q36:G)=>by
    exact ((cg (fun t => t ◇ q36) (cg (fun t => t ◇ ((((((((q33 ◇ q36) ◇ q36) ◇ q34) ◇ q33) ◇ q36) ◇ q36) ◇ q35) ◇ ((((q33 ◇ q36) ◇ q36) ◇ q34) ◇ q33))) (apc17 q33 q34 q36))).symm).trans (apc5 ((((q33 ◇ q36) ◇ q36) ◇ q34) ◇ q33) q35 q36 q36)
  have apc26:=fun (q22 q23 q24 q25:G)=>by
    exact (apc19 q22 q23 q24 q25).trans ((apc19 q22 q23 q24 q22).symm)
  have apc27:=fun (q37 q38 q39 q40:G)=>by
    exact (((cg (fun t => t ◇ q39) (cg (fun t => (((q37 ◇ q39) ◇ q39) ◇ q40) ◇ t) ((h q37 q39 q38).symm))).symm).trans (apc26 q37 q38 q39 q40)).symm
  have apc28:=fun (q41 q42 q43:G)=>by
    exact (apc27 q42 q41 q43 q41).trans ((h q42 q43 q41).symm)
  have apc29:=fun (q22 q23 q24 q25 q41 q42 q43:G)=>by
    exact (apc26 q22 q23 q24 q25).trans (apc28 q23 q22 q24)
  have apc30:=fun (q44 q45 q46:G)=>by
    exact ((cg (fun t => t ◇ (((((q44 ◇ q46) ◇ q46) ◇ q45) ◇ q44) ◇ q46)) (cg (fun t => t ◇ ((q44 ◇ q46) ◇ q46)) (apc29 q44 q45 q46 (((((q44 ◇ q46) ◇ q46) ◇ q45) ◇ q44) ◇ q46) q44 q44 q44))).symm).trans ((h ((q44 ◇ q46) ◇ q46) (((((q44 ◇ q46) ◇ q46) ◇ q45) ◇ q44) ◇ q46) q46).symm)
  have apc32:=fun (q47 q48 q49 q50:G)=>by
    exact ((cg (fun t => t ◇ q49) (cg (fun t => (q47 ◇ q50) ◇ t) (cg (fun t => t ◇ ((((q47 ◇ q49) ◇ q49) ◇ q47) ◇ q47)) (cg (fun t => t ◇ q48) (cg (fun t => t ◇ q49) (apc22 q47 q49 (((((q47 ◇ q49) ◇ q49) ◇ q47) ◇ q47) ◇ q49) (((((q47 ◇ q49) ◇ q49) ◇ q47) ◇ q47) ◇ q49) (((((q47 ◇ q49) ◇ q49) ◇ q47) ◇ q47) ◇ q49) (((((q47 ◇ q49) ◇ q49) ◇ q47) ◇ q47) ◇ q49) (((((q47 ◇ q49) ◇ q49) ◇ q47) ◇ q47) ◇ q49))))))).symm).trans ((((cg (fun t => t ◇ q49) (cg (fun t => t ◇ ((((((((q47 ◇ q49) ◇ q49) ◇ q47) ◇ q47) ◇ q49) ◇ q49) ◇ q48) ◇ ((((q47 ◇ q49) ◇ q49) ◇ q47) ◇ q47))) (cg (fun t => t ◇ q50) (apc22 q47 q49 q47 q47 q47 q47 q47)))).symm).trans (apc5 ((((q47 ◇ q49) ◇ q49) ◇ q47) ◇ q47) q48 q49 q50)).trans (cg (fun t => t ◇ ((((q47 ◇ q49) ◇ q49) ◇ q47) ◇ q47)) (cg (fun t => t ◇ q48) (cg (fun t => t ◇ q49) (apc22 q47 q49 (((((q47 ◇ q49) ◇ q49) ◇ q47) ◇ q47) ◇ q49) (((((q47 ◇ q49) ◇ q49) ◇ q47) ◇ q47) ◇ q49) (((((q47 ◇ q49) ◇ q49) ◇ q47) ◇ q47) ◇ q49) (((((q47 ◇ q49) ◇ q49) ◇ q47) ◇ q47) ◇ q49) (((((q47 ◇ q49) ◇ q49) ◇ q47) ◇ q47) ◇ q49))))))
  have apc37:=fun (q51 q52 q53:G)=>by
    exact ((cg (fun t => t ◇ q53) (apc32 (q52 ◇ q53) q51 q52 q53)).symm).trans ((h q52 q53 ((((q52 ◇ q53) ◇ q52) ◇ q51) ◇ (((((q52 ◇ q53) ◇ q52) ◇ q52) ◇ (q52 ◇ q53)) ◇ (q52 ◇ q53)))).symm)
  have apc39:=fun (q54 q55 q56 q57:G)=>by
    exact (((((cg (fun t => t ◇ q57) (cg (fun t => q57 ◇ t) (cg (fun t => t ◇ ((((((((q57 ◇ q57) ◇ q57) ◇ q54) ◇ q57) ◇ q57) ◇ q57) ◇ q55) ◇ ((((q57 ◇ q57) ◇ q57) ◇ q54) ◇ q57))) (cg (fun t => t ◇ q56) (cg (fun t => t ◇ q57) (cg (fun t => t ◇ q57) (cg (fun t => t ◇ ((((q57 ◇ q57) ◇ q57) ◇ q54) ◇ q57)) (cg (fun t => t ◇ q55) (cg (fun t => t ◇ q57) (apc6 q54 q57)))))))))).trans (cg (fun t => t ◇ q57) (cg (fun t => q57 ◇ t) (cg (fun t => ((((((q57 ◇ q57) ◇ q55) ◇ ((((q57 ◇ q57) ◇ q57) ◇ q54) ◇ q57)) ◇ q57) ◇ q57) ◇ q56) ◇ t) (cg (fun t => t ◇ ((((q57 ◇ q57) ◇ q57) ◇ q54) ◇ q57)) (cg (fun t => t ◇ q55) (cg (fun t => t ◇ q57) (apc6 q54 q57)))))))).trans (cg (fun t => t ◇ q57) (cg (fun t => q57 ◇ t) (cg (fun t => t ◇ (((q57 ◇ q57) ◇ q55) ◇ ((((q57 ◇ q57) ◇ q57) ◇ q54) ◇ q57))) (cg (fun t => t ◇ q56) (cg (fun t => t ◇ q57) (apc5 q57 q54 q57 q55))))))).trans (cg (fun t => t ◇ q57) (cg (fun t => q57 ◇ t) (cg (fun t => t ◇ (((q57 ◇ q57) ◇ q55) ◇ ((((q57 ◇ q57) ◇ q57) ◇ q54) ◇ q57))) (cg (fun t => t ◇ q56) (apc6 q54 q57)))))).symm).trans ((((cg (fun t => t ◇ q57) (cg (fun t => t ◇ ((((((((((((q57 ◇ q57) ◇ q57) ◇ q54) ◇ q57) ◇ q57) ◇ q57) ◇ q55) ◇ ((((q57 ◇ q57) ◇ q57) ◇ q54) ◇ q57)) ◇ q57) ◇ q57) ◇ q56) ◇ ((((((((q57 ◇ q57) ◇ q57) ◇ q54) ◇ q57) ◇ q57) ◇ q57) ◇ q55) ◇ ((((q57 ◇ q57) ◇ q57) ◇ q54) ◇ q57)))) (apc6 q54 q57))).symm).trans (apc25 ((((q57 ◇ q57) ◇ q57) ◇ q54) ◇ q57) q55 q56 q57)).trans ((((cg (fun t => t ◇ ((((((((q57 ◇ q57) ◇ q57) ◇ q54) ◇ q57) ◇ q57) ◇ q57) ◇ q55) ◇ ((((q57 ◇ q57) ◇ q57) ◇ q54) ◇ q57))) (cg (fun t => t ◇ q56) (cg (fun t => t ◇ q57) (cg (fun t => t ◇ q57) (cg (fun t => t ◇ ((((q57 ◇ q57) ◇ q57) ◇ q54) ◇ q57)) (cg (fun t => t ◇ q55) (cg (fun t => t ◇ q57) (apc6 q54 q57)))))))).trans (cg (fun t => ((((((q57 ◇ q57) ◇ q55) ◇ ((((q57 ◇ q57) ◇ q57) ◇ q54) ◇ q57)) ◇ q57) ◇ q57) ◇ q56) ◇ t) (cg (fun t => t ◇ ((((q57 ◇ q57) ◇ q57) ◇ q54) ◇ q57)) (cg (fun t => t ◇ q55) (cg (fun t => t ◇ q57) (apc6 q54 q57)))))).trans (cg (fun t => t ◇ (((q57 ◇ q57) ◇ q55) ◇ ((((q57 ◇ q57) ◇ q57) ◇ q54) ◇ q57))) (cg (fun t => t ◇ q56) (cg (fun t => t ◇ q57) (apc5 q57 q54 q57 q55))))).trans (cg (fun t => t ◇ (((q57 ◇ q57) ◇ q55) ◇ ((((q57 ◇ q57) ◇ q57) ◇ q54) ◇ q57))) (cg (fun t => t ◇ q56) (apc6 q54 q57)))))
  have apc46:=fun (q58 q59 q60:G)=>by
    exact ((((cg (fun t => t ◇ (((((q58 ◇ q60) ◇ q60) ◇ q59) ◇ q58) ◇ q60)) (apc23 q59 q60 q58)).trans (apc30 q58 q59 q60)).symm).trans (((cg (fun t => t ◇ (((((q58 ◇ q60) ◇ q60) ◇ q59) ◇ q58) ◇ q60)) (cg (fun t => (((((q58 ◇ q60) ◇ q60) ◇ q59) ◇ q58) ◇ q60) ◇ t) (cg (fun t => t ◇ q60) (apc17 q58 q59 q60)))).symm).trans (apc0 (((((q58 ◇ q60) ◇ q60) ◇ q59) ◇ q58) ◇ q60) q60))).symm
  have apc47:=fun (q61 q62 q63:G)=>by
    exact (((cg (fun t => t ◇ q63) (cg (fun t => (q61 ◇ q63) ◇ t) (cg (fun t => t ◇ ((((q61 ◇ q63) ◇ q63) ◇ q62) ◇ q61)) (apc46 q61 q62 q63)))).symm).trans (apc25 q61 q62 q63 q63)).trans (cg (fun t => t ◇ ((((q61 ◇ q63) ◇ q63) ◇ q62) ◇ q61)) (apc46 q61 q62 q63))
  have apc48:=fun (q64 q65:G)=>by
    exact ((apc5 (q65 ◇ q65) q64 q65 q65).symm).trans (((cg (fun t => t ◇ q65) (apc47 (q65 ◇ q65) q64 q65)).symm).trans ((h q65 q65 ((((q65 ◇ q65) ◇ q65) ◇ q65) ◇ (((((q65 ◇ q65) ◇ q65) ◇ q65) ◇ q64) ◇ (q65 ◇ q65)))).symm))
  have apc49:=fun (q66:G)=>by
    exact ((cg (fun t => t ◇ ((((q66 ◇ q66) ◇ q66) ◇ q66) ◇ q66)) (apc48 q66 q66)).symm).trans (apc11 q66 q66 q66)
  have apc52:=fun (q67 q68:G)=>by
    exact (((((cg (fun t => t ◇ ((((q68 ◇ q68) ◇ q68) ◇ q68) ◇ q68)) (cg (fun t => (((q68 ◇ q68) ◇ q68) ◇ q67) ◇ t) (cg (fun t => t ◇ (q68 ◇ ((((q68 ◇ q68) ◇ q68) ◇ q68) ◇ q68))) (cg (fun t => t ◇ (q68 ◇ ((((q68 ◇ q68) ◇ q68) ◇ q68) ◇ q68))) (cg (fun t => t ◇ q68) (cg (fun t => t ◇ q68) (apc49 q68))))))).trans (cg (fun t => t ◇ ((((q68 ◇ q68) ◇ q68) ◇ q68) ◇ q68)) (cg (fun t => (((q68 ◇ q68) ◇ q68) ◇ q67) ◇ t) (cg (fun t => t ◇ (q68 ◇ ((((q68 ◇ q68) ◇ q68) ◇ q68) ◇ q68))) (cg (fun t => (((q68 ◇ q68) ◇ q68) ◇ q68) ◇ t) (apc49 q68)))))).trans (cg (fun t => t ◇ ((((q68 ◇ q68) ◇ q68) ◇ q68) ◇ q68)) (cg (fun t => (((q68 ◇ q68) ◇ q68) ◇ q67) ◇ t) (cg (fun t => ((((q68 ◇ q68) ◇ q68) ◇ q68) ◇ (q68 ◇ q68)) ◇ t) (apc49 q68))))).trans (cg (fun t => t ◇ ((((q68 ◇ q68) ◇ q68) ◇ q68) ◇ q68)) (cg (fun t => (((q68 ◇ q68) ◇ q68) ◇ q67) ◇ t) (apc48 (q68 ◇ q68) q68)))).symm).trans (((cg (fun t => t ◇ ((((q68 ◇ q68) ◇ q68) ◇ q68) ◇ q68)) (cg (fun t => t ◇ (((((q68 ◇ ((((q68 ◇ q68) ◇ q68) ◇ q68) ◇ q68)) ◇ q68) ◇ q68) ◇ (q68 ◇ ((((q68 ◇ q68) ◇ q68) ◇ q68) ◇ q68))) ◇ (q68 ◇ ((((q68 ◇ q68) ◇ q68) ◇ q68) ◇ q68)))) (cg (fun t => t ◇ q67) (cg (fun t => t ◇ q68) (apc49 q68))))).symm).trans (apc37 q67 q68 ((((q68 ◇ q68) ◇ q68) ◇ q68) ◇ q68)))
  have apc53:=fun (q69 q70:G)=>by
    exact (((cg (fun t => t ◇ (((((q69 ◇ q69) ◇ q69) ◇ q69) ◇ q69) ◇ ((((q69 ◇ q69) ◇ q69) ◇ q69) ◇ q69))) (cg (fun t => t ◇ q70) (cg (fun t => t ◇ ((((q69 ◇ q69) ◇ q69) ◇ q69) ◇ q69)) (apc49 q69)))).trans (cg (fun t => (((q69 ◇ q69) ◇ ((((q69 ◇ q69) ◇ q69) ◇ q69) ◇ q69)) ◇ q70) ◇ t) (apc52 q69 q69))).symm).trans (((cg (fun t => t ◇ (((((q69 ◇ q69) ◇ q69) ◇ q69) ◇ q69) ◇ ((((q69 ◇ q69) ◇ q69) ◇ q69) ◇ q69))) (cg (fun t => t ◇ q70) (cg (fun t => t ◇ ((((q69 ◇ q69) ◇ q69) ◇ q69) ◇ q69)) (cg (fun t => t ◇ ((((q69 ◇ q69) ◇ q69) ◇ q69) ◇ q69)) (apc52 q69 q69))))).symm).trans (apc48 q70 ((((q69 ◇ q69) ◇ q69) ◇ q69) ◇ q69)))
  have apc54:=fun (q71 q72:G)=>by
    exact ((apc53 q72 ((((q72 ◇ q72) ◇ q72) ◇ q71) ◇ q72)).symm).trans (apc5 q72 q71 q72 ((((q72 ◇ q72) ◇ q72) ◇ q72) ◇ q72))
  have apc55:=fun (q73 q74 q75:G)=>by
    exact (((apc54 q73 q75).symm).trans (apc54 q74 q75)).symm
  have apc56:=fun (q76 q77:G)=>by
    exact ((cg (fun t => q77 ◇ t) (apc54 q76 q77)).symm).trans (apc49 q77)
  have apc61:=fun (q78 q79 q80:G)=>by
    exact ((cg (fun t => t ◇ (((q80 ◇ q80) ◇ q80) ◇ q79)) (apc55 q78 q79 q80)).symm).trans (apc4 q79 q80)
  have apc65:=fun (q81 q82 q83:G)=>by
    exact ((cg (fun t => ((((q83 ◇ q83) ◇ q83) ◇ q82) ◇ q83) ◇ t) (apc54 q81 q83)).symm).trans (apc52 q82 q83)
  have apc66:=fun (q84 q85 q86:G)=>by
    exact ((cg (fun t => t ◇ q85) (cg (fun t => t ◇ q86) (cg (fun t => (q85 ◇ q85) ◇ t) (apc54 q84 q85)))).symm).trans (apc53 q85 q86)
  have apc67:=fun (q87 q88 q89:G)=>by
    exact ((cg (fun t => t ◇ ((((q87 ◇ q87) ◇ q87) ◇ q87) ◇ q87)) (cg (fun t => t ◇ q89) (apc56 q87 q87))).symm).trans ((((cg (fun t => t ◇ ((((q87 ◇ q87) ◇ q87) ◇ q87) ◇ q87)) (cg (fun t => t ◇ q89) (cg (fun t => t ◇ ((((q87 ◇ q87) ◇ q87) ◇ q87) ◇ q87)) (apc52 q87 q87)))).symm).trans (apc55 q88 q89 ((((q87 ◇ q87) ◇ q87) ◇ q87) ◇ q87))).trans ((cg (fun t => t ◇ ((((q87 ◇ q87) ◇ q87) ◇ q87) ◇ q87)) (cg (fun t => t ◇ q88) (cg (fun t => t ◇ ((((q87 ◇ q87) ◇ q87) ◇ q87) ◇ q87)) (apc65 q87 q87 q87)))).trans (cg (fun t => t ◇ ((((q87 ◇ q87) ◇ q87) ◇ q87) ◇ q87)) (cg (fun t => t ◇ q88) (apc56 q87 q87)))))
  have apc70:=fun (q90 q91 q92 q93:G)=>by
    exact ((cg (fun t => t ◇ ((((q91 ◇ q91) ◇ q91) ◇ q90) ◇ q91)) (cg (fun t => t ◇ q93) (apc56 q90 q91))).symm).trans ((((cg (fun t => t ◇ ((((q91 ◇ q91) ◇ q91) ◇ q90) ◇ q91)) (cg (fun t => t ◇ q93) (cg (fun t => t ◇ ((((q91 ◇ q91) ◇ q91) ◇ q90) ◇ q91)) (apc65 q90 q90 q91)))).symm).trans (apc55 q92 q93 ((((q91 ◇ q91) ◇ q91) ◇ q90) ◇ q91))).trans ((cg (fun t => t ◇ ((((q91 ◇ q91) ◇ q91) ◇ q90) ◇ q91)) (cg (fun t => t ◇ q92) (cg (fun t => t ◇ ((((q91 ◇ q91) ◇ q91) ◇ q90) ◇ q91)) (apc65 q90 q90 q91)))).trans (cg (fun t => t ◇ ((((q91 ◇ q91) ◇ q91) ◇ q90) ◇ q91)) (cg (fun t => t ◇ q92) (apc56 q90 q91)))))
  have apc73:=fun (q87 q88 q89:G)=>by
    exact ((apc67 q87 q88 q87).symm).trans (apc67 q87 q87 q87)
  have apc74:=fun (q94 q95 q96:G)=>by
    exact (((cg (fun t => ((q95 ◇ q95) ◇ q96) ◇ t) (apc54 q94 q95)).symm).trans (apc67 q95 q94 q96)).trans (apc73 q95 q94 (((q95 ◇ q95) ◇ q94) ◇ ((((q95 ◇ q95) ◇ q95) ◇ q95) ◇ q95)))
  have apc77:=fun (q97 q98 q99:G)=>by
    exact (((apc14 q97 q98 q99 q97).symm).trans (((cg (fun t => t ◇ q99) (cg (fun t => (q99 ◇ q97) ◇ t) (apc70 q97 q99 q98 q99))).symm).trans (apc3 ((((q99 ◇ q99) ◇ q99) ◇ q97) ◇ q99) q99 q97))).symm
  have apc84:=fun (q97 q98 q99:G)=>by
    exact ((apc77 q97 q98 q99).symm).trans (apc77 q97 q97 q99)
  have apc91:=fun (q100 q101:G)=>by
    exact (((cg (fun t => t ◇ ((((q101 ◇ q101) ◇ q101) ◇ q101) ◇ q100)) (cg (fun t => ((((q101 ◇ q101) ◇ q101) ◇ q101) ◇ q100) ◇ t) (cg (fun t => t ◇ (q101 ◇ q101)) (apc48 q100 q101)))).symm).trans (apc0 ((((q101 ◇ q101) ◇ q101) ◇ q101) ◇ q100) (q101 ◇ q101))).trans (cg (fun t => t ◇ (q101 ◇ q101)) (apc48 q100 q101))
  have apc98:=fun (q102 q103 q104 q105:G)=>by
    exact ((cg (fun t => t ◇ q104) (cg (fun t => t ◇ ((((((q102 ◇ q104) ◇ q104) ◇ q103) ◇ q102) ◇ q104) ◇ q104)) (cg (fun t => t ◇ q105) (cg (fun t => t ◇ q104) (apc46 q102 q103 q104))))).symm).trans ((h ((((((q102 ◇ q104) ◇ q104) ◇ q103) ◇ q102) ◇ q104) ◇ q104) q104 q105).symm)
  have apc102:=fun (q106 q107 q108:G)=>by
    exact ((cg (fun t => t ◇ q107) (cg (fun t => q107 ◇ t) (cg (fun t => (q107 ◇ q108) ◇ t) (apc84 q106 q106 q107)))).symm).trans ((((cg (fun t => t ◇ q107) (cg (fun t => q107 ◇ t) (cg (fun t => (q107 ◇ q108) ◇ t) (cg (fun t => ((q107 ◇ q107) ◇ q106) ◇ t) (apc54 q106 q107))))).symm).trans (apc39 q107 q106 q108 q107)).trans (cg (fun t => (q107 ◇ q108) ◇ t) (apc84 q107 q106 q107)))
  have apc104:=fun (q109 q110 q111:G)=>by
    exact (((cg (fun t => t ◇ q111) (cg (fun t => q111 ◇ t) (cg (fun t => (q111 ◇ q110) ◇ t) (apc84 q109 q109 q111)))).trans (apc102 q109 q111 q110)).symm).trans ((((cg (fun t => t ◇ q111) (cg (fun t => q111 ◇ t) (cg (fun t => (q111 ◇ q110) ◇ t) (cg (fun t => ((q111 ◇ q111) ◇ q109) ◇ t) (apc55 q109 q109 q111))))).symm).trans (apc39 q109 q109 q110 q111)).trans (cg (fun t => (q111 ◇ q110) ◇ t) (apc84 q109 q109 q111)))
  have apc108:=fun (q112 q113 q114 q115:G)=>by
    exact (((((cg (fun t => t ◇ q115) (cg (fun t => t ◇ (((((q112 ◇ q115) ◇ q114) ◇ ((((q112 ◇ q115) ◇ q115) ◇ q113) ◇ q112)) ◇ q115) ◇ q115)) (cg (fun t => t ◇ q112) (apc46 q112 q113 q115)))).trans (cg (fun t => t ◇ q115) (cg (fun t => (((q112 ◇ q115) ◇ q115) ◇ q112) ◇ t) (cg (fun t => t ◇ q115) (apc5 q112 q113 q115 q114))))).trans (apc29 q112 q113 q115 q112 (((((q112 ◇ q115) ◇ q115) ◇ q112) ◇ (((((q112 ◇ q115) ◇ q115) ◇ q113) ◇ q112) ◇ q115)) ◇ q115) (((((q112 ◇ q115) ◇ q115) ◇ q112) ◇ (((((q112 ◇ q115) ◇ q115) ◇ q113) ◇ q112) ◇ q115)) ◇ q115) (((((q112 ◇ q115) ◇ q115) ◇ q112) ◇ (((((q112 ◇ q115) ◇ q115) ◇ q113) ◇ q112) ◇ q115)) ◇ q115))).symm).trans (((cg (fun t => t ◇ q115) (cg (fun t => ((((((((q112 ◇ q115) ◇ q115) ◇ q113) ◇ q112) ◇ q115) ◇ q115) ◇ q115) ◇ q112) ◇ t) (cg (fun t => t ◇ q115) (cg (fun t => t ◇ q115) (cg (fun t => t ◇ ((((q112 ◇ q115) ◇ q115) ◇ q113) ◇ q112)) (cg (fun t => t ◇ q114) (cg (fun t => t ◇ q115) ((h q112 q115 q113).symm)))))))).symm).trans (apc98 ((((q112 ◇ q115) ◇ q115) ◇ q113) ◇ q112) q114 q115 q112))).symm
  have apc109:=fun (q116 q117 q118 q119 q120:G)=>by
    exact ((cg (fun t => t ◇ q120) (cg (fun t => t ◇ q120) (cg (fun t => t ◇ (((q116 ◇ q120) ◇ q118) ◇ ((((q116 ◇ q120) ◇ q120) ◇ q117) ◇ q116))) (cg (fun t => t ◇ q119) (apc108 q116 q117 q118 q120))))).symm).trans (((cg (fun t => t ◇ q120) (cg (fun t => t ◇ q120) (cg (fun t => (((((((((((q116 ◇ q120) ◇ q120) ◇ q117) ◇ q116) ◇ q120) ◇ q120) ◇ q118) ◇ ((((q116 ◇ q120) ◇ q120) ◇ q117) ◇ q116)) ◇ q120) ◇ q120) ◇ q119) ◇ t) (cg (fun t => t ◇ ((((q116 ◇ q120) ◇ q120) ◇ q117) ◇ q116)) (cg (fun t => t ◇ q118) (cg (fun t => t ◇ q120) ((h q116 q120 q117).symm))))))).symm).trans (apc108 ((((q116 ◇ q120) ◇ q120) ◇ q117) ◇ q116) q118 q119 q120))
  have apc110:=fun (q121 q122:G)=>by
    exact (((cg (fun t => t ◇ (q122 ◇ q122)) (apc48 (((((q122 ◇ q122) ◇ q122) ◇ (q122 ◇ q122)) ◇ q121) ◇ ((((((q122 ◇ q122) ◇ q122) ◇ (q122 ◇ q122)) ◇ (q122 ◇ q122)) ◇ q121) ◇ ((q122 ◇ q122) ◇ q122))) q122)).symm).trans (apc109 ((q122 ◇ q122) ◇ q122) q121 q121 q122 (q122 ◇ q122))).symm
  have apc111:=fun (q123:G)=>by
    exact ((cg (fun t => t ◇ (q123 ◇ q123)) (apc110 q123 q123)).symm).trans ((h ((q123 ◇ q123) ◇ q123) (q123 ◇ q123) q123).symm)
  have apc125:=fun (q124 q125 q126 q127:G)=>by
    exact ((((cg (fun t => (q125 ◇ q127) ◇ t) (cg (fun t => t ◇ ((((q125 ◇ q125) ◇ q125) ◇ q124) ◇ q125)) (cg (fun t => t ◇ q124) (cg (fun t => t ◇ ((((q125 ◇ q125) ◇ q125) ◇ q124) ◇ q125)) (apc65 q124 q124 q125))))).trans (cg (fun t => (q125 ◇ q127) ◇ t) (cg (fun t => t ◇ ((((q125 ◇ q125) ◇ q125) ◇ q124) ◇ q125)) (cg (fun t => t ◇ q124) (apc56 q124 q125))))).trans (cg (fun t => (q125 ◇ q127) ◇ t) (apc84 q124 q124 q125))).symm).trans ((((cg (fun t => t ◇ ((((((((q125 ◇ q125) ◇ q125) ◇ q124) ◇ q125) ◇ ((((q125 ◇ q125) ◇ q125) ◇ q124) ◇ q125)) ◇ ((((q125 ◇ q125) ◇ q125) ◇ q124) ◇ q125)) ◇ q124) ◇ ((((q125 ◇ q125) ◇ q125) ◇ q124) ◇ q125))) (cg (fun t => t ◇ q127) (apc65 q124 q124 q125))).symm).trans (apc70 q124 ((((q125 ◇ q125) ◇ q125) ◇ q124) ◇ q125) q126 q127)).trans ((((cg (fun t => ((((((q125 ◇ q125) ◇ q125) ◇ q124) ◇ q125) ◇ ((((q125 ◇ q125) ◇ q125) ◇ q124) ◇ q125)) ◇ q126) ◇ t) (cg (fun t => t ◇ ((((q125 ◇ q125) ◇ q125) ◇ q124) ◇ q125)) (cg (fun t => t ◇ q124) (cg (fun t => t ◇ ((((q125 ◇ q125) ◇ q125) ◇ q124) ◇ q125)) (apc65 q124 q124 q125))))).trans (cg (fun t => ((((((q125 ◇ q125) ◇ q125) ◇ q124) ◇ q125) ◇ ((((q125 ◇ q125) ◇ q125) ◇ q124) ◇ q125)) ◇ q126) ◇ t) (cg (fun t => t ◇ ((((q125 ◇ q125) ◇ q125) ◇ q124) ◇ q125)) (cg (fun t => t ◇ q124) (apc56 q124 q125))))).trans (cg (fun t => t ◇ (((q125 ◇ q125) ◇ q124) ◇ ((((q125 ◇ q125) ◇ q125) ◇ q124) ◇ q125))) (cg (fun t => t ◇ q126) (apc65 q124 q124 q125)))).trans (cg (fun t => (q125 ◇ q126) ◇ t) (apc84 q124 q124 q125))))
  have apc126:=fun (q109 q110 q111:G)=>by
    exact (((apc104 q109 q110 q111).symm).trans (apc104 q110 q110 q111)).symm
  have apc132:=fun (q128 q129 q130 q131:G)=>by
    exact (((cg (fun t => t ◇ q131) (cg (fun t => (q128 ◇ q131) ◇ t) (cg (fun t => t ◇ ((((q128 ◇ q131) ◇ q131) ◇ q129) ◇ q128)) (cg (fun t => t ◇ q130) (cg (fun t => t ◇ q131) ((h q128 q131 q129).symm)))))).symm).trans (apc25 q128 q129 q130 q131)).symm
  have apc134:=fun (q132 q133 q134 q135:G)=>by
    exact (((cg (fun t => t ◇ ((((q132 ◇ q135) ◇ q135) ◇ q133) ◇ q132)) (cg (fun t => t ◇ q134) (cg (fun t => t ◇ q135) ((h q132 q135 q133).symm)))).symm).trans (apc132 q132 q133 q134 q135)).symm
  have apc135:=fun (q132 q133 q134 q135 q128 q129 q130 q131:G)=>by
    exact (apc132 q128 q129 q130 q131).trans (apc134 q128 q129 q130 q131)
  have apc140:=fun (q136 q137 q138:G)=>by
    exact ((((cg (fun t => (q137 ◇ q138) ◇ t) (cg (fun t => t ◇ ((((q137 ◇ q137) ◇ q137) ◇ q136) ◇ q137)) (cg (fun t => t ◇ q136) (cg (fun t => t ◇ ((((q137 ◇ q137) ◇ q137) ◇ q136) ◇ q137)) (apc65 q136 q136 q137))))).trans (cg (fun t => (q137 ◇ q138) ◇ t) (cg (fun t => t ◇ ((((q137 ◇ q137) ◇ q137) ◇ q136) ◇ q137)) (cg (fun t => t ◇ q136) (apc56 q136 q137))))).trans (cg (fun t => (q137 ◇ q138) ◇ t) (apc84 q136 q136 q137))).symm).trans ((((cg (fun t => t ◇ ((((((((q137 ◇ q137) ◇ q137) ◇ q136) ◇ q137) ◇ ((((q137 ◇ q137) ◇ q137) ◇ q136) ◇ q137)) ◇ ((((q137 ◇ q137) ◇ q137) ◇ q136) ◇ q137)) ◇ q136) ◇ ((((q137 ◇ q137) ◇ q137) ◇ q136) ◇ q137))) (cg (fun t => t ◇ q138) (apc65 q136 q136 q137))).symm).trans (apc74 q136 ((((q137 ◇ q137) ◇ q137) ◇ q136) ◇ q137) q138)).trans (((((cg (fun t => ((((((q137 ◇ q137) ◇ q137) ◇ q136) ◇ q137) ◇ ((((q137 ◇ q137) ◇ q137) ◇ q136) ◇ q137)) ◇ ((((q137 ◇ q137) ◇ q137) ◇ q136) ◇ q137)) ◇ t) (cg (fun t => t ◇ ((((q137 ◇ q137) ◇ q137) ◇ q136) ◇ q137)) (cg (fun t => t ◇ ((((q137 ◇ q137) ◇ q137) ◇ q136) ◇ q137)) (cg (fun t => t ◇ ((((q137 ◇ q137) ◇ q137) ◇ q136) ◇ q137)) (apc65 q136 q136 q137))))).trans (cg (fun t => ((((((q137 ◇ q137) ◇ q137) ◇ q136) ◇ q137) ◇ ((((q137 ◇ q137) ◇ q137) ◇ q136) ◇ q137)) ◇ ((((q137 ◇ q137) ◇ q137) ◇ q136) ◇ q137)) ◇ t) (cg (fun t => t ◇ ((((q137 ◇ q137) ◇ q137) ◇ q136) ◇ q137)) (cg (fun t => t ◇ ((((q137 ◇ q137) ◇ q137) ◇ q136) ◇ q137)) (apc56 q136 q137))))).trans (cg (fun t => t ◇ (((q137 ◇ q137) ◇ ((((q137 ◇ q137) ◇ q137) ◇ q136) ◇ q137)) ◇ ((((q137 ◇ q137) ◇ q137) ◇ q136) ◇ q137))) (cg (fun t => t ◇ ((((q137 ◇ q137) ◇ q137) ◇ q136) ◇ q137)) (apc65 q136 q136 q137)))).trans (cg (fun t => t ◇ (((q137 ◇ q137) ◇ ((((q137 ◇ q137) ◇ q137) ◇ q136) ◇ q137)) ◇ ((((q137 ◇ q137) ◇ q137) ◇ q136) ◇ q137))) (apc56 q136 q137))).trans (cg (fun t => (q137 ◇ q137) ◇ t) (apc84 q136 ((((q137 ◇ q137) ◇ q137) ◇ q136) ◇ q137) q137))))
  have apc145:=fun (q124 q125 q126 q127:G)=>by
    exact ((apc140 q124 q125 q126).symm).trans (((apc125 q124 q125 q126 q124).symm).trans (apc125 q124 q125 q124 q124))
  have apc147:=fun (q139 q140 q141 q142:G)=>by
    exact ((cg (fun t => (q140 ◇ q142) ◇ t) (cg (fun t => ((q140 ◇ q140) ◇ q139) ◇ t) ((apc54 q139 q140).symm))).symm).trans (apc125 q139 q140 q141 q142)
  have apc148:=fun (q143 q144:G)=>by
    exact ((apc32 q144 q143 q144 q143).symm).trans (((cg (fun t => t ◇ q144) ((apc147 q143 q144 q144 q143).symm)).symm).trans (apc134 q144 q143 q143 q144))
  have apc150:=fun (q145 q146 q147:G)=>by
    exact (((apc145 q145 q146 ((q146 ◇ q146) ◇ (((q146 ◇ q146) ◇ q145) ◇ ((((q146 ◇ q146) ◇ q146) ◇ q145) ◇ q146))) ((q146 ◇ q146) ◇ (((q146 ◇ q146) ◇ q145) ◇ ((((q146 ◇ q146) ◇ q146) ◇ q145) ◇ q146)))).symm).trans (((cg (fun t => t ◇ (((q146 ◇ q146) ◇ q145) ◇ ((((q146 ◇ q146) ◇ q146) ◇ q145) ◇ q146))) (apc56 q145 q146)).symm).trans (apc125 q145 q146 q147 ((((q146 ◇ q146) ◇ q146) ◇ q145) ◇ q146)))).symm
  have apc152:=fun (q148 q149 q150:G)=>by
    exact ((((cg (fun t => (q150 ◇ q150) ◇ t) (apc84 q148 q150 q150)).trans (apc150 q148 q150 q150)).symm).trans ((((cg (fun t => (q150 ◇ q150) ◇ t) (cg (fun t => ((q150 ◇ q150) ◇ q150) ◇ t) (apc54 q148 q150))).symm).trans (apc126 q149 q150 q150)).trans (apc150 q149 q150 q150))).symm
  have apc157:=fun (q151 q152 q153:G)=>by
    exact ((cg (fun t => t ◇ (((q152 ◇ q152) ◇ q152) ◇ q151)) (cg (fun t => t ◇ ((((q152 ◇ q152) ◇ q152) ◇ q151) ◇ q152)) (cg (fun t => t ◇ q153) (cg (fun t => t ◇ (((q152 ◇ q152) ◇ q152) ◇ q151)) (apc4 q151 q152))))).symm).trans ((h ((((q152 ◇ q152) ◇ q152) ◇ q151) ◇ q152) (((q152 ◇ q152) ◇ q152) ◇ q151) q153).symm)
  have apc158:=fun (q154 q155 q156:G)=>by
    exact (((((cg (fun t => t ◇ (((q156 ◇ q156) ◇ q156) ◇ q155)) (cg (fun t => ((q156 ◇ ((((q156 ◇ q156) ◇ q156) ◇ q155) ◇ q156)) ◇ q154) ◇ t) (cg (fun t => t ◇ q156) (cg (fun t => t ◇ q156) (cg (fun t => t ◇ ((((q156 ◇ q156) ◇ q156) ◇ q155) ◇ q156)) (apc56 q155 q156)))))).trans (cg (fun t => t ◇ (((q156 ◇ q156) ◇ q156) ◇ q155)) (cg (fun t => t ◇ ((((q156 ◇ q156) ◇ ((((q156 ◇ q156) ◇ q156) ◇ q155) ◇ q156)) ◇ q156) ◇ q156)) (cg (fun t => t ◇ q154) (apc56 q155 q156))))).trans (cg (fun t => t ◇ (((q156 ◇ q156) ◇ q156) ◇ q155)) (cg (fun t => ((q156 ◇ q156) ◇ q154) ◇ t) (apc66 q155 q156 q156)))).trans (cg (fun t => t ◇ (((q156 ◇ q156) ◇ q156) ◇ q155)) (apc148 q154 q156))).symm).trans (((cg (fun t => t ◇ (((q156 ◇ q156) ◇ q156) ◇ q155)) (apc32 q156 q154 ((((q156 ◇ q156) ◇ q156) ◇ q155) ◇ q156) (((q156 ◇ q156) ◇ q156) ◇ q155))).symm).trans (apc157 q155 q156 (((q156 ◇ ((((q156 ◇ q156) ◇ q156) ◇ q155) ◇ q156)) ◇ q154) ◇ ((((q156 ◇ ((((q156 ◇ q156) ◇ q156) ◇ q155) ◇ q156)) ◇ ((((q156 ◇ q156) ◇ q156) ◇ q155) ◇ q156)) ◇ q156) ◇ q156))))
  have apc180:=fun (q33 q34 q35 q157 q36:G)=>by
    exact ((cg (fun t => t ◇ q157) (cg (fun t => ((q33 ◇ q157) ◇ q36) ◇ t) (cg (fun t => t ◇ (((((q33 ◇ q157) ◇ q157) ◇ q34) ◇ q33) ◇ q157)) (cg (fun t => t ◇ q35) (apc46 q33 q34 q157))))).symm).trans ((((cg (fun t => t ◇ q157) (cg (fun t => t ◇ (((((((((q33 ◇ q157) ◇ q157) ◇ q34) ◇ q33) ◇ q157) ◇ q157) ◇ q157) ◇ q35) ◇ (((((q33 ◇ q157) ◇ q157) ◇ q34) ◇ q33) ◇ q157))) (cg (fun t => t ◇ q36) (apc17 q33 q34 q157)))).symm).trans (apc5 (((((q33 ◇ q157) ◇ q157) ◇ q34) ◇ q33) ◇ q157) q35 q157 q36)).trans (cg (fun t => t ◇ (((((q33 ◇ q157) ◇ q157) ◇ q34) ◇ q33) ◇ q157)) (cg (fun t => t ◇ q35) (apc46 q33 q34 q157))))
  have apc182:=fun (q158 q159 q160 q161 q162:G)=>by
    exact ((((cg (fun t => t ◇ q161) (cg (fun t => (q158 ◇ q162) ◇ t) (cg (fun t => (((((((q158 ◇ q161) ◇ q161) ◇ q159) ◇ q158) ◇ q161) ◇ q161) ◇ q160) ◇ t) (cg (fun t => t ◇ q161) (apc135 ((((((((q158 ◇ q161) ◇ q161) ◇ q159) ◇ q158) ◇ q161) ◇ q161) ◇ q158) ◇ ((((q158 ◇ q161) ◇ q161) ◇ q159) ◇ q158)) ((((((((q158 ◇ q161) ◇ q161) ◇ q159) ◇ q158) ◇ q161) ◇ q161) ◇ q158) ◇ ((((q158 ◇ q161) ◇ q161) ◇ q159) ◇ q158)) ((((((((q158 ◇ q161) ◇ q161) ◇ q159) ◇ q158) ◇ q161) ◇ q161) ◇ q158) ◇ ((((q158 ◇ q161) ◇ q161) ◇ q159) ◇ q158)) ((((((((q158 ◇ q161) ◇ q161) ◇ q159) ◇ q158) ◇ q161) ◇ q161) ◇ q158) ◇ ((((q158 ◇ q161) ◇ q161) ◇ q159) ◇ q158)) q158 q159 q158 q161))))).trans (cg (fun t => t ◇ q161) (cg (fun t => (q158 ◇ q162) ◇ t) (cg (fun t => (((((((q158 ◇ q161) ◇ q161) ◇ q159) ◇ q158) ◇ q161) ◇ q161) ◇ q160) ◇ t) (apc5 q158 q159 q161 q158))))).trans (cg (fun t => t ◇ q161) (cg (fun t => (q158 ◇ q162) ◇ t) (apc135 ((((((((q158 ◇ q161) ◇ q161) ◇ q159) ◇ q158) ◇ q161) ◇ q161) ◇ q160) ◇ ((((q158 ◇ q161) ◇ q161) ◇ q159) ◇ q158)) ((((((((q158 ◇ q161) ◇ q161) ◇ q159) ◇ q158) ◇ q161) ◇ q161) ◇ q160) ◇ ((((q158 ◇ q161) ◇ q161) ◇ q159) ◇ q158)) ((((((((q158 ◇ q161) ◇ q161) ◇ q159) ◇ q158) ◇ q161) ◇ q161) ◇ q160) ◇ ((((q158 ◇ q161) ◇ q161) ◇ q159) ◇ q158)) ((((((((q158 ◇ q161) ◇ q161) ◇ q159) ◇ q158) ◇ q161) ◇ q161) ◇ q160) ◇ ((((q158 ◇ q161) ◇ q161) ◇ q159) ◇ q158)) q158 q159 q160 q161)))).symm).trans ((((cg (fun t => t ◇ q161) (cg (fun t => t ◇ ((((((((q158 ◇ q161) ◇ q161) ◇ q159) ◇ q158) ◇ q161) ◇ q161) ◇ q160) ◇ (((((((((q158 ◇ q161) ◇ q161) ◇ q159) ◇ q158) ◇ q161) ◇ q161) ◇ q158) ◇ ((((q158 ◇ q161) ◇ q161) ◇ q159) ◇ q158)) ◇ q161))) (cg (fun t => t ◇ q162) ((h q158 q161 q159).symm)))).symm).trans (apc180 ((((q158 ◇ q161) ◇ q161) ◇ q159) ◇ q158) q158 q160 q161 q162)).trans (((cg (fun t => (((((((q158 ◇ q161) ◇ q161) ◇ q159) ◇ q158) ◇ q161) ◇ q161) ◇ q160) ◇ t) (cg (fun t => t ◇ q161) (apc135 ((((((((q158 ◇ q161) ◇ q161) ◇ q159) ◇ q158) ◇ q161) ◇ q161) ◇ q158) ◇ ((((q158 ◇ q161) ◇ q161) ◇ q159) ◇ q158)) ((((((((q158 ◇ q161) ◇ q161) ◇ q159) ◇ q158) ◇ q161) ◇ q161) ◇ q158) ◇ ((((q158 ◇ q161) ◇ q161) ◇ q159) ◇ q158)) ((((((((q158 ◇ q161) ◇ q161) ◇ q159) ◇ q158) ◇ q161) ◇ q161) ◇ q158) ◇ ((((q158 ◇ q161) ◇ q161) ◇ q159) ◇ q158)) ((((((((q158 ◇ q161) ◇ q161) ◇ q159) ◇ q158) ◇ q161) ◇ q161) ◇ q158) ◇ ((((q158 ◇ q161) ◇ q161) ◇ q159) ◇ q158)) q158 q159 q158 q161))).trans (cg (fun t => (((((((q158 ◇ q161) ◇ q161) ◇ q159) ◇ q158) ◇ q161) ◇ q161) ◇ q160) ◇ t) (apc5 q158 q159 q161 q158))).trans (apc135 ((((((((q158 ◇ q161) ◇ q161) ◇ q159) ◇ q158) ◇ q161) ◇ q161) ◇ q160) ◇ ((((q158 ◇ q161) ◇ q161) ◇ q159) ◇ q158)) ((((((((q158 ◇ q161) ◇ q161) ◇ q159) ◇ q158) ◇ q161) ◇ q161) ◇ q160) ◇ ((((q158 ◇ q161) ◇ q161) ◇ q159) ◇ q158)) ((((((((q158 ◇ q161) ◇ q161) ◇ q159) ◇ q158) ◇ q161) ◇ q161) ◇ q160) ◇ ((((q158 ◇ q161) ◇ q161) ◇ q159) ◇ q158)) ((((((((q158 ◇ q161) ◇ q161) ◇ q159) ◇ q158) ◇ q161) ◇ q161) ◇ q160) ◇ ((((q158 ◇ q161) ◇ q161) ◇ q159) ◇ q158)) q158 q159 q160 q161)))
  have apc183:=fun (q163 q164:G)=>by
    exact ((cg (fun t => ((((q164 ◇ q164) ◇ q164) ◇ (q164 ◇ q164)) ◇ q163) ◇ t) (apc110 q163 q164)).symm).trans (((apc182 ((q164 ◇ q164) ◇ q164) q163 q163 (q164 ◇ q164) q164).symm).trans (apc48 (((((q164 ◇ q164) ◇ q164) ◇ (q164 ◇ q164)) ◇ q163) ◇ ((((((q164 ◇ q164) ◇ q164) ◇ (q164 ◇ q164)) ◇ (q164 ◇ q164)) ◇ q163) ◇ ((q164 ◇ q164) ◇ q164))) q164))
  have apc184:=fun (q165:G)=>by
    exact ((cg (fun t => t ◇ ((q165 ◇ q165) ◇ q165)) (apc183 (q165 ◇ q165) q165)).symm).trans (apc110 (q165 ◇ (q165 ◇ q165)) q165)
  have apc186:=fun (q166:G)=>by
    exact ((cg (fun t => t ◇ (q166 ◇ (q166 ◇ q166))) ((apc54 (q166 ◇ q166) q166).symm)).symm).trans (apc183 q166 q166)
  have apc187:=fun (q167:G)=>by
    exact (((apc56 q167 q167).symm).trans (((cg (fun t => t ◇ ((((q167 ◇ q167) ◇ q167) ◇ q167) ◇ q167)) (apc186 q167)).symm).trans (apc91 q167 q167))).symm
  have apc188:=fun (q165 q167:G)=>by
    exact (apc184 q165).trans (apc187 q165)
  have apc189:=fun (q123 q167:G)=>by
    exact ((cg (fun t => t ◇ (q123 ◇ q123)) (apc187 q123)).symm).trans (apc111 q123)
  have apc191:=fun (q168:G)=>by
    exact ((cg (fun t => ((q168 ◇ q168) ◇ q168) ◇ t) (apc189 q168 ((q168 ◇ q168) ◇ (q168 ◇ q168)))).symm).trans ((((cg (fun t => t ◇ ((q168 ◇ q168) ◇ (q168 ◇ q168))) (apc189 q168 q168)).symm).trans (apc189 (q168 ◇ q168) q168)).trans (cg (fun t => t ◇ (q168 ◇ q168)) (apc189 q168 ((q168 ◇ q168) ◇ (q168 ◇ q168)))))
  have apc192:=fun (q169:G)=>by
    exact (((cg (fun t => (q169 ◇ q169) ◇ t) (cg (fun t => t ◇ (q169 ◇ q169)) (apc189 q169 q169))).symm).trans (apc188 (q169 ◇ q169) q169)).trans (apc189 q169 ((q169 ◇ q169) ◇ (q169 ◇ q169)))
  have apc193:=fun (q170:G)=>by
    exact (((cg (fun t => t ◇ q170) (apc192 q170)).symm).trans (apc3 (q170 ◇ q170) q170 q170)).symm
  have apc194:=fun (q169 q170:G)=>by
    exact ((cg (fun t => (q169 ◇ q169) ◇ t) (apc193 q169)).symm).trans (apc192 q169)
  have apc195:=fun (q168 q170:G)=>by
    exact (apc191 q168).trans (apc193 q168)
  have apc197:=fun (q171 q172:G)=>by
    exact (((((cg (fun t => t ◇ ((q172 ◇ q172) ◇ q172)) (cg (fun t => (((q172 ◇ q172) ◇ q172) ◇ q171) ◇ t) (cg (fun t => t ◇ (q172 ◇ ((q172 ◇ q172) ◇ q172))) (cg (fun t => t ◇ (q172 ◇ ((q172 ◇ q172) ◇ q172))) (cg (fun t => t ◇ q172) (cg (fun t => t ◇ q172) (apc188 q172 (q172 ◇ ((q172 ◇ q172) ◇ q172))))))))).trans (cg (fun t => t ◇ ((q172 ◇ q172) ◇ q172)) (cg (fun t => (((q172 ◇ q172) ◇ q172) ◇ q171) ◇ t) (cg (fun t => t ◇ (q172 ◇ ((q172 ◇ q172) ◇ q172))) (cg (fun t => (((q172 ◇ q172) ◇ q172) ◇ q172) ◇ t) (apc188 q172 (q172 ◇ ((q172 ◇ q172) ◇ q172)))))))).trans (cg (fun t => t ◇ ((q172 ◇ q172) ◇ q172)) (cg (fun t => (((q172 ◇ q172) ◇ q172) ◇ q171) ◇ t) (cg (fun t => ((((q172 ◇ q172) ◇ q172) ◇ q172) ◇ (q172 ◇ q172)) ◇ t) (apc188 q172 (q172 ◇ ((q172 ◇ q172) ◇ q172))))))).trans (cg (fun t => t ◇ ((q172 ◇ q172) ◇ q172)) (cg (fun t => (((q172 ◇ q172) ◇ q172) ◇ q171) ◇ t) (apc48 (q172 ◇ q172) q172)))).symm).trans (((cg (fun t => t ◇ ((q172 ◇ q172) ◇ q172)) (cg (fun t => t ◇ (((((q172 ◇ ((q172 ◇ q172) ◇ q172)) ◇ q172) ◇ q172) ◇ (q172 ◇ ((q172 ◇ q172) ◇ q172))) ◇ (q172 ◇ ((q172 ◇ q172) ◇ q172)))) (cg (fun t => t ◇ q171) (cg (fun t => t ◇ q172) (apc188 q172 q171))))).symm).trans (apc37 q171 q172 ((q172 ◇ q172) ◇ q172)))
  have apc198:=fun (q173:G)=>by
    exact (((((cg (fun t => t ◇ (((q173 ◇ q173) ◇ (q173 ◇ q173)) ◇ (q173 ◇ q173))) (cg (fun t => t ◇ (q173 ◇ q173)) (cg (fun t => t ◇ q173) (apc193 q173)))).trans (cg (fun t => (((((q173 ◇ q173) ◇ q173) ◇ q173) ◇ q173) ◇ (q173 ◇ q173)) ◇ t) (cg (fun t => t ◇ (q173 ◇ q173)) (apc189 q173 ((q173 ◇ q173) ◇ (q173 ◇ q173)))))).trans (cg (fun t => (((((q173 ◇ q173) ◇ q173) ◇ q173) ◇ q173) ◇ (q173 ◇ q173)) ◇ t) (apc193 q173))).trans (cg (fun t => t ◇ (((q173 ◇ q173) ◇ q173) ◇ q173)) (apc48 q173 q173))).symm).trans (((cg (fun t => t ◇ (((q173 ◇ q173) ◇ (q173 ◇ q173)) ◇ (q173 ◇ q173))) (cg (fun t => t ◇ (q173 ◇ q173)) (cg (fun t => t ◇ q173) (cg (fun t => t ◇ (q173 ◇ q173)) (apc189 q173 q173))))).symm).trans (apc197 q173 (q173 ◇ q173)))
  have apc199:=fun (q174:G)=>by
    exact (((cg (fun t => ((q174 ◇ q174) ◇ q174) ◇ t) (apc195 q174 q174)).symm).trans (apc187 ((q174 ◇ q174) ◇ q174))).trans (apc195 q174 (((q174 ◇ q174) ◇ q174) ◇ ((q174 ◇ q174) ◇ q174)))
  have apc201:=fun (q175 q176 q177 q178:G)=>by
    exact ((cg (fun t => t ◇ q178) (apc182 (q177 ◇ q178) q175 q176 q177 q178)).symm).trans ((h q177 q178 ((((q177 ◇ q178) ◇ q177) ◇ q176) ◇ (((((q177 ◇ q178) ◇ q177) ◇ q177) ◇ q175) ◇ (q177 ◇ q178)))).symm)
  have apc202:=fun (q179 q180:G)=>by
    exact ((((((cg (fun t => t ◇ q180) (cg (fun t => ((((((q180 ◇ q180) ◇ q180) ◇ q179) ◇ q180) ◇ (((q180 ◇ q180) ◇ q180) ◇ q180)) ◇ q179) ◇ t) (cg (fun t => t ◇ ((((q180 ◇ q180) ◇ q180) ◇ q180) ◇ q180)) (cg (fun t => t ◇ q179) (cg (fun t => t ◇ (((q180 ◇ q180) ◇ q180) ◇ q180)) (apc61 q180 q180 q180)))))).trans (cg (fun t => t ◇ q180) (cg (fun t => ((((((q180 ◇ q180) ◇ q180) ◇ q179) ◇ q180) ◇ (((q180 ◇ q180) ◇ q180) ◇ q180)) ◇ q179) ◇ t) (cg (fun t => t ◇ ((((q180 ◇ q180) ◇ q180) ◇ q180) ◇ q180)) (cg (fun t => t ◇ q179) (apc198 q180)))))).trans (cg (fun t => t ◇ q180) (cg (fun t => t ◇ (((q180 ◇ q180) ◇ q179) ◇ ((((q180 ◇ q180) ◇ q180) ◇ q180) ◇ q180))) (cg (fun t => t ◇ q179) (apc61 q179 q180 q180))))).trans (cg (fun t => t ◇ q180) (cg (fun t => (q180 ◇ q179) ◇ t) (apc148 q179 q180)))).trans (apc182 q180 q179 q179 q180 q179)).symm).trans (((cg (fun t => t ◇ q180) (cg (fun t => t ◇ ((((((((q180 ◇ q180) ◇ q180) ◇ q180) ◇ q180) ◇ (((q180 ◇ q180) ◇ q180) ◇ q180)) ◇ (((q180 ◇ q180) ◇ q180) ◇ q180)) ◇ q179) ◇ ((((q180 ◇ q180) ◇ q180) ◇ q180) ◇ q180))) (cg (fun t => t ◇ q179) (cg (fun t => t ◇ (((q180 ◇ q180) ◇ q180) ◇ q180)) (apc54 q179 q180))))).symm).trans (apc201 q179 q179 (((q180 ◇ q180) ◇ q180) ◇ q180) q180))
  have apc204:=fun (q148 q149 q150 q179 q180:G)=>by
    exact ((cg (fun t => (q150 ◇ q149) ◇ t) (apc202 q149 q150)).symm).trans ((apc152 q148 q149 q150).trans (cg (fun t => (q150 ◇ q148) ◇ t) (apc202 q148 q150)))
  have apc205:=fun (q181 q182:G)=>by
    exact ((apc8 q182 q181 q182).symm).trans ((((cg (fun t => t ◇ q182) (cg (fun t => q182 ◇ t) (apc204 q181 (((q182 ◇ q182) ◇ q182) ◇ q182) q182 q181 q181))).symm).trans (apc0 q182 (((q182 ◇ q182) ◇ q182) ◇ q182))).trans ((cg (fun t => t ◇ (((q182 ◇ q182) ◇ q182) ◇ q182)) (apc198 q182)).trans (apc194 q182 ((q182 ◇ q182) ◇ (((q182 ◇ q182) ◇ q182) ◇ q182)))))
  have apc206:=fun (q183 q184:G)=>by
    exact (((cg (fun t => t ◇ (q184 ◇ q183)) (cg (fun t => (q184 ◇ q183) ◇ t) (apc199 q184))).trans (cg (fun t => t ◇ (q184 ◇ q183)) (apc205 q183 q184))).symm).trans ((((cg (fun t => t ◇ (q184 ◇ q183)) (cg (fun t => (q184 ◇ q183) ◇ t) (cg (fun t => t ◇ (((q184 ◇ q184) ◇ q184) ◇ q184)) (apc205 q183 q184)))).symm).trans (apc0 (q184 ◇ q183) (((q184 ◇ q184) ◇ q184) ◇ q184))).trans ((cg (fun t => t ◇ (((q184 ◇ q184) ◇ q184) ◇ q184)) (apc205 q183 q184)).trans (apc199 q184)))
  have apc208:=fun (q154 q155 q156 q179 q180:G)=>by
    exact ((cg (fun t => t ◇ (((q156 ◇ q156) ◇ q156) ◇ q155)) (apc202 q155 q156)).symm).trans (apc158 q155 q155 q156)
  have apc209:=fun (q185 q186:G)=>by
    exact (((((cg (fun t => ((((((q185 ◇ q185) ◇ q185) ◇ q185) ◇ q185) ◇ (((q185 ◇ q185) ◇ q185) ◇ q185)) ◇ (((q185 ◇ q185) ◇ q185) ◇ q185)) ◇ t) (cg (fun t => t ◇ q186) (cg (fun t => t ◇ (((q185 ◇ q185) ◇ q185) ◇ q185)) (apc208 ((((q185 ◇ q185) ◇ q185) ◇ q185) ◇ (((q185 ◇ q185) ◇ q185) ◇ q185)) q185 q185 ((((q185 ◇ q185) ◇ q185) ◇ q185) ◇ (((q185 ◇ q185) ◇ q185) ◇ q185)) ((((q185 ◇ q185) ◇ q185) ◇ q185) ◇ (((q185 ◇ q185) ◇ q185) ◇ q185)))))).trans (cg (fun t => t ◇ ((((((q185 ◇ q185) ◇ q185) ◇ q185) ◇ q185) ◇ (((q185 ◇ q185) ◇ q185) ◇ q185)) ◇ q186)) (cg (fun t => t ◇ (((q185 ◇ q185) ◇ q185) ◇ q185)) (apc61 q185 q185 q185)))).trans (cg (fun t => (q185 ◇ (((q185 ◇ q185) ◇ q185) ◇ q185)) ◇ t) (cg (fun t => t ◇ q186) (apc61 q185 q185 q185)))).trans (cg (fun t => t ◇ (q185 ◇ q186)) (apc198 q185))).symm).trans ((((cg (fun t => t ◇ ((((((q185 ◇ q185) ◇ q185) ◇ q185) ◇ (((q185 ◇ q185) ◇ q185) ◇ q185)) ◇ (((q185 ◇ q185) ◇ q185) ◇ q185)) ◇ q186)) (cg (fun t => t ◇ (((q185 ◇ q185) ◇ q185) ◇ q185)) (cg (fun t => t ◇ (((q185 ◇ q185) ◇ q185) ◇ q185)) (apc208 q185 q185 q185 q185 q185)))).symm).trans (apc208 q185 q186 (((q185 ◇ q185) ◇ q185) ◇ q185) q185 q185)).trans (((cg (fun t => t ◇ (((q185 ◇ q185) ◇ q185) ◇ q185)) (cg (fun t => t ◇ q186) (cg (fun t => t ◇ (((q185 ◇ q185) ◇ q185) ◇ q185)) (apc208 ((((q185 ◇ q185) ◇ q185) ◇ q185) ◇ (((q185 ◇ q185) ◇ q185) ◇ q185)) q185 q185 ((((q185 ◇ q185) ◇ q185) ◇ q185) ◇ (((q185 ◇ q185) ◇ q185) ◇ q185)) ((((q185 ◇ q185) ◇ q185) ◇ q185) ◇ (((q185 ◇ q185) ◇ q185) ◇ q185)))))).trans (cg (fun t => t ◇ (((q185 ◇ q185) ◇ q185) ◇ q185)) (cg (fun t => t ◇ q186) (apc61 q185 q185 q185)))).trans (apc205 q186 q185)))
  have apc213:=fun (q187 q188 q189:G)=>by
    exact ((((cg (fun t => t ◇ (q187 ◇ q188)) (cg (fun t => (((q187 ◇ q187) ◇ q187) ◇ q189) ◇ t) (cg (fun t => t ◇ (q187 ◇ q187)) (cg (fun t => t ◇ q187) (cg (fun t => t ◇ (q187 ◇ q188)) (apc209 q187 q188)))))).trans (cg (fun t => t ◇ (q187 ◇ q188)) (cg (fun t => (((q187 ◇ q187) ◇ q187) ◇ q189) ◇ t) (cg (fun t => t ◇ (q187 ◇ q187)) (cg (fun t => t ◇ q187) (apc206 q188 q187)))))).trans (cg (fun t => t ◇ (q187 ◇ q188)) (cg (fun t => (((q187 ◇ q187) ◇ q187) ◇ q189) ◇ t) (apc48 q187 q187)))).symm).trans ((((cg (fun t => t ◇ (q187 ◇ q188)) (cg (fun t => t ◇ (((((q187 ◇ q187) ◇ (q187 ◇ q188)) ◇ (q187 ◇ q188)) ◇ q187) ◇ (q187 ◇ q187))) (cg (fun t => t ◇ q189) (apc209 q187 q188)))).symm).trans (apc5 (q187 ◇ q187) q187 (q187 ◇ q188) q189)).trans (((cg (fun t => t ◇ (q187 ◇ q187)) (cg (fun t => t ◇ q187) (cg (fun t => t ◇ (q187 ◇ q188)) (apc209 q187 q188)))).trans (cg (fun t => t ◇ (q187 ◇ q187)) (cg (fun t => t ◇ q187) (apc206 q188 q187)))).trans (apc48 q187 q187)))
  have apc214:=fun (q190 q191:G)=>by
    exact (((cg (fun t => t ◇ ((q190 ◇ q190) ◇ q191)) (cg (fun t => t ◇ (q190 ◇ q190)) (cg (fun t => t ◇ q190) (apc206 q190 q190)))).trans (cg (fun t => t ◇ ((q190 ◇ q190) ◇ q191)) (apc48 q190 q190))).symm).trans (((cg (fun t => t ◇ ((q190 ◇ q190) ◇ q191)) (cg (fun t => t ◇ (q190 ◇ q190)) (cg (fun t => t ◇ q190) (cg (fun t => t ◇ (q190 ◇ q190)) (apc209 q190 q190))))).symm).trans (apc213 (q190 ◇ q190) q191 q190))
  have apc215:=fun (q192 q193:G)=>by
    exact (((cg (fun t => (q192 ◇ q192) ◇ t) (cg (fun t => t ◇ q193) (apc209 q192 q192))).symm).trans (apc214 (q192 ◇ q192) q193)).trans (apc209 q192 q192)
  have apc216:=fun (q194 q195:G)=>by
    exact ((cg (fun t => t ◇ q195) (apc215 q195 q194)).symm).trans (apc3 q194 q195 q195)
  have apc217:=fun (q196 q197:G)=>by
    exact ((((cg (fun t => t ◇ (((q196 ◇ q196) ◇ q196) ◇ q196)) (apc61 q196 q196 q196)).trans (apc198 q196)).symm).trans ((((cg (fun t => t ◇ (((q196 ◇ q196) ◇ q196) ◇ q196)) (cg (fun t => t ◇ (((q196 ◇ q196) ◇ q196) ◇ q196)) (apc208 q196 q196 q196 q196 q196))).symm).trans (apc216 q197 (((q196 ◇ q196) ◇ q196) ◇ q196))).trans ((cg (fun t => t ◇ q197) (cg (fun t => t ◇ (((q196 ◇ q196) ◇ q196) ◇ q196)) (apc208 ((((q196 ◇ q196) ◇ q196) ◇ q196) ◇ (((q196 ◇ q196) ◇ q196) ◇ q196)) q196 q196 ((((q196 ◇ q196) ◇ q196) ◇ q196) ◇ (((q196 ◇ q196) ◇ q196) ◇ q196)) ((((q196 ◇ q196) ◇ q196) ◇ q196) ◇ (((q196 ◇ q196) ◇ q196) ◇ q196))))).trans (cg (fun t => t ◇ q197) (apc61 q196 q196 q196))))).symm
  have apc218:=fun (q198 q199:G)=>by
    exact (((cg (fun t => t ◇ ((((q198 ◇ q198) ◇ q198) ◇ q198) ◇ q198)) (apc217 q198 ((((q198 ◇ q198) ◇ q198) ◇ q198) ◇ q198))).trans (apc217 (q198 ◇ q198) ((((q198 ◇ q198) ◇ q198) ◇ q198) ◇ q198))).symm).trans ((((cg (fun t => t ◇ ((((q198 ◇ q198) ◇ q198) ◇ q198) ◇ q198)) (cg (fun t => t ◇ ((((q198 ◇ q198) ◇ q198) ◇ q198) ◇ q198)) (apc65 q198 q198 q198))).symm).trans (apc216 q199 ((((q198 ◇ q198) ◇ q198) ◇ q198) ◇ q198))).trans ((cg (fun t => t ◇ q199) (cg (fun t => t ◇ ((((q198 ◇ q198) ◇ q198) ◇ q198) ◇ q198)) (apc65 q198 q198 q198))).trans (cg (fun t => t ◇ q199) (apc217 q198 ((((q198 ◇ q198) ◇ q198) ◇ q198) ◇ q198)))))
  have apc219:=fun (q198 q199:G)=>by
    exact ((apc218 q198 q199).symm).trans (apc218 q198 q198)
  exact (calc
    ((x ◇ x) ◇ y)=((x ◇ x) ◇ x):=apc219 x y
    _=((x ◇ (y ◇ z)) ◇ x):=((cg (fun t => t ◇ x) (cg (fun t => x ◇ t) (apc217 y z))).trans (cg (fun t => t ◇ x) (apc217 x (y ◇ y)))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_40762_to_60891 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_40762_to_60891
