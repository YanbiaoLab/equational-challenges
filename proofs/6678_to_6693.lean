-- Equation6678 → Equation6693
-- Recorded verdict: true
-- Premise: x = y ◇ (x ◇ ((x ◇ z) ◇ (y ◇ z)))
-- Conclusion: x = y ◇ (x ◇ ((y ◇ x) ◇ (y ◇ y)))
-- Original submission SHA-256: 9393a001f5dd93a5f25a79cf8c0947fa305381665a576606ffd78d9397b27a3e
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (x ◇ ((x ◇ z) ◇ (y ◇ z)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = y ◇ (x ◇ ((y ◇ x) ◇ (y ◇ y)))
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
    exact ((cg (fun t => ((q1 ◇ (q1 ◇ q0)) ◇ q0) ◇ t) ((h (q1 ◇ (q1 ◇ q0)) q1 q0).symm)).symm).trans ((h q1 ((q1 ◇ (q1 ◇ q0)) ◇ q0) (q1 ◇ q0)).symm)
  have apc1:=fun (x y z:G)=>by
    exact ((h x y z).symm).trans (h x x x)
  have apc2:=fun (x y z:G)=>by
    exact ((h x x x).trans (apc1 x x x)).symm
  have apc3:=fun (q2:G)=>by
    exact ((cg (fun t => (q2 ◇ ((q2 ◇ q2) ◇ (q2 ◇ q2))) ◇ t) (apc2 q2 (q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ (q2 ◇ q2)))) (q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ (q2 ◇ q2)))))).symm).trans (((cg (fun t => t ◇ (q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ (q2 ◇ q2))))) (cg (fun t => t ◇ ((q2 ◇ q2) ◇ (q2 ◇ q2))) (apc2 q2 q2 q2))).symm).trans (apc0 ((q2 ◇ q2) ◇ (q2 ◇ q2)) q2))
  have apc4:=fun (q3:G)=>by
    exact (((((cg (fun t => t ◇ ((q3 ◇ ((q3 ◇ q3) ◇ (q3 ◇ q3))) ◇ ((q3 ◇ ((q3 ◇ q3) ◇ (q3 ◇ q3))) ◇ q3))) (cg (fun t => t ◇ q3) (apc3 q3))).trans (cg (fun t => (q3 ◇ q3) ◇ t) (cg (fun t => (q3 ◇ ((q3 ◇ q3) ◇ (q3 ◇ q3))) ◇ t) (apc3 q3)))).trans (cg (fun t => (q3 ◇ q3) ◇ t) (apc3 q3))).symm).trans (((cg (fun t => t ◇ ((q3 ◇ ((q3 ◇ q3) ◇ (q3 ◇ q3))) ◇ ((q3 ◇ ((q3 ◇ q3) ◇ (q3 ◇ q3))) ◇ q3))) (cg (fun t => t ◇ q3) (cg (fun t => (q3 ◇ ((q3 ◇ q3) ◇ (q3 ◇ q3))) ◇ t) (apc3 q3)))).symm).trans (apc0 q3 (q3 ◇ ((q3 ◇ q3) ◇ (q3 ◇ q3)))))).symm
  have apc5:=fun (x y z q3:G)=>by
    exact ((cg (fun t => x ◇ t) (apc4 x)).symm).trans (apc2 x x x)
  have apc6:=fun (q2 q3:G)=>by
    exact ((cg (fun t => t ◇ q2) (apc4 q2)).symm).trans (apc3 q2)
  have apc7:=fun (q4:G)=>by
    exact ((cg (fun t => ((q4 ◇ q4) ◇ ((q4 ◇ q4) ◇ q4)) ◇ t) (cg (fun t => q4 ◇ t) (apc5 q4 (q4 ◇ ((q4 ◇ q4) ◇ q4)) (q4 ◇ ((q4 ◇ q4) ◇ q4)) (q4 ◇ ((q4 ◇ q4) ◇ q4))))).symm).trans (((cg (fun t => t ◇ (q4 ◇ (q4 ◇ ((q4 ◇ q4) ◇ q4)))) (cg (fun t => t ◇ ((q4 ◇ q4) ◇ q4)) (cg (fun t => q4 ◇ t) (apc5 q4 q4 q4 q4)))).symm).trans (apc0 ((q4 ◇ q4) ◇ q4) q4))
  have apc8:=fun (q5 q6:G)=>by
    exact ((cg (fun t => ((q6 ◇ q6) ◇ q6) ◇ t) (cg (fun t => q5 ◇ t) (cg (fun t => (q5 ◇ q6) ◇ t) (apc6 q6 q5)))).symm).trans ((h q5 ((q6 ◇ q6) ◇ q6) q6).symm)
  have apc9:=fun (q7:G)=>by
    exact ((cg (fun t => ((q7 ◇ q7) ◇ q7) ◇ t) (cg (fun t => (q7 ◇ q7) ◇ t) (apc6 q7 q7))).symm).trans (apc8 (q7 ◇ q7) q7)
  have apc10:=fun (q8:G)=>by
    exact ((cg (fun t => (q8 ◇ q8) ◇ t) (cg (fun t => (q8 ◇ q8) ◇ t) (apc9 q8))).symm).trans ((h (q8 ◇ q8) (q8 ◇ q8) q8).symm)
  have apc11:=fun (q9:G)=>by
    exact (((cg (fun t => ((((q9 ◇ q9) ◇ (q9 ◇ q9)) ◇ ((q9 ◇ q9) ◇ (q9 ◇ q9))) ◇ ((q9 ◇ q9) ◇ (q9 ◇ q9))) ◇ t) (cg (fun t => (q9 ◇ q9) ◇ t) (apc10 q9))).trans (apc6 ((q9 ◇ q9) ◇ (q9 ◇ q9)) (((((q9 ◇ q9) ◇ (q9 ◇ q9)) ◇ ((q9 ◇ q9) ◇ (q9 ◇ q9))) ◇ ((q9 ◇ q9) ◇ (q9 ◇ q9))) ◇ ((q9 ◇ q9) ◇ (q9 ◇ q9))))).symm).trans (((cg (fun t => ((((q9 ◇ q9) ◇ (q9 ◇ q9)) ◇ ((q9 ◇ q9) ◇ (q9 ◇ q9))) ◇ ((q9 ◇ q9) ◇ (q9 ◇ q9))) ◇ t) (cg (fun t => (q9 ◇ q9) ◇ t) (cg (fun t => t ◇ ((q9 ◇ q9) ◇ (q9 ◇ q9))) (apc10 q9)))).symm).trans (apc8 (q9 ◇ q9) ((q9 ◇ q9) ◇ (q9 ◇ q9))))
  have apc16:=fun (q10 q11:G)=>by
    exact ((cg (fun t => q11 ◇ t) (cg (fun t => q10 ◇ t) (cg (fun t => (q10 ◇ ((q11 ◇ q11) ◇ q11)) ◇ t) (apc5 q11 q10 q10 q10)))).symm).trans ((h q10 q11 ((q11 ◇ q11) ◇ q11)).symm)
  have apc17:=fun (q12 q0 q1 q13:G)=>by
    exact ((cg (fun t => q13 ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => t ◇ (q13 ◇ (q12 ◇ ((q12 ◇ q0) ◇ (q1 ◇ q0))))) ((h q12 q1 q0).symm)))).symm).trans ((h q1 q13 (q12 ◇ ((q12 ◇ q0) ◇ (q1 ◇ q0)))).symm)
  have apc18:=fun (q14 q15:G)=>by
    exact ((cg (fun t => q15 ◇ t) (cg (fun t => q15 ◇ t) (cg (fun t => q14 ◇ t) ((h q14 q15 q14).symm)))).symm).trans (apc17 q14 q14 q15 q15)
  have apc19:=fun (q16 q17:G)=>by
    exact ((cg (fun t => (q17 ◇ (q16 ◇ q16)) ◇ t) (apc18 q16 q17)).symm).trans (((cg (fun t => (q17 ◇ (q16 ◇ q16)) ◇ t) (cg (fun t => q17 ◇ t) (apc18 q16 (q17 ◇ (q16 ◇ q16))))).symm).trans ((h q17 (q17 ◇ (q16 ◇ q16)) (q16 ◇ q16)).symm))
  have apc20:=fun (q18 q19:G)=>by
    exact (((((cg (fun t => t ◇ ((q19 ◇ (q18 ◇ q18)) ◇ ((q19 ◇ (q18 ◇ q18)) ◇ q19))) (cg (fun t => t ◇ q19) (apc19 q18 q19))).trans (cg (fun t => (q19 ◇ q19) ◇ t) (cg (fun t => (q19 ◇ (q18 ◇ q18)) ◇ t) (apc19 q18 q19)))).trans (cg (fun t => (q19 ◇ q19) ◇ t) (apc19 q18 q19))).symm).trans (((cg (fun t => t ◇ ((q19 ◇ (q18 ◇ q18)) ◇ ((q19 ◇ (q18 ◇ q18)) ◇ q19))) (cg (fun t => t ◇ q19) (cg (fun t => (q19 ◇ (q18 ◇ q18)) ◇ t) (apc19 q18 q19)))).symm).trans (apc0 q19 (q19 ◇ (q18 ◇ q18))))).symm
  have apc21:=fun (q20 q21:G)=>by
    exact ((cg (fun t => ((q21 ◇ q21) ◇ (q20 ◇ q20)) ◇ t) (apc19 q20 (q21 ◇ q21))).symm).trans (apc18 q21 ((q21 ◇ q21) ◇ (q20 ◇ q20)))
  have apc22:=fun (q22 q23:G)=>by
    exact (((((cg (fun t => t ◇ (q23 ◇ q23)) (cg (fun t => t ◇ (q23 ◇ q23)) (apc11 q23))).trans (cg (fun t => t ◇ (q23 ◇ q23)) (apc11 q23))).trans (apc11 q23)).symm).trans (((cg (fun t => t ◇ (q23 ◇ q23)) (apc20 q22 (q23 ◇ q23))).symm).trans (apc21 q22 q23))).symm
  have apc23:=fun (q24 q25:G)=>by
    exact (((((((cg (fun t => t ◇ ((q25 ◇ q25) ◇ ((q25 ◇ q25) ◇ (q24 ◇ q24)))) (cg (fun t => t ◇ (q24 ◇ q24)) (apc22 q24 q24))).trans (cg (fun t => ((q24 ◇ q24) ◇ (q24 ◇ q24)) ◇ t) (cg (fun t => (q25 ◇ q25) ◇ t) (apc22 q24 q25)))).trans (cg (fun t => t ◇ ((q25 ◇ q25) ◇ (q25 ◇ q25))) (apc22 q24 q24))).trans (cg (fun t => (q24 ◇ q24) ◇ t) (apc22 q25 q25))).trans (apc22 q25 q24)).symm).trans (((cg (fun t => (((q24 ◇ q24) ◇ (q24 ◇ q24)) ◇ (q24 ◇ q24)) ◇ t) (cg (fun t => (q25 ◇ q25) ◇ t) (cg (fun t => t ◇ (q24 ◇ q24)) (apc22 q24 q25)))).symm).trans (apc8 (q25 ◇ q25) (q24 ◇ q24)))).symm
  have apc24:=fun (q26 q27:G)=>by
    exact ((cg (fun t => q27 ◇ t) (cg (fun t => t ◇ q27) (apc23 q26 q27))).symm).trans (apc5 q27 q26 q26 q26)
  have apc25:=fun (q28 q29:G)=>by
    exact ((cg (fun t => t ◇ q29) (cg (fun t => t ◇ q29) (apc23 q28 q29))).symm).trans (apc6 q29 q28)
  have apc26:=fun (q30 q31:G)=>by
    exact ((((cg (fun t => t ◇ (((q30 ◇ q30) ◇ q31) ◇ (((q30 ◇ q30) ◇ q31) ◇ q31))) (cg (fun t => t ◇ q31) (apc25 q30 q31))).trans (cg (fun t => (q31 ◇ q31) ◇ t) (cg (fun t => ((q30 ◇ q30) ◇ q31) ◇ t) (apc25 q30 q31)))).trans (cg (fun t => (q31 ◇ q31) ◇ t) (apc25 q30 q31))).symm).trans (((cg (fun t => t ◇ (((q30 ◇ q30) ◇ q31) ◇ (((q30 ◇ q30) ◇ q31) ◇ q31))) (cg (fun t => t ◇ q31) (cg (fun t => ((q30 ◇ q30) ◇ q31) ◇ t) (apc25 q30 q31)))).symm).trans (apc0 q31 ((q30 ◇ q30) ◇ q31)))
  have apc28:=fun (q32 q33:G)=>by
    exact ((((cg (fun t => q33 ◇ t) (cg (fun t => (q32 ◇ (q32 ◇ q32)) ◇ t) (cg (fun t => q32 ◇ t) (cg (fun t => q33 ◇ t) (cg (fun t => q32 ◇ t) (apc20 q32 q32)))))).trans (cg (fun t => q33 ◇ t) (cg (fun t => (q32 ◇ (q32 ◇ q32)) ◇ t) (cg (fun t => q32 ◇ t) (cg (fun t => q33 ◇ t) (apc24 q32 q32)))))).trans (cg (fun t => q33 ◇ t) (cg (fun t => t ◇ (q32 ◇ (q33 ◇ q32))) (apc20 q32 q32)))).symm).trans ((((cg (fun t => q33 ◇ t) (cg (fun t => (q32 ◇ (q32 ◇ q32)) ◇ t) (cg (fun t => q32 ◇ t) (cg (fun t => q33 ◇ t) (cg (fun t => q32 ◇ t) (apc18 q32 (q32 ◇ (q32 ◇ q32)))))))).symm).trans (apc17 q32 (q32 ◇ q32) (q32 ◇ (q32 ◇ q32)) q33)).trans (apc20 q32 q32))
  have apc29:=fun (q34 q35 q36:G)=>by
    exact ((cg (fun t => q35 ◇ t) (cg (fun t => q36 ◇ t) (cg (fun t => t ◇ (q35 ◇ q36)) (apc23 q34 q36)))).symm).trans ((h q36 q35 q36).symm)
  have apc30:=fun (q34 q37 q36:G)=>by
    exact ((cg (fun t => q36 ◇ t) (cg (fun t => q37 ◇ t) (cg (fun t => (q37 ◇ q36) ◇ t) (apc23 q34 q36)))).symm).trans ((h q37 q36 q36).symm)
  have apc31:=fun (q38 q39:G)=>by
    exact ((cg (fun t => t ◇ ((q39 ◇ q39) ◇ q39)) (cg (fun t => t ◇ q39) (apc23 q38 q39))).symm).trans (apc9 q39)
  have apc33:=fun (q40 q41 q42:G)=>by
    exact ((cg (fun t => ((q41 ◇ q41) ◇ q42) ◇ t) (cg (fun t => t ◇ q42) (apc23 q40 q42))).symm).trans (apc31 q41 q42)
  have apc34:=fun (q43 q44:G)=>by
    exact (((cg (fun t => t ◇ ((q43 ◇ q43) ◇ q43)) (apc9 q43)).symm).trans (apc26 q44 ((q43 ◇ q43) ◇ q43))).symm
  have apc35:=fun (q45 q46 q47:G)=>by
    exact (((cg (fun t => t ◇ ((q45 ◇ q45) ◇ q46)) (apc33 q45 q45 q46)).symm).trans (apc26 q47 ((q45 ◇ q45) ◇ q46))).symm
  have apc37:=fun (q48:G)=>by
    exact ((cg (fun t => ((q48 ◇ q48) ◇ ((q48 ◇ q48) ◇ q48)) ◇ t) (apc7 q48)).symm).trans (apc18 q48 ((q48 ◇ q48) ◇ ((q48 ◇ q48) ◇ q48)))
  have apc41:=fun (q49 q50:G)=>by
    exact (((apc35 q49 q50 q49).symm).trans (((cg (fun t => (q49 ◇ q49) ◇ t) (cg (fun t => t ◇ q50) (apc23 q49 q50))).symm).trans (apc34 q50 q49))).symm
  have apc55:=fun (q51 q52 q53:G)=>by
    exact ((cg (fun t => q53 ◇ t) (cg (fun t => q52 ◇ t) (cg (fun t => t ◇ q53) (cg (fun t => q52 ◇ t) (cg (fun t => t ◇ q53) (apc23 q51 q53)))))).symm).trans (apc16 q52 q53)
  have apc56:=fun (q54 q55:G)=>by
    exact ((cg (fun t => t ◇ q55) (cg (fun t => t ◇ ((q55 ◇ q55) ◇ q55)) (apc23 q54 q55))).symm).trans (apc37 q55)
  have apc57:=fun (q56 q57:G)=>by
    exact (((((((cg (fun t => ((((q56 ◇ q56) ◇ ((q57 ◇ q57) ◇ q57)) ◇ ((q57 ◇ q57) ◇ ((q57 ◇ q57) ◇ q57))) ◇ q57) ◇ t) (cg (fun t => ((q56 ◇ q56) ◇ ((q57 ◇ q57) ◇ q57)) ◇ t) (apc56 q56 q57))).trans (cg (fun t => t ◇ (((q56 ◇ q56) ◇ ((q57 ◇ q57) ◇ q57)) ◇ ((q57 ◇ q57) ◇ ((q57 ◇ q57) ◇ q57)))) (cg (fun t => t ◇ q57) (apc33 q57 q56 ((q57 ◇ q57) ◇ q57))))).trans (cg (fun t => t ◇ (((q56 ◇ q56) ◇ ((q57 ◇ q57) ◇ q57)) ◇ ((q57 ◇ q57) ◇ ((q57 ◇ q57) ◇ q57)))) (cg (fun t => t ◇ q57) (apc33 q57 q57 q57)))).trans (cg (fun t => ((q57 ◇ q57) ◇ q57) ◇ t) (apc33 q57 q56 ((q57 ◇ q57) ◇ q57)))).trans (cg (fun t => ((q57 ◇ q57) ◇ q57) ◇ t) (apc33 q57 q57 q57))).symm).trans (((cg (fun t => t ◇ (((q56 ◇ q56) ◇ ((q57 ◇ q57) ◇ q57)) ◇ (((q56 ◇ q56) ◇ ((q57 ◇ q57) ◇ q57)) ◇ q57))) (cg (fun t => t ◇ q57) (cg (fun t => ((q56 ◇ q56) ◇ ((q57 ◇ q57) ◇ q57)) ◇ t) (apc56 q56 q57)))).symm).trans (apc0 q57 ((q56 ◇ q56) ◇ ((q57 ◇ q57) ◇ q57))))).symm
  have apc62:=fun (q58 q59:G)=>by
    exact ((cg (fun t => q59 ◇ t) (cg (fun t => q58 ◇ t) (apc20 q59 (q58 ◇ q59)))).symm).trans ((h q58 q59 q59).symm)
  have apc63:=fun (q60 q61 q62:G)=>by
    exact ((cg (fun t => q62 ◇ t) (cg (fun t => q61 ◇ t) (cg (fun t => t ◇ (q61 ◇ q62)) (apc23 q60 (q61 ◇ q62))))).symm).trans (apc62 q61 q62)
  have apc81:=fun (q63 q64 q65:G)=>by
    exact (((cg (fun t => t ◇ ((q64 ◇ q64) ◇ q65)) (apc23 q63 q65)).symm).trans ((apc41 q64 q65).symm)).trans (apc57 q65 q65)
  have apc89:=fun (q66 q67 q68:G)=>by
    exact ((cg (fun t => ((q68 ◇ q66) ◇ ((q67 ◇ q67) ◇ q66)) ◇ t) (cg (fun t => q68 ◇ t) ((h q68 (q67 ◇ q67) q66).symm))).symm).trans (apc63 q67 q68 ((q68 ◇ q66) ◇ ((q67 ◇ q67) ◇ q66)))
  have apc90:=fun (q69 q70 q71:G)=>by
    exact (((((((cg (fun t => t ◇ (((q71 ◇ q69) ◇ ((q70 ◇ q70) ◇ q69)) ◇ ((q71 ◇ q69) ◇ ((q70 ◇ q70) ◇ q69)))) (cg (fun t => q71 ◇ t) (apc22 q71 q69))).trans (cg (fun t => t ◇ (((q71 ◇ q69) ◇ ((q70 ◇ q70) ◇ q69)) ◇ ((q71 ◇ q69) ◇ ((q70 ◇ q70) ◇ q69)))) (apc20 q69 q71))).trans (apc20 ((q71 ◇ q69) ◇ ((q70 ◇ q70) ◇ q69)) ((q71 ◇ q71) ◇ q71))).trans (cg (fun t => t ◇ ((q71 ◇ q71) ◇ q71)) (apc33 q71 q71 q71))).trans (apc81 q71 q71 q71)).symm).trans (((cg (fun t => t ◇ (((q71 ◇ q69) ◇ ((q70 ◇ q70) ◇ q69)) ◇ ((q71 ◇ q69) ◇ ((q70 ◇ q70) ◇ q69)))) (cg (fun t => t ◇ ((q69 ◇ q69) ◇ (q71 ◇ q71))) (apc89 q69 q70 q71))).symm).trans (apc89 (q71 ◇ q71) q69 ((q71 ◇ q69) ◇ ((q70 ◇ q70) ◇ q69))))).symm
  have apc91:=fun (q72 q73 q74:G)=>by
    exact ((cg (fun t => ((q73 ◇ q73) ◇ q72) ◇ t) (cg (fun t => (q74 ◇ q72) ◇ t) (apc89 q72 q73 q74))).symm).trans (apc30 q74 (q74 ◇ q72) ((q73 ◇ q73) ◇ q72))
  have apc92:=fun (q75 q76 q77:G)=>by
    exact (((cg (fun t => ((q77 ◇ q77) ◇ q76) ◇ t) (apc0 q76 q75)).symm).trans (apc91 q76 q77 (q75 ◇ (q75 ◇ q76)))).symm
  have apc93:=fun (q75 q76 q77:G)=>by
    exact ((apc92 q75 q76 q77).symm).trans (apc92 q75 q76 q75)
  have apc94:=fun (q78 q79:G)=>by
    exact ((apc93 q78 q79 q79).symm).trans (((cg (fun t => t ◇ q78) ((apc26 q78 q79).symm)).symm).trans ((apc92 q78 q79 q78).symm))
  have apc96:=fun (q80 q81:G)=>by
    exact ((((cg (fun t => t ◇ q81) (apc28 q80 (q81 ◇ q81))).symm).trans (apc94 q81 (((q80 ◇ q80) ◇ q80) ◇ (q80 ◇ ((q81 ◇ q81) ◇ q80))))).trans ((((cg (fun t => t ◇ (((q80 ◇ q80) ◇ q80) ◇ (q80 ◇ ((q81 ◇ q81) ◇ q80)))) (cg (fun t => q81 ◇ t) (cg (fun t => q81 ◇ t) (cg (fun t => ((q80 ◇ q80) ◇ q80) ◇ t) (apc24 q81 q80))))).trans (cg (fun t => t ◇ (((q80 ◇ q80) ◇ q80) ◇ (q80 ◇ ((q81 ◇ q81) ◇ q80)))) (cg (fun t => q81 ◇ t) (cg (fun t => q81 ◇ t) (apc25 q80 q80))))).trans (cg (fun t => (q81 ◇ (q81 ◇ q80)) ◇ t) (cg (fun t => ((q80 ◇ q80) ◇ q80) ◇ t) (apc24 q81 q80)))).trans (cg (fun t => (q81 ◇ (q81 ◇ q80)) ◇ t) (apc25 q80 q80)))).symm
  have apc103:=fun (q82 q83:G)=>by
    exact (((apc20 (q83 ◇ q82) q83).symm).trans ((((cg (fun t => t ◇ ((q83 ◇ q82) ◇ (q83 ◇ q82))) ((h q83 q83 q82).symm)).symm).trans (apc96 ((q83 ◇ q82) ◇ (q83 ◇ q82)) q83)).trans ((cg (fun t => t ◇ q83) (cg (fun t => t ◇ ((q83 ◇ q82) ◇ (q83 ◇ q82))) (apc22 (q83 ◇ q82) (q83 ◇ q82)))).trans (cg (fun t => t ◇ q83) (apc22 (q83 ◇ q82) (q83 ◇ q82)))))).symm
  have apc104:=fun (q84 q85:G)=>by
    exact (((apc33 q84 q85 q85).symm).trans ((((cg (fun t => t ◇ ((q84 ◇ q84) ◇ q85)) (apc103 q84 q85)).symm).trans (apc90 q85 q84 ((q85 ◇ q84) ◇ (q85 ◇ q84)))).trans ((((cg (fun t => t ◇ (((q85 ◇ q84) ◇ (q85 ◇ q84)) ◇ ((q85 ◇ q84) ◇ (q85 ◇ q84)))) (cg (fun t => t ◇ ((q85 ◇ q84) ◇ (q85 ◇ q84))) (apc22 (q85 ◇ q84) (q85 ◇ q84)))).trans (cg (fun t => t ◇ (((q85 ◇ q84) ◇ (q85 ◇ q84)) ◇ ((q85 ◇ q84) ◇ (q85 ◇ q84)))) (apc22 (q85 ◇ q84) (q85 ◇ q84)))).trans (cg (fun t => ((q85 ◇ q84) ◇ (q85 ◇ q84)) ◇ t) (apc22 (q85 ◇ q84) (q85 ◇ q84)))).trans (apc22 (q85 ◇ q84) (q85 ◇ q84))))).symm
  have apc105:=fun (q86 q87 q88:G)=>by
    exact (((cg (fun t => t ◇ (q87 ◇ q86)) (apc104 q86 q87)).symm).trans (apc26 q88 (q87 ◇ q86))).symm
  have apc111:=fun (q89 q90 q91:G)=>by
    exact (((cg (fun t => (q91 ◇ q91) ◇ t) (apc91 q89 q89 q90)).symm).trans (apc105 ((q90 ◇ q89) ◇ q90) ((q89 ◇ q89) ◇ q89) q91)).trans ((cg (fun t => t ◇ (((q89 ◇ q89) ◇ q89) ◇ ((q90 ◇ q89) ◇ q90))) (apc33 q89 q89 q89)).trans (cg (fun t => (q89 ◇ q89) ◇ t) (apc91 q89 q89 q90)))
  have apc112:=fun (q92 q93:G)=>by
    exact (((((cg (fun t => (q93 ◇ q92) ◇ t) (cg (fun t => ((q92 ◇ q92) ◇ (q93 ◇ q92)) ◇ t) (apc111 q92 q93 q93))).trans (cg (fun t => (q93 ◇ q92) ◇ t) (cg (fun t => t ◇ ((q92 ◇ q92) ◇ (q93 ◇ q92))) (apc111 q92 q93 q92)))).trans (cg (fun t => (q93 ◇ q92) ◇ t) (apc33 q92 q92 (q93 ◇ q92)))).trans (cg (fun t => (q93 ◇ q92) ◇ t) (apc104 q92 q93))).symm).trans ((((cg (fun t => (q93 ◇ q92) ◇ t) (cg (fun t => ((q92 ◇ q92) ◇ (q93 ◇ q92)) ◇ t) (apc105 q92 q93 ((q92 ◇ q92) ◇ (q93 ◇ q92))))).symm).trans (apc55 q92 ((q92 ◇ q92) ◇ (q93 ◇ q92)) (q93 ◇ q92))).trans (apc111 q92 q93 q92))
  exact (calc
    x=x:=rfl
    _=(y ◇ (x ◇ ((y ◇ x) ◇ (y ◇ y)))):=((cg (fun t => y ◇ t) (cg (fun t => x ◇ t) (apc112 x y))).trans (apc29 x y x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_6678_to_6693 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_6678_to_6693
