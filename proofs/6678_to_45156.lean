-- Equation6678 → Equation45156
-- Recorded verdict: true
-- Premise: x = y ◇ (x ◇ ((x ◇ z) ◇ (y ◇ z)))
-- Conclusion: x ◇ x = y ◇ (((y ◇ z) ◇ z) ◇ z)
-- Original submission SHA-256: 3db0ccac4ee933a2a688a2d8095eb041f8cc0863e56665fa2a93b93fb7769b0e
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (x ◇ ((x ◇ z) ◇ (y ◇ z)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = y ◇ (((y ◇ z) ◇ z) ◇ z)
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
  have apc15:=fun (q10 q11:G)=>by
    exact ((cg (fun t => q11 ◇ t) (cg (fun t => q10 ◇ t) (cg (fun t => t ◇ (q11 ◇ ((q10 ◇ q10) ◇ q10))) (apc5 q10 q10 q10 q10)))).symm).trans ((h q10 q11 ((q10 ◇ q10) ◇ q10)).symm)
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
  have apc36:=fun (q48 q49:G)=>by
    exact ((cg (fun t => (((q49 ◇ q49) ◇ q49) ◇ (q48 ◇ q48)) ◇ t) (cg (fun t => q49 ◇ t) (apc24 q49 q49))).symm).trans (((cg (fun t => (((q49 ◇ q49) ◇ q49) ◇ (q48 ◇ q48)) ◇ t) (cg (fun t => q49 ◇ t) (cg (fun t => q49 ◇ t) (apc19 q48 ((q49 ◇ q49) ◇ q49))))).symm).trans (apc15 q49 (((q49 ◇ q49) ◇ q49) ◇ (q48 ◇ q48))))
  have apc37:=fun (q50:G)=>by
    exact ((cg (fun t => ((q50 ◇ q50) ◇ ((q50 ◇ q50) ◇ q50)) ◇ t) (apc7 q50)).symm).trans (apc18 q50 ((q50 ◇ q50) ◇ ((q50 ◇ q50) ◇ q50)))
  have apc41:=fun (q51 q52:G)=>by
    exact (((apc35 q51 q52 q51).symm).trans (((cg (fun t => (q51 ◇ q51) ◇ t) (cg (fun t => t ◇ q52) (apc23 q51 q52))).symm).trans (apc34 q52 q51))).symm
  have apc50:=fun (q53 q54 q55:G)=>by
    exact ((cg (fun t => t ◇ (q54 ◇ ((q54 ◇ q55) ◇ q55))) (cg (fun t => t ◇ q55) (apc23 q53 q55))).symm).trans (apc8 q54 q55)
  have apc51:=fun (q56 q57 q58:G)=>by
    exact ((cg (fun t => t ◇ (q58 ◇ q58)) (cg (fun t => t ◇ (q57 ◇ q57)) (cg (fun t => t ◇ q58) (apc23 q56 q58)))).symm).trans (apc36 q57 q58)
  have apc56:=fun (q59 q60:G)=>by
    exact ((cg (fun t => t ◇ q60) (cg (fun t => t ◇ ((q60 ◇ q60) ◇ q60)) (apc23 q59 q60))).symm).trans (apc37 q60)
  have apc57:=fun (q61 q62:G)=>by
    exact (((((((cg (fun t => ((((q61 ◇ q61) ◇ ((q62 ◇ q62) ◇ q62)) ◇ ((q62 ◇ q62) ◇ ((q62 ◇ q62) ◇ q62))) ◇ q62) ◇ t) (cg (fun t => ((q61 ◇ q61) ◇ ((q62 ◇ q62) ◇ q62)) ◇ t) (apc56 q61 q62))).trans (cg (fun t => t ◇ (((q61 ◇ q61) ◇ ((q62 ◇ q62) ◇ q62)) ◇ ((q62 ◇ q62) ◇ ((q62 ◇ q62) ◇ q62)))) (cg (fun t => t ◇ q62) (apc33 q62 q61 ((q62 ◇ q62) ◇ q62))))).trans (cg (fun t => t ◇ (((q61 ◇ q61) ◇ ((q62 ◇ q62) ◇ q62)) ◇ ((q62 ◇ q62) ◇ ((q62 ◇ q62) ◇ q62)))) (cg (fun t => t ◇ q62) (apc33 q62 q62 q62)))).trans (cg (fun t => ((q62 ◇ q62) ◇ q62) ◇ t) (apc33 q62 q61 ((q62 ◇ q62) ◇ q62)))).trans (cg (fun t => ((q62 ◇ q62) ◇ q62) ◇ t) (apc33 q62 q62 q62))).symm).trans (((cg (fun t => t ◇ (((q61 ◇ q61) ◇ ((q62 ◇ q62) ◇ q62)) ◇ (((q61 ◇ q61) ◇ ((q62 ◇ q62) ◇ q62)) ◇ q62))) (cg (fun t => t ◇ q62) (cg (fun t => ((q61 ◇ q61) ◇ ((q62 ◇ q62) ◇ q62)) ◇ t) (apc56 q61 q62)))).symm).trans (apc0 q62 ((q61 ◇ q61) ◇ ((q62 ◇ q62) ◇ q62))))).symm
  have apc62:=fun (q63 q64:G)=>by
    exact ((cg (fun t => q64 ◇ t) (cg (fun t => q63 ◇ t) (apc20 q64 (q63 ◇ q64)))).symm).trans ((h q63 q64 q64).symm)
  have apc63:=fun (q65 q66 q67:G)=>by
    exact ((cg (fun t => q67 ◇ t) (cg (fun t => q66 ◇ t) (cg (fun t => t ◇ (q66 ◇ q67)) (apc23 q65 (q66 ◇ q67))))).symm).trans (apc62 q66 q67)
  have apc81:=fun (q68 q69 q70:G)=>by
    exact (((cg (fun t => t ◇ ((q69 ◇ q69) ◇ q70)) (apc23 q68 q70)).symm).trans ((apc41 q69 q70).symm)).trans (apc57 q70 q70)
  have apc88:=fun (q71 q72 q73 q74:G)=>by
    exact ((cg (fun t => (((q72 ◇ q72) ◇ q74) ◇ (q73 ◇ q73)) ◇ t) (apc23 q71 q74)).symm).trans (apc51 q72 q73 q74)
  have apc89:=fun (q75 q76 q77:G)=>by
    exact ((cg (fun t => ((q77 ◇ q75) ◇ ((q76 ◇ q76) ◇ q75)) ◇ t) (cg (fun t => q77 ◇ t) ((h q77 (q76 ◇ q76) q75).symm))).symm).trans (apc63 q76 q77 ((q77 ◇ q75) ◇ ((q76 ◇ q76) ◇ q75)))
  have apc90:=fun (q78 q79 q80:G)=>by
    exact (((((((cg (fun t => t ◇ (((q80 ◇ q78) ◇ ((q79 ◇ q79) ◇ q78)) ◇ ((q80 ◇ q78) ◇ ((q79 ◇ q79) ◇ q78)))) (cg (fun t => q80 ◇ t) (apc22 q80 q78))).trans (cg (fun t => t ◇ (((q80 ◇ q78) ◇ ((q79 ◇ q79) ◇ q78)) ◇ ((q80 ◇ q78) ◇ ((q79 ◇ q79) ◇ q78)))) (apc20 q78 q80))).trans (apc20 ((q80 ◇ q78) ◇ ((q79 ◇ q79) ◇ q78)) ((q80 ◇ q80) ◇ q80))).trans (cg (fun t => t ◇ ((q80 ◇ q80) ◇ q80)) (apc33 q80 q80 q80))).trans (apc81 q80 q80 q80)).symm).trans (((cg (fun t => t ◇ (((q80 ◇ q78) ◇ ((q79 ◇ q79) ◇ q78)) ◇ ((q80 ◇ q78) ◇ ((q79 ◇ q79) ◇ q78)))) (cg (fun t => t ◇ ((q78 ◇ q78) ◇ (q80 ◇ q80))) (apc89 q78 q79 q80))).symm).trans (apc89 (q80 ◇ q80) q78 ((q80 ◇ q78) ◇ ((q79 ◇ q79) ◇ q78))))).symm
  have apc91:=fun (q81 q82 q83:G)=>by
    exact ((cg (fun t => ((q82 ◇ q82) ◇ q81) ◇ t) (cg (fun t => (q83 ◇ q81) ◇ t) (apc89 q81 q82 q83))).symm).trans (apc30 q83 (q83 ◇ q81) ((q82 ◇ q82) ◇ q81))
  have apc92:=fun (q84 q85 q86:G)=>by
    exact (((cg (fun t => ((q86 ◇ q86) ◇ q85) ◇ t) (apc0 q85 q84)).symm).trans (apc91 q85 q86 (q84 ◇ (q84 ◇ q85)))).symm
  have apc93:=fun (q84 q85 q86:G)=>by
    exact ((apc92 q84 q85 q86).symm).trans (apc92 q84 q85 q84)
  have apc94:=fun (q87 q88:G)=>by
    exact ((apc93 q87 q88 q88).symm).trans (((cg (fun t => t ◇ q87) ((apc26 q87 q88).symm)).symm).trans ((apc92 q87 q88 q87).symm))
  have apc95:=fun (q89 q90:G)=>by
    exact ((((cg (fun t => t ◇ q90) (apc28 q89 (q89 ◇ q89))).symm).trans (apc93 q90 (((q89 ◇ q89) ◇ q89) ◇ (q89 ◇ ((q89 ◇ q89) ◇ q89))) q89)).trans ((cg (fun t => t ◇ q90) (cg (fun t => (q90 ◇ q90) ◇ t) (cg (fun t => ((q89 ◇ q89) ◇ q89) ◇ t) (apc24 q89 q89)))).trans (cg (fun t => t ◇ q90) (cg (fun t => (q90 ◇ q90) ◇ t) (apc25 q89 q89))))).symm
  have apc96:=fun (q91 q92:G)=>by
    exact ((((cg (fun t => t ◇ q92) (apc28 q91 (q92 ◇ q92))).symm).trans (apc94 q92 (((q91 ◇ q91) ◇ q91) ◇ (q91 ◇ ((q92 ◇ q92) ◇ q91))))).trans ((((cg (fun t => t ◇ (((q91 ◇ q91) ◇ q91) ◇ (q91 ◇ ((q92 ◇ q92) ◇ q91)))) (cg (fun t => q92 ◇ t) (cg (fun t => q92 ◇ t) (cg (fun t => ((q91 ◇ q91) ◇ q91) ◇ t) (apc24 q92 q91))))).trans (cg (fun t => t ◇ (((q91 ◇ q91) ◇ q91) ◇ (q91 ◇ ((q92 ◇ q92) ◇ q91)))) (cg (fun t => q92 ◇ t) (cg (fun t => q92 ◇ t) (apc25 q91 q91))))).trans (cg (fun t => (q92 ◇ (q92 ◇ q91)) ◇ t) (cg (fun t => ((q91 ◇ q91) ◇ q91) ◇ t) (apc24 q92 q91)))).trans (cg (fun t => (q92 ◇ (q92 ◇ q91)) ◇ t) (apc25 q91 q91)))).symm
  have apc97:=fun (q93 q94 q95:G)=>by
    exact (((cg (fun t => t ◇ q95) (cg (fun t => t ◇ q94) (apc23 q93 q95))).symm).trans (apc95 q94 q95)).symm
  have apc103:=fun (q96 q97:G)=>by
    exact (((apc20 (q97 ◇ q96) q97).symm).trans ((((cg (fun t => t ◇ ((q97 ◇ q96) ◇ (q97 ◇ q96))) ((h q97 q97 q96).symm)).symm).trans (apc96 ((q97 ◇ q96) ◇ (q97 ◇ q96)) q97)).trans ((cg (fun t => t ◇ q97) (cg (fun t => t ◇ ((q97 ◇ q96) ◇ (q97 ◇ q96))) (apc22 (q97 ◇ q96) (q97 ◇ q96)))).trans (cg (fun t => t ◇ q97) (apc22 (q97 ◇ q96) (q97 ◇ q96)))))).symm
  have apc104:=fun (q98 q99:G)=>by
    exact (((apc33 q98 q99 q99).symm).trans ((((cg (fun t => t ◇ ((q98 ◇ q98) ◇ q99)) (apc103 q98 q99)).symm).trans (apc90 q99 q98 ((q99 ◇ q98) ◇ (q99 ◇ q98)))).trans ((((cg (fun t => t ◇ (((q99 ◇ q98) ◇ (q99 ◇ q98)) ◇ ((q99 ◇ q98) ◇ (q99 ◇ q98)))) (cg (fun t => t ◇ ((q99 ◇ q98) ◇ (q99 ◇ q98))) (apc22 (q99 ◇ q98) (q99 ◇ q98)))).trans (cg (fun t => t ◇ (((q99 ◇ q98) ◇ (q99 ◇ q98)) ◇ ((q99 ◇ q98) ◇ (q99 ◇ q98)))) (apc22 (q99 ◇ q98) (q99 ◇ q98)))).trans (cg (fun t => ((q99 ◇ q98) ◇ (q99 ◇ q98)) ◇ t) (apc22 (q99 ◇ q98) (q99 ◇ q98)))).trans (apc22 (q99 ◇ q98) (q99 ◇ q98))))).symm
  have apc105:=fun (q100 q101 q102:G)=>by
    exact (((cg (fun t => t ◇ (q101 ◇ q100)) (apc104 q100 q101)).symm).trans (apc26 q102 (q101 ◇ q100))).symm
  have apc111:=fun (q103 q104 q105:G)=>by
    exact (((cg (fun t => (q105 ◇ q105) ◇ t) (apc91 q103 q103 q104)).symm).trans (apc105 ((q104 ◇ q103) ◇ q104) ((q103 ◇ q103) ◇ q103) q105)).trans ((cg (fun t => t ◇ (((q103 ◇ q103) ◇ q103) ◇ ((q104 ◇ q103) ◇ q104))) (apc33 q103 q103 q103)).trans (cg (fun t => (q103 ◇ q103) ◇ t) (apc91 q103 q103 q104)))
  have apc122:=fun (q106 q107 q108:G)=>by
    exact ((cg (fun t => (((q106 ◇ q106) ◇ q108) ◇ (q107 ◇ q107)) ◇ t) (apc88 ((((q106 ◇ q106) ◇ q108) ◇ (q107 ◇ q107)) ◇ q106) q106 q107 q108)).symm).trans ((h (((q106 ◇ q106) ◇ q108) ◇ (q107 ◇ q107)) (((q106 ◇ q106) ◇ q108) ◇ (q107 ◇ q107)) q106).symm)
  have apc124:=fun (q109 q110 q111 q112:G)=>by
    exact (((apc122 q110 q109 q112).symm).trans (((cg (fun t => t ◇ q112) (cg (fun t => ((q110 ◇ q110) ◇ q112) ◇ t) (apc23 q109 q111))).symm).trans (apc122 q110 q111 q112))).symm
  have apc125:=fun (q109 q110 q111 q112:G)=>by
    exact (((apc124 q109 q110 q109 q112).symm).trans (apc124 q110 q110 q109 q112)).symm
  have apc137:=fun (q113 q114:G)=>by
    exact ((cg (fun t => (q114 ◇ q113) ◇ t) (apc111 q114 (q114 ◇ q113) q113)).symm).trans ((((cg (fun t => t ◇ ((q113 ◇ q113) ◇ ((q114 ◇ q113) ◇ q114))) (apc91 q113 q113 q114)).symm).trans (apc90 ((q114 ◇ q113) ◇ q114) q113 ((q113 ◇ q113) ◇ q113))).trans ((((cg (fun t => t ◇ (((q113 ◇ q113) ◇ q113) ◇ ((q113 ◇ q113) ◇ q113))) (cg (fun t => t ◇ ((q113 ◇ q113) ◇ q113)) (apc33 q113 q113 q113))).trans (cg (fun t => t ◇ (((q113 ◇ q113) ◇ q113) ◇ ((q113 ◇ q113) ◇ q113))) (apc81 q113 q113 q113))).trans (cg (fun t => (((q113 ◇ q113) ◇ q113) ◇ (q113 ◇ q113)) ◇ t) (apc33 q113 q113 q113))).trans (apc88 q113 q113 q113 q113)))
  have apc138:=fun (q115 q116 q117:G)=>by
    exact ((cg (fun t => q116 ◇ t) (cg (fun t => (q117 ◇ q117) ◇ t) (cg (fun t => t ◇ q117) (apc29 q115 q117 q116)))).symm).trans (((cg (fun t => t ◇ ((q117 ◇ q117) ◇ ((q117 ◇ (q116 ◇ ((q115 ◇ q115) ◇ (q117 ◇ q116)))) ◇ q117))) (apc29 q115 q117 q116)).symm).trans (apc137 (q116 ◇ ((q115 ◇ q115) ◇ (q117 ◇ q116))) q117))
  have apc140:=fun (q118 q119 q120:G)=>by
    exact ((cg (fun t => q119 ◇ t) (cg (fun t => (q120 ◇ q120) ◇ t) (cg (fun t => t ◇ q120) (apc63 q118 q119 q120)))).symm).trans (((cg (fun t => t ◇ ((q120 ◇ q120) ◇ ((q120 ◇ (q119 ◇ ((q118 ◇ q118) ◇ (q119 ◇ q120)))) ◇ q120))) (apc63 q118 q119 q120)).symm).trans (apc137 (q119 ◇ ((q118 ◇ q118) ◇ (q119 ◇ q120))) q120))
  have apc141:=fun (q121 q122 q123:G)=>by
    exact (((cg (fun t => q123 ◇ t) (cg (fun t => t ◇ q121) (apc104 ((q121 ◇ q121) ◇ (q123 ◇ q121)) q121))).symm).trans ((((cg (fun t => q123 ◇ t) (cg (fun t => ((q121 ◇ ((q121 ◇ q121) ◇ (q123 ◇ q121))) ◇ (q121 ◇ ((q121 ◇ q121) ◇ (q123 ◇ q121)))) ◇ t) (apc29 q121 q123 q121))).symm).trans (apc140 q122 q123 (q121 ◇ ((q121 ◇ q121) ◇ (q123 ◇ q121))))).trans (cg (fun t => q123 ◇ t) (cg (fun t => (q122 ◇ q122) ◇ t) (apc29 q121 q123 q121))))).symm
  have apc143:=fun (q124 q125 q126 q127:G)=>by
    exact (((cg (fun t => q126 ◇ t) (cg (fun t => t ◇ (q126 ◇ q127)) (apc23 q124 q127))).symm).trans (apc138 q125 q126 q127)).symm
  have apc147:=fun (q128 q129:G)=>by
    exact ((((cg (fun t => ((q128 ◇ q128) ◇ q129) ◇ t) (cg (fun t => t ◇ (((q128 ◇ q128) ◇ q129) ◇ ((q128 ◇ q128) ◇ q129))) (apc33 q128 q128 q129))).trans (cg (fun t => ((q128 ◇ q128) ◇ q129) ◇ t) (cg (fun t => (q129 ◇ q129) ◇ t) (apc33 q128 q128 q129)))).trans (cg (fun t => ((q128 ◇ q128) ◇ q129) ◇ t) (apc104 q129 q129))).symm).trans ((apc138 ((q128 ◇ q128) ◇ q129) ((q128 ◇ q128) ◇ q129) ((q128 ◇ q128) ◇ q129)).trans ((apc125 (((q128 ◇ q128) ◇ q129) ◇ ((q128 ◇ q128) ◇ q129)) q128 q128 q129).symm))
  have apc158:=fun (q130 q131:G)=>by
    exact ((apc138 q130 q131 q130).trans (apc141 (q130 ◇ q131) q130 q131)).trans (cg (fun t => q131 ◇ t) (cg (fun t => t ◇ (q130 ◇ q131)) (apc104 q131 q130)))
  have apc159:=fun (q132 q133:G)=>by
    exact ((((cg (fun t => (q133 ◇ ((q132 ◇ q132) ◇ (q132 ◇ q133))) ◇ t) (cg (fun t => (q133 ◇ q133) ◇ t) (cg (fun t => t ◇ q133) (apc158 q132 q133)))).trans (apc137 ((q132 ◇ q132) ◇ (q132 ◇ q133)) q133)).symm).trans (((cg (fun t => t ◇ ((q133 ◇ q133) ◇ ((q133 ◇ ((q132 ◇ q132) ◇ (q133 ◇ q132))) ◇ q133))) (apc158 q132 q133)).symm).trans (apc137 ((q132 ◇ q132) ◇ (q133 ◇ q132)) q133))).symm
  have apc160:=fun (q134 q135:G)=>by
    exact ((apc88 q134 q135 q134 (q135 ◇ q134)).symm).trans (((cg (fun t => t ◇ (q134 ◇ q134)) (cg (fun t => t ◇ (q134 ◇ q134)) (apc159 q135 q134))).symm).trans (apc88 q134 q135 q134 (q134 ◇ q135)))
  have apc161:=fun (q98 q99 q134 q135:G)=>by
    exact (((cg (fun t => t ◇ (q99 ◇ q98)) (apc160 q98 q99)).trans (cg (fun t => (q98 ◇ q99) ◇ t) (apc160 q98 q99))).symm).trans (apc104 q98 q99)
  have apc162:=fun (q134 q135 q91 q92:G)=>by
    exact (((cg (fun t => t ◇ q91) (cg (fun t => q92 ◇ t) (apc160 q91 q92))).trans (cg (fun t => t ◇ q91) (apc160 (q91 ◇ q92) q92))).symm).trans (apc96 q91 q92)
  have apc166:=fun (q136 q137 q138:G)=>by
    exact (((((((cg (fun t => q137 ◇ t) (cg (fun t => t ◇ (q138 ◇ q137)) (cg (fun t => t ◇ (q138 ◇ q137)) (apc160 q137 q138)))).trans (cg (fun t => q137 ◇ t) (cg (fun t => t ◇ (q138 ◇ q137)) (cg (fun t => (q137 ◇ q138) ◇ t) (apc160 q137 q138))))).trans (cg (fun t => q137 ◇ t) (cg (fun t => ((q137 ◇ q138) ◇ (q137 ◇ q138)) ◇ t) (apc160 q137 q138)))).trans (cg (fun t => q137 ◇ t) (cg (fun t => t ◇ (q137 ◇ q138)) (apc161 q137 q138 ((q137 ◇ q138) ◇ (q137 ◇ q138)) ((q137 ◇ q138) ◇ (q137 ◇ q138)))))).trans (cg (fun t => q137 ◇ t) (apc160 (q137 ◇ q138) (q138 ◇ q138)))).trans (apc160 ((q137 ◇ q138) ◇ (q138 ◇ q138)) q137)).symm).trans ((((cg (fun t => q137 ◇ t) ((apc26 q136 (q138 ◇ q137)).symm)).symm).trans (apc143 q136 q136 q137 q138)).trans (apc160 ((q136 ◇ q136) ◇ (q137 ◇ q138)) q137))
  have apc169:=fun (q139 q140 q141:G)=>by
    exact (((((cg (fun t => q139 ◇ t) (cg (fun t => (q141 ◇ q141) ◇ t) (apc160 ((q139 ◇ q140) ◇ q140) q139))).trans (cg (fun t => q139 ◇ t) (cg (fun t => (q141 ◇ q141) ◇ t) (apc162 (((q139 ◇ q140) ◇ q140) ◇ q139) (((q139 ◇ q140) ◇ q140) ◇ q139) q139 q140)))).trans (cg (fun t => q139 ◇ t) (apc160 (((q139 ◇ q139) ◇ q139) ◇ q140) (q141 ◇ q141)))).trans (apc160 ((((q139 ◇ q139) ◇ q139) ◇ q140) ◇ (q141 ◇ q141)) q139)).symm).trans ((((cg (fun t => t ◇ ((q141 ◇ q141) ◇ (q139 ◇ ((q139 ◇ q140) ◇ q140)))) (apc50 q139 q139 q140)).symm).trans (apc90 (q139 ◇ ((q139 ◇ q140) ◇ q140)) q141 ((q139 ◇ q139) ◇ q140))).trans (((((cg (fun t => t ◇ (((q139 ◇ q139) ◇ q140) ◇ ((q139 ◇ q139) ◇ q140))) (cg (fun t => t ◇ ((q139 ◇ q139) ◇ q140)) (apc161 (q139 ◇ q139) q140 (((q139 ◇ q139) ◇ q140) ◇ ((q139 ◇ q139) ◇ q140)) (((q139 ◇ q139) ◇ q140) ◇ ((q139 ◇ q139) ◇ q140))))).trans (cg (fun t => t ◇ (((q139 ◇ q139) ◇ q140) ◇ ((q139 ◇ q139) ◇ q140))) (apc160 ((q139 ◇ q139) ◇ q140) (q140 ◇ q140)))).trans (cg (fun t => t ◇ (((q139 ◇ q139) ◇ q140) ◇ ((q139 ◇ q139) ◇ q140))) (apc147 q139 q140))).trans (cg (fun t => (((q139 ◇ q139) ◇ q140) ◇ (q139 ◇ q139)) ◇ t) (apc161 (q139 ◇ q139) q140 (((q139 ◇ q139) ◇ q140) ◇ ((q139 ◇ q139) ◇ q140)) (((q139 ◇ q139) ◇ q140) ◇ ((q139 ◇ q139) ◇ q140))))).trans (apc88 q140 q139 q139 q140)))
  have apc184:=fun (q142 q143 q144:G)=>by
    exact (((((cg (fun t => t ◇ (q144 ◇ ((q142 ◇ q142) ◇ q142))) (cg (fun t => q142 ◇ t) (cg (fun t => (q142 ◇ q143) ◇ t) (apc160 q143 q144)))).trans (cg (fun t => (q142 ◇ ((q142 ◇ q143) ◇ (q143 ◇ q144))) ◇ t) (apc160 ((q142 ◇ q142) ◇ q142) q144))).trans (cg (fun t => t ◇ (((q142 ◇ q142) ◇ q142) ◇ q144)) (apc160 ((q142 ◇ q143) ◇ (q143 ◇ q144)) q142))).trans (apc160 (((q142 ◇ q142) ◇ q142) ◇ q144) (((q142 ◇ q143) ◇ (q143 ◇ q144)) ◇ q142))).symm).trans (((cg (fun t => (q142 ◇ ((q142 ◇ q143) ◇ (q144 ◇ q143))) ◇ t) (cg (fun t => q144 ◇ t) (apc20 (q142 ◇ ((q142 ◇ q143) ◇ (q144 ◇ q143))) q142))).symm).trans (apc17 q142 q143 q144 (q142 ◇ ((q142 ◇ q143) ◇ (q144 ◇ q143)))))
  have apc192:=fun (q145 q146 q147:G)=>by
    exact ((((cg (fun t => t ◇ q147) (cg (fun t => t ◇ (q145 ◇ q145)) (apc160 q145 q147))).trans (cg (fun t => t ◇ q147) (apc160 (q145 ◇ q145) (q145 ◇ q147)))).symm).trans (((apc166 (q147 ◇ q145) q147 q145).trans (apc97 q146 (q147 ◇ q145) q147)).trans ((cg (fun t => t ◇ q147) (cg (fun t => (q146 ◇ q146) ◇ t) (apc160 q145 q147))).trans (cg (fun t => t ◇ q147) (apc160 (q145 ◇ q147) (q146 ◇ q146)))))).symm
  have apc202:=fun (q148 q149 q150:G)=>by
    exact (((cg (fun t => (((q148 ◇ q148) ◇ q149) ◇ q150) ◇ t) (cg (fun t => q150 ◇ t) (apc160 q149 q150))).trans (cg (fun t => (((q148 ◇ q148) ◇ q149) ◇ q150) ◇ t) (apc160 (q149 ◇ q150) q150))).symm).trans (((cg (fun t => t ◇ (q150 ◇ (q150 ◇ q149))) (apc92 q150 q149 q148)).symm).trans (apc0 q149 q150))
  have apc206:=fun (q151 q152 q153:G)=>by
    exact (((((cg (fun t => (q153 ◇ q152) ◇ t) (cg (fun t => (q151 ◇ q151) ◇ t) (cg (fun t => t ◇ q153) (apc160 q152 q153)))).trans (cg (fun t => t ◇ ((q151 ◇ q151) ◇ ((q152 ◇ q153) ◇ q153))) (apc160 q152 q153))).trans (cg (fun t => (q152 ◇ q153) ◇ t) (apc160 ((q152 ◇ q153) ◇ q153) (q151 ◇ q151)))).trans (apc160 (((q152 ◇ q153) ◇ q153) ◇ (q151 ◇ q151)) (q152 ◇ q153))).symm).trans (((cg (fun t => (q153 ◇ q152) ◇ t) (cg (fun t => t ◇ ((q153 ◇ q152) ◇ q153)) (apc23 q151 q153))).symm).trans (apc137 q152 q153))
  have apc207:=fun (q154 q155:G)=>by
    exact ((((cg (fun t => t ◇ q154) (cg (fun t => t ◇ q155) (cg (fun t => t ◇ (q154 ◇ q155)) (apc161 q154 q155 ((q154 ◇ q155) ◇ (q154 ◇ q155)) ((q154 ◇ q155) ◇ (q154 ◇ q155)))))).trans (cg (fun t => t ◇ q154) (cg (fun t => t ◇ q155) (apc160 (q154 ◇ q155) (q155 ◇ q155))))).trans (cg (fun t => t ◇ q154) (apc192 q154 q155 q155))).symm).trans (((cg (fun t => ((((q154 ◇ q155) ◇ (q154 ◇ q155)) ◇ (q154 ◇ q155)) ◇ q155) ◇ t) (apc206 q155 q154 q155)).symm).trans (apc184 (q154 ◇ q155) q155 q155))
  have apc210:=fun (q156 q157 q158 q159:G)=>by
    exact ((cg (fun t => t ◇ q157) (cg (fun t => t ◇ (q159 ◇ q159)) (cg (fun t => t ◇ q158) (cg (fun t => t ◇ q157) (apc23 q156 q157))))).symm).trans (apc169 q157 q158 q159)
  have apc211:=fun (q160 q161:G)=>by
    exact (((((((((((((cg (fun t => q160 ◇ t) (cg (fun t => ((q161 ◇ q160) ◇ (q161 ◇ q160)) ◇ t) (cg (fun t => t ◇ (q161 ◇ q160)) (cg (fun t => (q161 ◇ q160) ◇ t) (cg (fun t => (q161 ◇ q161) ◇ t) (cg (fun t => t ◇ q161) (apc160 q160 q161))))))).trans (cg (fun t => q160 ◇ t) (cg (fun t => ((q161 ◇ q160) ◇ (q161 ◇ q160)) ◇ t) (cg (fun t => t ◇ (q161 ◇ q160)) (cg (fun t => t ◇ ((q161 ◇ q161) ◇ ((q160 ◇ q161) ◇ q161))) (apc160 q160 q161)))))).trans (cg (fun t => q160 ◇ t) (cg (fun t => ((q161 ◇ q160) ◇ (q161 ◇ q160)) ◇ t) (cg (fun t => t ◇ (q161 ◇ q160)) (cg (fun t => (q160 ◇ q161) ◇ t) (apc160 ((q160 ◇ q161) ◇ q161) (q161 ◇ q161))))))).trans (cg (fun t => q160 ◇ t) (cg (fun t => t ◇ (((q160 ◇ q161) ◇ (((q160 ◇ q161) ◇ q161) ◇ (q161 ◇ q161))) ◇ (q161 ◇ q160))) (cg (fun t => t ◇ (q161 ◇ q160)) (apc160 q160 q161))))).trans (cg (fun t => q160 ◇ t) (cg (fun t => t ◇ (((q160 ◇ q161) ◇ (((q160 ◇ q161) ◇ q161) ◇ (q161 ◇ q161))) ◇ (q161 ◇ q160))) (cg (fun t => (q160 ◇ q161) ◇ t) (apc160 q160 q161))))).trans (cg (fun t => q160 ◇ t) (cg (fun t => ((q160 ◇ q161) ◇ (q160 ◇ q161)) ◇ t) (cg (fun t => ((q160 ◇ q161) ◇ (((q160 ◇ q161) ◇ q161) ◇ (q161 ◇ q161))) ◇ t) (apc160 q160 q161))))).trans (cg (fun t => q160 ◇ t) (cg (fun t => ((q160 ◇ q161) ◇ (q160 ◇ q161)) ◇ t) (cg (fun t => t ◇ (q160 ◇ q161)) (apc160 (((q160 ◇ q161) ◇ q161) ◇ (q161 ◇ q161)) (q160 ◇ q161)))))).trans (cg (fun t => q160 ◇ t) (cg (fun t => ((q160 ◇ q161) ◇ (q160 ◇ q161)) ◇ t) (cg (fun t => t ◇ (q160 ◇ q161)) (apc206 q161 q160 q161))))).trans (cg (fun t => q160 ◇ t) (cg (fun t => ((q160 ◇ q161) ◇ (q160 ◇ q161)) ◇ t) (apc160 (q160 ◇ q161) q160)))).trans (cg (fun t => q160 ◇ t) (cg (fun t => t ◇ ((q160 ◇ q161) ◇ q160)) (apc161 q160 q161 ((q160 ◇ q161) ◇ (q160 ◇ q161)) ((q160 ◇ q161) ◇ (q160 ◇ q161)))))).trans (cg (fun t => q160 ◇ t) (apc160 ((q160 ◇ q161) ◇ q160) (q161 ◇ q161)))).trans (apc160 (((q160 ◇ q161) ◇ q160) ◇ (q161 ◇ q161)) q160)).symm).trans ((((cg (fun t => t ◇ (((q161 ◇ q160) ◇ (q161 ◇ q160)) ◇ (((q161 ◇ q160) ◇ ((q161 ◇ q161) ◇ ((q161 ◇ q160) ◇ q161))) ◇ (q161 ◇ q160)))) (apc137 q160 q161)).symm).trans (apc137 ((q161 ◇ q161) ◇ ((q161 ◇ q160) ◇ q161)) (q161 ◇ q160))).trans ((cg (fun t => (q161 ◇ q161) ◇ t) (cg (fun t => t ◇ q161) (apc160 q160 q161))).trans (apc160 ((q160 ◇ q161) ◇ q161) (q161 ◇ q161))))
  have apc222:=fun (q162 q163 q164:G)=>by
    exact (((((cg (fun t => t ◇ (((q162 ◇ q162) ◇ q163) ◇ q164)) (cg (fun t => t ◇ (((q163 ◇ q164) ◇ q164) ◇ ((q163 ◇ q164) ◇ q164))) (apc160 (((q162 ◇ q162) ◇ q163) ◇ q164) q164))).trans (cg (fun t => t ◇ (((q162 ◇ q162) ◇ q163) ◇ q164)) (cg (fun t => ((((q162 ◇ q162) ◇ q163) ◇ q164) ◇ q164) ◇ t) (apc161 (q163 ◇ q164) q164 (((q163 ◇ q164) ◇ q164) ◇ ((q163 ◇ q164) ◇ q164)) (((q163 ◇ q164) ◇ q164) ◇ ((q163 ◇ q164) ◇ q164)))))).trans (apc206 q164 ((q162 ◇ q162) ◇ q163) q164)).symm).trans ((((cg (fun t => t ◇ (((q162 ◇ q162) ◇ q163) ◇ q164)) (cg (fun t => t ◇ (((q163 ◇ q164) ◇ q164) ◇ ((q163 ◇ q164) ◇ q164))) (cg (fun t => t ◇ (((q162 ◇ q162) ◇ q163) ◇ q164)) (apc202 q162 q163 q164)))).symm).trans (apc211 (((q162 ◇ q162) ◇ q163) ◇ q164) ((q163 ◇ q164) ◇ q164))).trans (((cg (fun t => t ◇ (((q163 ◇ q164) ◇ q164) ◇ ((q163 ◇ q164) ◇ q164))) (cg (fun t => t ◇ ((q163 ◇ q164) ◇ q164)) (apc202 q162 q163 q164))).trans (cg (fun t => t ◇ (((q163 ◇ q164) ◇ q164) ◇ ((q163 ◇ q164) ◇ q164))) (apc160 ((q163 ◇ q164) ◇ q164) q164))).trans (cg (fun t => (((q163 ◇ q164) ◇ q164) ◇ q164) ◇ t) (apc161 (q163 ◇ q164) q164 (((q163 ◇ q164) ◇ q164) ◇ ((q163 ◇ q164) ◇ q164)) (((q163 ◇ q164) ◇ q164) ◇ ((q163 ◇ q164) ◇ q164))))))).symm
  have apc223:=fun (q165 q166 q167:G)=>by
    exact ((cg (fun t => t ◇ ((q166 ◇ q167) ◇ q167)) (apc222 q165 q166 q167)).symm).trans (apc206 q167 (q166 ◇ q167) q167)
  have apc224:=fun (q168 q169:G)=>by
    exact (((cg (fun t => t ◇ q169) (cg (fun t => t ◇ (q168 ◇ q168)) (apc160 q168 q169))).trans (apc192 q168 q168 q169)).symm).trans ((((cg (fun t => t ◇ q169) (cg (fun t => t ◇ (q168 ◇ q168)) (apc223 q168 q169 q168))).symm).trans (apc210 q168 q169 ((q169 ◇ q168) ◇ q168) q168)).trans (cg (fun t => t ◇ q168) (apc160 q168 q169)))
  have apc225:=fun (q154 q155 q168 q169:G)=>by
    exact ((cg (fun t => t ◇ q154) (apc224 q154 q155)).symm).trans (apc207 q154 q155)
  have apc226:=fun (q170 q171:G)=>by
    exact ((((apc225 q171 q170 q170 q170).symm).trans (apc160 q171 ((q171 ◇ q170) ◇ q171))).trans ((cg (fun t => q171 ◇ t) (cg (fun t => t ◇ q171) (apc160 q170 q171))).trans (apc160 ((q170 ◇ q171) ◇ q171) q171))).symm
  exact ((apc23 x y).symm).trans (congrArg (fun t => y ◇ t) (apc226 y z).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_6678_to_45156 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_6678_to_45156
