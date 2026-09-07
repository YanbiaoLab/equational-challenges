-- Equation41890 → Equation55199
-- Recorded verdict: true
-- Premise: x ◇ y = y ◇ (x ◇ (x ◇ (z ◇ y)))
-- Conclusion: x ◇ (y ◇ z) = x ◇ ((x ◇ z) ◇ z)
-- Original submission SHA-256: f747258c67552697b7f8422fe3040a8804d2a446cbfc5f4c1e7612caaf9032e0
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = y ◇ (x ◇ (x ◇ (z ◇ y)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ z) = x ◇ ((x ◇ z) ◇ z)
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
    exact ((cg (fun t => (q0 ◇ q1) ◇ t) ((h q1 q1 q0).symm)).symm).trans ((h q1 (q0 ◇ q1) q1).symm)
  have apc1:=fun (x y z:G)=>by
    exact ((h x y z).symm).trans (h x y x)
  have apc2:=fun (x y z:G)=>by
    exact ((h x y x).trans (apc1 x y x)).symm
  have apc3:=fun (q0 q2 q1:G)=>by
    exact ((cg (fun t => (q1 ◇ (q0 ◇ q2)) ◇ t) (cg (fun t => q2 ◇ t) ((h q1 q2 q0).symm))).symm).trans ((h q2 (q1 ◇ (q0 ◇ q2)) q1).symm)
  have apc4:=fun (q3 q4:G)=>by
    exact ((cg (fun t => q4 ◇ t) (cg (fun t => (q3 ◇ q4) ◇ t) (apc0 q3 q4))).symm).trans ((h (q3 ◇ q4) q4 q4).symm)
  have apc5:=fun (q5 q6:G)=>by
    exact ((((cg (fun t => (q6 ◇ (q5 ◇ q6)) ◇ t) (apc0 q6 q6)).trans (apc3 q5 q6 q6)).symm).trans ((((cg (fun t => t ◇ ((q6 ◇ q6) ◇ (q6 ◇ q6))) (apc0 q5 q6)).symm).trans (apc0 (q5 ◇ q6) (q6 ◇ q6))).trans (cg (fun t => (q6 ◇ q6) ◇ t) (apc0 q5 q6)))).symm
  have apc6:=fun (q7:G)=>by
    exact (((apc2 q7 q7 (q7 ◇ (q7 ◇ (q7 ◇ (q7 ◇ q7))))).symm).trans (((cg (fun t => q7 ◇ t) (apc5 q7 q7)).symm).trans (apc4 q7 q7))).symm
  have apc7:=fun (q8 q9:G)=>by
    exact ((cg (fun t => q9 ◇ t) (cg (fun t => q8 ◇ t) (cg (fun t => q8 ◇ t) (apc6 q9)))).symm).trans ((h q8 q9 (q9 ◇ q9)).symm)
  have apc9:=fun (q10:G)=>by
    exact (((cg (fun t => t ◇ (q10 ◇ q10)) (apc0 q10 q10)).symm).trans (apc6 (q10 ◇ q10))).trans (apc0 q10 q10)
  have apc11:=fun (q3 q11 q12:G)=>by
    exact ((cg (fun t => (q11 ◇ q11) ◇ t) (cg (fun t => q12 ◇ t) (cg (fun t => q12 ◇ t) (apc0 q3 q11)))).symm).trans ((h q12 (q11 ◇ q11) (q3 ◇ q11)).symm)
  have apc15:=fun (q13 q14:G)=>by
    exact (((cg (fun t => (q13 ◇ (q13 ◇ (q13 ◇ q14))) ◇ t) (cg (fun t => q14 ◇ t) (cg (fun t => q14 ◇ t) (apc2 q13 q14 q13)))).symm).trans (apc2 q14 (q13 ◇ (q13 ◇ (q13 ◇ q14))) q13)).trans (apc2 q13 q14 (q14 ◇ (q13 ◇ (q13 ◇ (q13 ◇ q14)))))
  have apc18:=fun (q15 q16:G)=>by
    exact (((cg (fun t => t ◇ ((q16 ◇ q16) ◇ (q16 ◇ (q15 ◇ q16)))) (apc0 q16 q16)).trans (cg (fun t => (q16 ◇ (q16 ◇ q16)) ◇ t) (apc5 q15 q16))).symm).trans ((((cg (fun t => ((q16 ◇ q16) ◇ (q16 ◇ q16)) ◇ t) (cg (fun t => (q16 ◇ q16) ◇ t) (apc0 q15 q16))).symm).trans (apc5 (q15 ◇ q16) (q16 ◇ q16))).trans ((cg (fun t => (q16 ◇ q16) ◇ t) (cg (fun t => (q16 ◇ q16) ◇ t) (apc0 q15 q16))).trans (cg (fun t => (q16 ◇ q16) ◇ t) (apc5 q15 q16))))
  have apc20:=fun (q9 q17:G)=>by
    exact (((cg (fun t => q9 ◇ t) (apc0 (q17 ◇ q9) (q17 ◇ q9))).symm).trans (((cg (fun t => q9 ◇ t) (cg (fun t => ((q17 ◇ q9) ◇ (q17 ◇ q9)) ◇ t) (apc6 (q17 ◇ q9)))).symm).trans ((h ((q17 ◇ q9) ◇ (q17 ◇ q9)) q9 q17).symm))).symm
  have apc21:=fun (q18 q0 q2 q1:G)=>by
    exact ((cg (fun t => (q18 ◇ (q18 ◇ (q0 ◇ q1))) ◇ t) (cg (fun t => q2 ◇ t) (cg (fun t => q2 ◇ t) ((h q18 q1 q0).symm)))).symm).trans ((h q2 (q18 ◇ (q18 ◇ (q0 ◇ q1))) q1).symm)
  have apc23:=fun (q19 q20:G)=>by
    exact ((((cg (fun t => (q20 ◇ (q20 ◇ (q19 ◇ q20))) ◇ t) (apc3 q20 q20 q20)).trans (apc21 q20 q19 q20 q20)).symm).trans ((((cg (fun t => (q20 ◇ (q20 ◇ (q19 ◇ q20))) ◇ t) (cg (fun t => (q20 ◇ (q20 ◇ q20)) ◇ t) (apc9 q20))).symm).trans (apc21 q20 q19 (q20 ◇ (q20 ◇ q20)) q20)).trans (apc18 q19 q20))).symm
  have apc24:=fun (q21 q22 q23:G)=>by
    exact ((cg (fun t => (q22 ◇ (q22 ◇ (q23 ◇ (q21 ◇ q22)))) ◇ t) ((h q22 q22 q21).symm)).symm).trans (apc21 q22 q23 q22 (q21 ◇ q22))
  have apc25:=fun (q24 q25:G)=>by
    exact ((((cg (fun t => (q24 ◇ q25) ◇ t) (apc23 q24 q25)).trans (apc2 q25 (q24 ◇ q25) ((q24 ◇ q25) ◇ (q25 ◇ (q25 ◇ (q25 ◇ (q24 ◇ q25))))))).symm).trans (((cg (fun t => (q24 ◇ q25) ◇ t) (cg (fun t => (q25 ◇ q25) ◇ t) (apc5 q24 q25))).symm).trans ((h (q25 ◇ q25) (q24 ◇ q25) q25).symm))).symm
  have apc26:=fun (q26 q27:G)=>by
    exact ((cg (fun t => q26 ◇ t) (apc5 q27 q26)).symm).trans ((((cg (fun t => q26 ◇ t) (cg (fun t => (q26 ◇ q26) ◇ t) (apc25 q27 q26))).symm).trans ((h (q26 ◇ q26) q26 q27).symm)).trans (apc6 q26))
  have apc27:=fun (q28 q29:G)=>by
    exact (((((cg (fun t => (q29 ◇ q29) ◇ t) (apc5 q29 (q28 ◇ q29))).trans (apc11 q28 q29 (q28 ◇ q29))).trans (apc0 q28 q29)).symm).trans (((cg (fun t => (q29 ◇ q29) ◇ t) (cg (fun t => ((q28 ◇ q29) ◇ (q28 ◇ q29)) ◇ t) (apc25 q29 (q28 ◇ q29)))).symm).trans (apc11 q28 q29 ((q28 ◇ q29) ◇ (q28 ◇ q29))))).symm
  have apc28:=fun (q30 q31:G)=>by
    exact ((((cg (fun t => q31 ◇ t) (apc25 q31 (q30 ◇ q31))).trans (apc4 q30 q31)).symm).trans (((cg (fun t => q31 ◇ t) (cg (fun t => ((q30 ◇ q31) ◇ (q30 ◇ q31)) ◇ t) (apc27 q30 q31))).symm).trans ((h ((q30 ◇ q31) ◇ (q30 ◇ q31)) q31 q31).symm))).symm
  have apc29:=fun (q32 q33:G)=>by
    exact ((cg (fun t => t ◇ (q33 ◇ (q32 ◇ q33))) (apc0 q33 q33)).symm).trans ((((cg (fun t => ((q33 ◇ q33) ◇ (q33 ◇ q33)) ◇ t) (apc0 q32 q33)).symm).trans (apc25 (q32 ◇ q33) (q33 ◇ q33))).trans ((cg (fun t => (q33 ◇ q33) ◇ t) (apc0 q32 q33)).trans (apc5 q32 q33)))
  have apc33:=fun (q34 q35 q36:G)=>by
    exact ((((cg (fun t => (q34 ◇ (q34 ◇ (q35 ◇ q36))) ◇ t) (apc5 q34 q36)).trans (apc21 q34 q35 q36 q36)).symm).trans (((cg (fun t => (q34 ◇ (q34 ◇ (q35 ◇ q36))) ◇ t) (cg (fun t => (q36 ◇ q36) ◇ t) (apc25 q34 q36))).symm).trans (apc21 q34 q35 (q36 ◇ q36) q36))).symm
  have apc34:=fun (q37 q38 q39:G)=>by
    exact ((cg (fun t => (q37 ◇ q38) ◇ t) (cg (fun t => q39 ◇ t) (cg (fun t => q39 ◇ t) (apc25 q37 q38)))).symm).trans ((h q39 (q37 ◇ q38) (q38 ◇ q38)).symm)
  have apc35:=fun (q40 q41:G)=>by
    exact (((cg (fun t => t ◇ (q41 ◇ (q41 ◇ (q40 ◇ q41)))) (cg (fun t => (q41 ◇ q41) ◇ t) (apc26 q41 q40))).trans (cg (fun t => t ◇ (q41 ◇ (q41 ◇ (q40 ◇ q41)))) (apc0 q41 q41))).symm).trans ((((cg (fun t => t ◇ (q41 ◇ (q41 ◇ (q40 ◇ q41)))) (cg (fun t => t ◇ (q41 ◇ (q41 ◇ (q41 ◇ (q40 ◇ q41))))) (apc26 q41 q40))).symm).trans (apc20 (q41 ◇ (q41 ◇ (q40 ◇ q41))) q41)).trans (((((((cg (fun t => (q41 ◇ (q41 ◇ (q40 ◇ q41))) ◇ t) (cg (fun t => (q41 ◇ (q41 ◇ (q41 ◇ (q40 ◇ q41)))) ◇ t) (cg (fun t => t ◇ (q41 ◇ (q41 ◇ (q41 ◇ (q40 ◇ q41))))) (apc26 q41 q40)))).trans (cg (fun t => (q41 ◇ (q41 ◇ (q40 ◇ q41))) ◇ t) (cg (fun t => (q41 ◇ (q41 ◇ (q41 ◇ (q40 ◇ q41)))) ◇ t) (cg (fun t => (q41 ◇ q41) ◇ t) (apc26 q41 q40))))).trans (cg (fun t => (q41 ◇ (q41 ◇ (q40 ◇ q41))) ◇ t) (cg (fun t => (q41 ◇ (q41 ◇ (q41 ◇ (q40 ◇ q41)))) ◇ t) (apc0 q41 q41)))).trans (cg (fun t => (q41 ◇ (q41 ◇ (q40 ◇ q41))) ◇ t) (cg (fun t => t ◇ (q41 ◇ (q41 ◇ q41))) (apc26 q41 q40)))).trans (cg (fun t => (q41 ◇ (q41 ◇ (q40 ◇ q41))) ◇ t) (apc5 q41 q41))).trans (apc21 q41 q40 q41 q41)).trans (apc26 q41 q40)))
  have apc36:=fun (q42 q43:G)=>by
    exact (((cg (fun t => (q43 ◇ q43) ◇ t) (cg (fun t => (q42 ◇ q43) ◇ t) (apc0 q42 q43))).symm).trans (apc33 (q42 ◇ q43) q43 q43)).trans ((cg (fun t => q43 ◇ t) (cg (fun t => (q42 ◇ q43) ◇ t) (apc0 q42 q43))).trans (apc4 q42 q43))
  have apc39:=fun (q44 q45:G)=>by
    exact ((cg (fun t => t ◇ (q44 ◇ q45)) (apc21 q44 q44 q44 q45)).symm).trans ((((cg (fun t => ((q44 ◇ (q44 ◇ (q44 ◇ q45))) ◇ (q44 ◇ (q44 ◇ (q44 ◇ q45)))) ◇ t) (apc2 q44 q45 q44)).symm).trans (apc25 q45 (q44 ◇ (q44 ◇ (q44 ◇ q45))))).trans (cg (fun t => (q44 ◇ (q44 ◇ (q44 ◇ q45))) ◇ t) (apc2 q44 q45 (q45 ◇ (q44 ◇ (q44 ◇ (q44 ◇ q45)))))))
  have apc40:=fun (q46 q47:G)=>by
    exact (((((((cg (fun t => (q46 ◇ q47) ◇ t) (cg (fun t => t ◇ ((q47 ◇ (q47 ◇ (q47 ◇ (q46 ◇ q47)))) ◇ (q47 ◇ (q46 ◇ q47)))) (cg (fun t => q47 ◇ t) (apc26 q47 q46)))).trans (cg (fun t => (q46 ◇ q47) ◇ t) (cg (fun t => (q47 ◇ (q47 ◇ q47)) ◇ t) (cg (fun t => t ◇ (q47 ◇ (q46 ◇ q47))) (apc26 q47 q46))))).trans (cg (fun t => (q46 ◇ q47) ◇ t) (cg (fun t => (q47 ◇ (q47 ◇ q47)) ◇ t) (apc5 q46 q47)))).trans (cg (fun t => (q46 ◇ q47) ◇ t) (apc35 q46 q47))).trans (apc0 q46 q47)).symm).trans ((((cg (fun t => (q46 ◇ q47) ◇ t) (cg (fun t => (q47 ◇ (q47 ◇ (q47 ◇ (q47 ◇ (q46 ◇ q47))))) ◇ t) (apc39 q47 (q46 ◇ q47)))).symm).trans (apc34 q46 q47 (q47 ◇ (q47 ◇ (q47 ◇ (q47 ◇ (q46 ◇ q47))))))).trans (cg (fun t => t ◇ (q46 ◇ q47)) (cg (fun t => q47 ◇ t) (apc26 q47 q46))))).symm
  have apc45:=fun (q48 q49 q50:G)=>by
    exact (((cg (fun t => t ◇ ((q48 ◇ (q48 ◇ (q49 ◇ q50))) ◇ (q48 ◇ (q48 ◇ (q49 ◇ q50))))) ((h q48 q50 q49).symm)).symm).trans (apc0 q50 (q48 ◇ (q48 ◇ (q49 ◇ q50))))).symm
  have apc46:=fun (q51 q52:G)=>by
    exact (((cg (fun t => (q51 ◇ (q51 ◇ (q51 ◇ q52))) ◇ t) (apc2 q51 q52 q51)).symm).trans (apc45 q51 q51 q52)).trans ((cg (fun t => (q51 ◇ q52) ◇ t) (apc21 q51 q51 q51 q52)).trans (apc2 q51 (q51 ◇ q52) ((q51 ◇ q52) ◇ (q51 ◇ (q51 ◇ (q51 ◇ (q51 ◇ q52)))))))
  have apc48:=fun (q44 q45 q51 q52:G)=>by
    exact (apc39 q44 q45).trans (apc46 q44 q45)
  have apc49:=fun (q53 q54:G)=>by
    exact ((((cg (fun t => q53 ◇ t) (apc46 q54 (q54 ◇ q53))).trans (apc2 q54 q53 (q53 ◇ (q54 ◇ (q54 ◇ (q54 ◇ q53)))))).symm).trans (((cg (fun t => q53 ◇ t) (cg (fun t => (q54 ◇ (q54 ◇ (q54 ◇ (q54 ◇ q53)))) ◇ t) (apc48 q54 q53 q53 q53))).symm).trans ((h (q54 ◇ (q54 ◇ (q54 ◇ (q54 ◇ q53)))) q53 q54).symm))).symm
  have apc53:=fun (q55 q56 q57:G)=>by
    exact ((((cg (fun t => (q55 ◇ (q55 ◇ (q56 ◇ q57))) ◇ t) (apc29 q55 q57)).trans (apc21 q55 q56 q57 q57)).symm).trans (((cg (fun t => (q55 ◇ (q55 ◇ (q56 ◇ q57))) ◇ t) (cg (fun t => (q57 ◇ (q57 ◇ q57)) ◇ t) (apc40 q55 q57))).symm).trans (apc21 q55 q56 (q57 ◇ (q57 ◇ q57)) q57))).symm
  have apc54:=fun (q42 q58 q59:G)=>by
    exact ((cg (fun t => t ◇ (q59 ◇ (q59 ◇ (q58 ◇ (q42 ◇ q58))))) (apc0 q58 q58)).symm).trans ((((cg (fun t => ((q58 ◇ q58) ◇ (q58 ◇ q58)) ◇ t) (cg (fun t => q59 ◇ t) (cg (fun t => q59 ◇ t) (apc0 q42 q58)))).symm).trans (apc33 q59 (q42 ◇ q58) (q58 ◇ q58))).trans ((cg (fun t => (q58 ◇ q58) ◇ t) (cg (fun t => q59 ◇ t) (cg (fun t => q59 ◇ t) (apc0 q42 q58)))).trans (apc11 q42 q58 q59)))
  have apc55:=fun (q60 q61:G)=>by
    exact ((((((((cg (fun t => ((q60 ◇ (q60 ◇ q60)) ◇ ((q60 ◇ (q60 ◇ q60)) ◇ (q60 ◇ (q60 ◇ q60)))) ◇ t) (cg (fun t => q61 ◇ t) (cg (fun t => q61 ◇ t) (apc2 q60 q60 (q60 ◇ (q60 ◇ (q60 ◇ (q60 ◇ q60)))))))).trans (cg (fun t => t ◇ (q61 ◇ (q61 ◇ (q60 ◇ q60)))) (cg (fun t => (q60 ◇ (q60 ◇ q60)) ◇ t) (apc3 q60 q60 q60)))).trans (cg (fun t => t ◇ (q61 ◇ (q61 ◇ (q60 ◇ q60)))) (apc53 q60 q60 q60))).trans (cg (fun t => t ◇ (q61 ◇ (q61 ◇ (q60 ◇ q60)))) (apc2 q60 q60 (q60 ◇ (q60 ◇ (q60 ◇ (q60 ◇ q60))))))).trans (apc33 q61 q60 q60)).trans (apc7 q61 q60)).symm).trans ((((cg (fun t => ((q60 ◇ (q60 ◇ q60)) ◇ ((q60 ◇ (q60 ◇ q60)) ◇ (q60 ◇ (q60 ◇ q60)))) ◇ t) (cg (fun t => q61 ◇ t) (cg (fun t => q61 ◇ t) (apc53 q60 q60 q60)))).symm).trans (apc54 q60 (q60 ◇ (q60 ◇ q60)) q61)).trans (cg (fun t => q61 ◇ t) (apc3 q60 q60 q60)))).symm
  have apc56:=fun (q62 q63:G)=>by
    exact (((apc55 q63 (q63 ◇ (q63 ◇ (q62 ◇ q63)))).symm).trans (apc21 q63 q62 q63 q63)).trans (apc26 q63 q62)
  have apc57:=fun (q64 q65:G)=>by
    exact (((((cg (fun t => (q65 ◇ q64) ◇ t) (apc21 q64 q64 q64 q64)).trans (cg (fun t => (q65 ◇ q64) ◇ t) (apc2 q64 q64 (q64 ◇ (q64 ◇ (q64 ◇ (q64 ◇ q64))))))).trans (apc0 q65 q64)).symm).trans ((((cg (fun t => t ◇ ((q64 ◇ (q64 ◇ (q64 ◇ q64))) ◇ (q64 ◇ (q64 ◇ (q64 ◇ q64))))) (apc55 q64 q65)).symm).trans (apc0 q65 (q64 ◇ (q64 ◇ (q64 ◇ q64))))).trans (cg (fun t => (q64 ◇ (q64 ◇ (q64 ◇ q64))) ◇ t) (apc55 q64 q65)))).symm
  have apc58:=fun (q66 q67:G)=>by
    exact ((cg (fun t => (q67 ◇ (q67 ◇ q67)) ◇ t) (cg (fun t => q66 ◇ t) (apc55 q67 q66))).symm).trans ((h q66 (q67 ◇ (q67 ◇ q67)) q67).symm)
  have apc59:=fun (q68 q69:G)=>by
    exact ((((cg (fun t => t ◇ (q68 ◇ (q68 ◇ q69))) (cg (fun t => (q69 ◇ (q69 ◇ q69)) ◇ t) (apc3 q69 q69 q69))).trans (cg (fun t => t ◇ (q68 ◇ (q68 ◇ q69))) (apc53 q69 q69 q69))).trans (cg (fun t => t ◇ (q68 ◇ (q68 ◇ q69))) (apc2 q69 q69 (q69 ◇ (q69 ◇ (q69 ◇ (q69 ◇ q69))))))).symm).trans ((((cg (fun t => ((q69 ◇ (q69 ◇ q69)) ◇ ((q69 ◇ (q69 ◇ q69)) ◇ (q69 ◇ (q69 ◇ q69)))) ◇ t) (cg (fun t => q68 ◇ t) (apc55 q69 q68))).symm).trans (apc53 q68 q69 (q69 ◇ (q69 ◇ q69)))).trans ((cg (fun t => (q69 ◇ (q69 ◇ q69)) ◇ t) (cg (fun t => q68 ◇ t) (apc55 q69 q68))).trans (apc58 q68 q69)))
  have apc62:=fun (q70 q71:G)=>by
    exact ((((cg (fun t => (q70 ◇ (q70 ◇ (q71 ◇ (q70 ◇ q70)))) ◇ t) (apc6 q70)).trans (apc24 q70 q70 q71)).symm).trans (((cg (fun t => (q70 ◇ (q70 ◇ (q71 ◇ (q70 ◇ q70)))) ◇ t) (apc36 q70 q70)).symm).trans (apc21 q70 q71 (q70 ◇ q70) (q70 ◇ q70)))).symm
  have apc63:=fun (q72 q73:G)=>by
    exact ((apc62 q72 q73).symm).trans ((h q72 (q72 ◇ q72) q73).symm)
  have apc67:=fun (q74 q75:G)=>by
    exact ((cg (fun t => t ◇ (q75 ◇ (q74 ◇ (q75 ◇ q75)))) (apc2 q75 q75 (q75 ◇ (q75 ◇ (q75 ◇ (q75 ◇ q75)))))).symm).trans (((cg (fun t => t ◇ (q75 ◇ (q74 ◇ (q75 ◇ q75)))) (cg (fun t => q75 ◇ t) (cg (fun t => q75 ◇ t) (apc63 q75 q74)))).symm).trans (apc49 (q75 ◇ (q74 ◇ (q75 ◇ q75))) q75))
  have apc72:=fun (q76 q77 q78:G)=>by
    exact ((cg (fun t => t ◇ (q78 ◇ (q76 ◇ (q76 ◇ (q77 ◇ q78))))) (apc26 q78 q76)).symm).trans (((cg (fun t => t ◇ (q78 ◇ (q76 ◇ (q76 ◇ (q77 ◇ q78))))) (cg (fun t => q78 ◇ t) (cg (fun t => q78 ◇ t) (cg (fun t => q78 ◇ t) ((h q76 q78 q77).symm))))).symm).trans (apc48 q78 (q76 ◇ (q76 ◇ (q77 ◇ q78))) q76 q76))
  have apc73:=fun (q79 q80 q81:G)=>by
    exact (((apc25 q79 q81).symm).trans (((cg (fun t => (q81 ◇ q81) ◇ t) ((h q79 q81 q80).symm)).symm).trans (apc72 q79 q80 q81))).symm
  have apc74:=fun (q76 q77 q78 q79 q80 q81:G)=>by
    exact (apc72 q76 q77 q78).trans (apc73 q76 q77 q78)
  have apc78:=fun (q82 q83 q84:G)=>by
    exact (((cg (fun t => q83 ◇ t) (apc48 q82 (q84 ◇ q83) ((q82 ◇ (q82 ◇ (q82 ◇ (q82 ◇ (q84 ◇ q83))))) ◇ (q82 ◇ (q84 ◇ q83))) ((q82 ◇ (q82 ◇ (q82 ◇ (q82 ◇ (q84 ◇ q83))))) ◇ (q82 ◇ (q84 ◇ q83))))).symm).trans (((cg (fun t => q83 ◇ t) (cg (fun t => (q82 ◇ (q82 ◇ (q82 ◇ (q82 ◇ (q84 ◇ q83))))) ◇ t) (apc49 (q84 ◇ q83) q82))).symm).trans ((h (q82 ◇ (q82 ◇ (q82 ◇ (q82 ◇ (q84 ◇ q83))))) q83 q84).symm))).symm
  have apc79:=fun (q85 q86:G)=>by
    exact (((cg (fun t => t ◇ (q86 ◇ (q86 ◇ q85))) (apc26 q85 q86)).trans (apc59 q86 q85)).symm).trans ((((cg (fun t => t ◇ (q86 ◇ (q86 ◇ q85))) (cg (fun t => q85 ◇ t) (cg (fun t => q85 ◇ t) (cg (fun t => q85 ◇ t) (apc2 q86 q85 q85))))).symm).trans (apc78 q85 (q86 ◇ (q86 ◇ q85)) q86)).trans ((cg (fun t => (q86 ◇ (q86 ◇ q85)) ◇ t) (cg (fun t => q85 ◇ t) (apc2 q86 q85 (q85 ◇ (q86 ◇ (q86 ◇ (q86 ◇ q85))))))).trans (apc3 q86 q85 q86)))
  have apc80:=fun (q87 q88 q89:G)=>by
    exact ((cg (fun t => t ◇ (q89 ◇ (q87 ◇ q88))) (apc26 q88 q89)).symm).trans ((((cg (fun t => t ◇ (q89 ◇ (q87 ◇ q88))) (cg (fun t => q88 ◇ t) (cg (fun t => q88 ◇ t) (cg (fun t => q88 ◇ t) ((h q89 q88 q87).symm))))).symm).trans (apc78 q88 (q89 ◇ (q87 ◇ q88)) q89)).trans ((cg (fun t => (q89 ◇ (q87 ◇ q88)) ◇ t) (apc73 q89 q87 q88)).trans (apc3 q87 q88 q89)))
  have apc83:=fun (q90 q91 q92:G)=>by
    exact ((cg (fun t => (q91 ◇ (q91 ◇ (q90 ◇ q91))) ◇ t) (cg (fun t => q92 ◇ t) (cg (fun t => q92 ◇ t) (apc15 q90 q91)))).symm).trans ((h q92 (q91 ◇ (q91 ◇ (q90 ◇ q91))) (q90 ◇ (q90 ◇ (q90 ◇ q91)))).symm)
  have apc84:=fun (q93 q94 q95:G)=>by
    exact ((((((cg (fun t => t ◇ (q95 ◇ (q95 ◇ (q93 ◇ q94)))) (apc26 (q94 ◇ (q94 ◇ (q93 ◇ q94))) q95)).trans (cg (fun t => t ◇ (q95 ◇ (q95 ◇ (q93 ◇ q94)))) (apc83 q93 q94 q94))).trans (cg (fun t => t ◇ (q95 ◇ (q95 ◇ (q93 ◇ q94)))) (apc26 q94 q93))).trans (apc33 q95 q93 q94)).symm).trans ((((cg (fun t => t ◇ (q95 ◇ (q95 ◇ (q93 ◇ q94)))) (cg (fun t => (q94 ◇ (q94 ◇ (q93 ◇ q94))) ◇ t) (cg (fun t => (q94 ◇ (q94 ◇ (q93 ◇ q94))) ◇ t) (cg (fun t => (q94 ◇ (q94 ◇ (q93 ◇ q94))) ◇ t) (apc83 q93 q94 q95))))).symm).trans (apc49 (q95 ◇ (q95 ◇ (q93 ◇ q94))) (q94 ◇ (q94 ◇ (q93 ◇ q94))))).trans (apc83 q93 q94 q95))).symm
  have apc85:=fun (q96 q97:G)=>by
    exact ((((cg (fun t => t ◇ (q97 ◇ (q96 ◇ q97))) (apc26 q97 q96)).trans (apc80 q96 q97 q97)).symm).trans (((cg (fun t => t ◇ (q97 ◇ (q96 ◇ q97))) (apc83 q96 q97 q97)).symm).trans (apc28 q97 (q97 ◇ (q96 ◇ q97))))).symm
  have apc86:=fun (q98 q99:G)=>by
    exact ((cg (fun t => q98 ◇ t) (cg (fun t => (q99 ◇ (q99 ◇ (q99 ◇ q98))) ◇ t) (apc46 q99 q98))).symm).trans ((h (q99 ◇ (q99 ◇ (q99 ◇ q98))) q98 q99).symm)
  have apc87:=fun (q100 q101:G)=>by
    exact ((((((cg (fun t => (q100 ◇ (q100 ◇ (q101 ◇ q101))) ◇ t) (cg (fun t => (q101 ◇ (q101 ◇ (q100 ◇ q101))) ◇ t) (cg (fun t => q101 ◇ t) (apc7 q100 q101)))).trans (cg (fun t => (q100 ◇ (q100 ◇ (q101 ◇ q101))) ◇ t) (apc85 q100 q101))).trans (apc21 q100 q101 q101 q101)).trans (apc7 q100 q101)).symm).trans ((((cg (fun t => (q100 ◇ (q100 ◇ (q101 ◇ q101))) ◇ t) (cg (fun t => t ◇ (q101 ◇ (q101 ◇ (q100 ◇ (q100 ◇ (q101 ◇ q101)))))) (cg (fun t => q101 ◇ t) (cg (fun t => q101 ◇ t) (apc7 q100 q101))))).symm).trans (apc86 (q100 ◇ (q100 ◇ (q101 ◇ q101))) q101)).trans ((cg (fun t => t ◇ (q100 ◇ (q100 ◇ (q101 ◇ q101)))) (cg (fun t => q101 ◇ t) (cg (fun t => q101 ◇ t) (apc7 q100 q101)))).trans (apc21 q101 q100 q100 q101)))).symm
  have apc88:=fun (q102 q103:G)=>by
    exact (((cg (fun t => q103 ◇ t) (cg (fun t => (q102 ◇ (q102 ◇ (q102 ◇ q103))) ◇ t) (apc46 q102 q103))).trans (apc86 q103 q102)).symm).trans ((((cg (fun t => q103 ◇ t) (cg (fun t => (q102 ◇ (q102 ◇ (q102 ◇ q103))) ◇ t) (cg (fun t => (q102 ◇ (q102 ◇ (q102 ◇ q103))) ◇ t) (apc2 q102 q103 q102)))).symm).trans (apc87 q103 (q102 ◇ (q102 ◇ (q102 ◇ q103))))).trans (apc2 q102 q103 (q103 ◇ (q102 ◇ (q102 ◇ (q102 ◇ q103))))))
  have apc96:=fun (q104 q105:G)=>by
    exact ((((((cg (fun t => (q104 ◇ (q104 ◇ (q104 ◇ q105))) ◇ t) (cg (fun t => (q105 ◇ (q105 ◇ (q104 ◇ q105))) ◇ t) (cg (fun t => q105 ◇ t) (apc2 q104 q105 (q105 ◇ (q104 ◇ (q104 ◇ (q104 ◇ q105)))))))).trans (cg (fun t => (q104 ◇ (q104 ◇ (q104 ◇ q105))) ◇ t) (apc85 q104 q105))).trans (apc21 q104 q104 q105 q105)).trans (apc2 q104 q105 (q105 ◇ (q104 ◇ (q104 ◇ (q104 ◇ q105)))))).symm).trans ((((cg (fun t => (q104 ◇ (q104 ◇ (q104 ◇ q105))) ◇ t) (cg (fun t => t ◇ (q105 ◇ (q105 ◇ (q104 ◇ (q104 ◇ (q104 ◇ q105)))))) (cg (fun t => q105 ◇ t) (cg (fun t => q105 ◇ t) (apc2 q104 q105 q104))))).symm).trans (apc86 (q104 ◇ (q104 ◇ (q104 ◇ q105))) q105)).trans (cg (fun t => t ◇ (q104 ◇ (q104 ◇ (q104 ◇ q105)))) (cg (fun t => q105 ◇ t) (cg (fun t => q105 ◇ t) (apc2 q104 q105 (q105 ◇ (q104 ◇ (q104 ◇ (q104 ◇ q105)))))))))).symm
  have apc97:=fun (q106 q107:G)=>by
    exact ((((((((cg (fun t => (q106 ◇ q106) ◇ t) (cg (fun t => (q107 ◇ (q106 ◇ (q106 ◇ (q106 ◇ q106)))) ◇ t) (cg (fun t => (q106 ◇ (q106 ◇ (q106 ◇ q106))) ◇ t) (apc84 q106 q106 q107)))).trans (cg (fun t => (q106 ◇ q106) ◇ t) (cg (fun t => (q107 ◇ (q106 ◇ (q106 ◇ (q106 ◇ q106)))) ◇ t) (cg (fun t => (q106 ◇ (q106 ◇ (q106 ◇ q106))) ◇ t) (apc7 q107 q106))))).trans (cg (fun t => (q106 ◇ q106) ◇ t) (cg (fun t => t ◇ ((q106 ◇ (q106 ◇ (q106 ◇ q106))) ◇ (q107 ◇ q106))) (apc84 q106 q106 q107)))).trans (cg (fun t => (q106 ◇ q106) ◇ t) (cg (fun t => t ◇ ((q106 ◇ (q106 ◇ (q106 ◇ q106))) ◇ (q107 ◇ q106))) (apc7 q107 q106)))).trans (cg (fun t => (q106 ◇ q106) ◇ t) (cg (fun t => (q107 ◇ q106) ◇ t) (apc57 q106 q107)))).trans (apc36 q107 q106)).symm).trans ((((cg (fun t => t ◇ ((q107 ◇ (q106 ◇ (q106 ◇ (q106 ◇ q106)))) ◇ ((q106 ◇ (q106 ◇ (q106 ◇ q106))) ◇ (q107 ◇ (q106 ◇ (q106 ◇ (q106 ◇ q106))))))) (apc96 q106 q106)).symm).trans (apc36 q107 (q106 ◇ (q106 ◇ (q106 ◇ q106))))).trans ((cg (fun t => t ◇ (q106 ◇ (q106 ◇ (q106 ◇ q106)))) (apc84 q106 q106 q107)).trans (cg (fun t => t ◇ (q106 ◇ (q106 ◇ (q106 ◇ q106)))) (apc7 q107 q106))))).symm
  have apc98:=fun (q108 q109:G)=>by
    exact (((((cg (fun t => t ◇ ((q108 ◇ q109) ◇ ((q108 ◇ q109) ◇ q109))) (cg (fun t => (q109 ◇ (q109 ◇ q109)) ◇ t) (apc3 q109 q109 q109))).trans (cg (fun t => t ◇ ((q108 ◇ q109) ◇ ((q108 ◇ q109) ◇ q109))) (apc53 q109 q109 q109))).trans (cg (fun t => t ◇ ((q108 ◇ q109) ◇ ((q108 ◇ q109) ◇ q109))) (apc2 q109 q109 (q109 ◇ (q109 ◇ (q109 ◇ (q109 ◇ q109))))))).trans (apc80 (q108 ◇ q109) q109 (q108 ◇ q109))).symm).trans ((((cg (fun t => ((q109 ◇ (q109 ◇ q109)) ◇ ((q109 ◇ (q109 ◇ q109)) ◇ (q109 ◇ (q109 ◇ q109)))) ◇ t) (cg (fun t => (q108 ◇ q109) ◇ t) (apc97 q109 q108))).symm).trans (apc53 (q108 ◇ q109) q109 (q109 ◇ (q109 ◇ q109)))).trans ((cg (fun t => (q109 ◇ (q109 ◇ q109)) ◇ t) (cg (fun t => (q108 ◇ q109) ◇ t) (apc97 q109 q108))).trans (apc58 (q108 ◇ q109) q109)))
  have apc117:=fun (q110 q111 q112:G)=>by
    exact ((((((cg (fun t => ((q110 ◇ (q110 ◇ (q110 ◇ q110))) ◇ q110) ◇ t) (cg (fun t => q112 ◇ t) (apc84 q110 q110 q111))).trans (cg (fun t => ((q110 ◇ (q110 ◇ (q110 ◇ q110))) ◇ q110) ◇ t) (cg (fun t => q112 ◇ t) (apc7 q111 q110)))).trans (cg (fun t => t ◇ (q112 ◇ (q111 ◇ q110))) (apc56 q110 q110))).trans (apc80 q111 q110 q112)).symm).trans ((((cg (fun t => t ◇ (q112 ◇ (q111 ◇ (q110 ◇ (q110 ◇ (q110 ◇ q110)))))) (apc55 q110 (q110 ◇ (q110 ◇ (q110 ◇ q110))))).symm).trans (apc80 q111 (q110 ◇ (q110 ◇ (q110 ◇ q110))) q112)).trans ((cg (fun t => (q110 ◇ (q110 ◇ (q110 ◇ q110))) ◇ t) (cg (fun t => q112 ◇ t) (apc84 q110 q110 q111))).trans (cg (fun t => (q110 ◇ (q110 ◇ (q110 ◇ q110))) ◇ t) (cg (fun t => q112 ◇ t) (apc7 q111 q110)))))).symm
  have apc118:=fun (q113 q114 q115:G)=>by
    exact (((((cg (fun t => (q113 ◇ (q113 ◇ (q114 ◇ q115))) ◇ t) (cg (fun t => (q115 ◇ (q115 ◇ (q113 ◇ q115))) ◇ t) (apc73 q113 q114 q115))).trans (cg (fun t => (q113 ◇ (q113 ◇ (q114 ◇ q115))) ◇ t) (apc85 q113 q115))).trans (apc21 q113 q114 q115 q115)).symm).trans ((((cg (fun t => (q113 ◇ (q113 ◇ (q114 ◇ q115))) ◇ t) (cg (fun t => t ◇ (q115 ◇ (q115 ◇ (q113 ◇ (q113 ◇ (q114 ◇ q115)))))) (cg (fun t => q115 ◇ t) (cg (fun t => q115 ◇ t) ((h q113 q115 q114).symm))))).symm).trans (apc86 (q113 ◇ (q113 ◇ (q114 ◇ q115))) q115)).trans (cg (fun t => t ◇ (q113 ◇ (q113 ◇ (q114 ◇ q115)))) (cg (fun t => q115 ◇ t) (apc73 q113 q114 q115))))).symm
  have apc119:=fun (q116 q117 q118:G)=>by
    exact ((cg (fun t => (q117 ◇ q118) ◇ t) (cg (fun t => (q117 ◇ (q116 ◇ q118)) ◇ t) (apc3 q116 q118 q117))).symm).trans ((h (q117 ◇ (q116 ◇ q118)) (q117 ◇ q118) q118).symm)
  have apc120:=fun (q119 q120:G)=>by
    exact (((apc74 (q120 ◇ (q119 ◇ q120)) q119 q120 ((q120 ◇ q120) ◇ (q120 ◇ ((q120 ◇ (q119 ◇ q120)) ◇ ((q120 ◇ (q119 ◇ q120)) ◇ (q119 ◇ q120))))) ((q120 ◇ q120) ◇ (q120 ◇ ((q120 ◇ (q119 ◇ q120)) ◇ ((q120 ◇ (q119 ◇ q120)) ◇ (q119 ◇ q120))))) ((q120 ◇ q120) ◇ (q120 ◇ ((q120 ◇ (q119 ◇ q120)) ◇ ((q120 ◇ (q119 ◇ q120)) ◇ (q119 ◇ q120)))))).symm).trans (((cg (fun t => (q120 ◇ q120) ◇ t) (apc84 q119 q120 (q120 ◇ (q119 ◇ q120)))).symm).trans (apc119 q119 q120 q120))).symm
  have apc127:=fun (q121 q122:G)=>by
    exact (((cg (fun t => (q122 ◇ (q122 ◇ q122)) ◇ t) (cg (fun t => (q121 ◇ q122) ◇ t) (apc0 q121 q122))).symm).trans (apc53 (q121 ◇ q122) q122 q122)).trans ((cg (fun t => q122 ◇ t) (cg (fun t => (q121 ◇ q122) ◇ t) (apc0 q121 q122))).trans (apc4 q121 q122))
  have apc130:=fun (q123 q124 q125:G)=>by
    exact ((((cg (fun t => (q125 ◇ q125) ◇ t) (apc46 q123 (q125 ◇ (q124 ◇ q125)))).trans (apc11 q124 q125 q123)).symm).trans (((cg (fun t => (q125 ◇ q125) ◇ t) (cg (fun t => (q123 ◇ (q123 ◇ (q123 ◇ (q125 ◇ (q124 ◇ q125))))) ◇ t) (apc88 q123 (q125 ◇ (q124 ◇ q125))))).symm).trans (apc11 q124 q125 (q123 ◇ (q123 ◇ (q123 ◇ (q125 ◇ (q124 ◇ q125)))))))).symm
  have apc131:=fun (q126 q127 q128:G)=>by
    exact ((cg (fun t => (q127 ◇ q127) ◇ t) (cg (fun t => q128 ◇ t) (cg (fun t => q128 ◇ t) (apc130 q126 q126 q127)))).symm).trans ((h q128 (q127 ◇ q127) (q126 ◇ (q126 ◇ (q126 ◇ (q127 ◇ (q126 ◇ q127)))))).symm)
  have apc132:=fun (q129 q130 q131:G)=>by
    exact ((((cg (fun t => (q131 ◇ (q131 ◇ (q129 ◇ (q130 ◇ q130)))) ◇ t) (cg (fun t => (q130 ◇ q130) ◇ t) (apc80 q130 q130 q131))).trans (cg (fun t => (q131 ◇ (q131 ◇ (q129 ◇ (q130 ◇ q130)))) ◇ t) (apc67 q131 q130))).trans (apc21 q131 q129 q130 (q130 ◇ q130))).symm).trans ((((cg (fun t => (q131 ◇ (q131 ◇ (q129 ◇ (q130 ◇ q130)))) ◇ t) (cg (fun t => (q130 ◇ q130) ◇ t) (cg (fun t => (q130 ◇ q130) ◇ t) (apc131 q129 q130 q131)))).symm).trans (apc2 (q130 ◇ q130) (q131 ◇ (q131 ◇ (q129 ◇ (q130 ◇ q130)))) q129)).trans (apc131 q129 q130 q131))
  have apc133:=fun (q132 q133:G)=>by
    exact (((cg (fun t => q132 ◇ t) (cg (fun t => q133 ◇ t) (cg (fun t => q133 ◇ t) (apc0 q132 q132)))).trans (cg (fun t => q132 ◇ t) (cg (fun t => q133 ◇ t) (apc79 q132 q133)))).symm).trans (((cg (fun t => q132 ◇ t) (cg (fun t => q133 ◇ t) (cg (fun t => q133 ◇ t) (apc6 (q132 ◇ q132))))).symm).trans (apc132 ((q132 ◇ q132) ◇ (q132 ◇ q132)) q132 q133))
  have apc135:=fun (q134 q135:G)=>by
    exact ((cg (fun t => (q134 ◇ q135) ◇ t) (cg (fun t => q135 ◇ t) ((h (q134 ◇ q135) q135 q134).symm))).symm).trans (apc132 (q134 ◇ q135) (q134 ◇ q135) q135)
  have apc139:=fun (q24 q136 q137:G)=>by
    exact ((cg (fun t => (q136 ◇ (q24 ◇ q136)) ◇ t) (cg (fun t => q137 ◇ t) (apc84 q24 q136 q137))).symm).trans (((cg (fun t => (q136 ◇ (q24 ◇ q136)) ◇ t) (cg (fun t => q137 ◇ t) (cg (fun t => q137 ◇ t) (apc5 q24 q136)))).symm).trans ((h q137 (q136 ◇ (q24 ◇ q136)) (q136 ◇ q136)).symm))
  have apc140:=fun (q138 q139 q140:G)=>by
    exact ((cg (fun t => (q139 ◇ (q138 ◇ q139)) ◇ t) (cg (fun t => q140 ◇ t) ((h q140 q139 q138).symm))).symm).trans (apc139 q138 q139 q140)
  have apc141:=fun (q141 q142:G)=>by
    exact ((cg (fun t => q142 ◇ t) (apc140 q141 q142 (q142 ◇ (q141 ◇ q142)))).symm).trans ((h (q142 ◇ (q141 ◇ q142)) q142 (q142 ◇ (q141 ◇ q142))).symm)
  have apc147:=fun (q143 q144:G)=>by
    exact ((cg (fun t => (q144 ◇ (q143 ◇ q144)) ◇ t) (cg (fun t => q144 ◇ t) (apc141 q143 q144))).symm).trans ((h q144 (q144 ◇ (q143 ◇ q144)) (q144 ◇ (q143 ◇ q144))).symm)
  have apc150:=fun (q145 q66 q67:G)=>by
    exact (((cg (fun t => (q145 ◇ (q145 ◇ (q145 ◇ q145))) ◇ t) (cg (fun t => q66 ◇ t) (cg (fun t => q66 ◇ t) (apc55 q145 q67)))).symm).trans ((h q66 (q145 ◇ (q145 ◇ (q145 ◇ q145))) q67).symm)).trans ((apc84 q145 q145 q66).trans (apc7 q66 q145))
  have apc151:=fun (q146 q147:G)=>by
    exact (((((cg (fun t => (q147 ◇ (q147 ◇ (q147 ◇ q147))) ◇ t) (apc147 q146 q147)).trans (apc118 q147 q146 q147)).trans (apc26 q147 q146)).symm).trans (((cg (fun t => (q147 ◇ (q147 ◇ (q147 ◇ q147))) ◇ t) (cg (fun t => (q147 ◇ (q146 ◇ q147)) ◇ t) (apc120 q146 q147))).symm).trans (apc150 q147 (q147 ◇ (q146 ◇ q147)) q147))).symm
  have apc152:=fun (q148 q149 q150:G)=>by
    exact ((apc150 q148 (q149 ◇ (q149 ◇ (q150 ◇ q148))) q149).symm).trans ((((cg (fun t => (q148 ◇ (q148 ◇ (q148 ◇ q148))) ◇ t) (cg (fun t => (q149 ◇ (q149 ◇ (q150 ◇ q148))) ◇ t) (cg (fun t => (q149 ◇ (q149 ◇ (q150 ◇ q148))) ◇ t) (apc150 q148 q149 q150)))).symm).trans (apc87 (q148 ◇ (q148 ◇ (q148 ◇ q148))) (q149 ◇ (q149 ◇ (q150 ◇ q148))))).trans (apc150 q148 q149 q150))
  have apc153:=fun (q151 q152:G)=>by
    exact ((apc140 q152 q151 q152).symm).trans (((cg (fun t => t ◇ (q152 ◇ (q152 ◇ q151))) (cg (fun t => q151 ◇ t) (apc2 q152 q151 q151))).symm).trans (apc152 (q152 ◇ (q152 ◇ q151)) q151 q152))
  have apc154:=fun (q146 q147 q119 q120:G)=>by
    exact (apc120 q119 q120).trans (cg (fun t => q120 ◇ t) (apc151 q119 q120))
  have apc155:=fun (q153 q154:G)=>by
    exact ((((((cg (fun t => (q154 ◇ q154) ◇ t) (cg (fun t => (q154 ◇ (q153 ◇ q154)) ◇ t) (cg (fun t => (q154 ◇ q154) ◇ t) (apc3 q153 q154 q154)))).trans (cg (fun t => (q154 ◇ q154) ◇ t) (cg (fun t => (q154 ◇ (q153 ◇ q154)) ◇ t) (apc33 q154 q153 q154)))).trans (cg (fun t => (q154 ◇ q154) ◇ t) (cg (fun t => (q154 ◇ (q153 ◇ q154)) ◇ t) (apc26 q154 q153)))).trans (cg (fun t => (q154 ◇ q154) ◇ t) (apc154 ((q154 ◇ (q153 ◇ q154)) ◇ (q154 ◇ q154)) ((q154 ◇ (q153 ◇ q154)) ◇ (q154 ◇ q154)) q153 q154))).trans (apc80 q154 q154 q154)).symm).trans ((((cg (fun t => (q154 ◇ q154) ◇ t) (cg (fun t => (q154 ◇ (q153 ◇ q154)) ◇ t) (cg (fun t => (q154 ◇ q154) ◇ t) (cg (fun t => (q154 ◇ (q153 ◇ q154)) ◇ t) (apc154 q153 q153 q153 q154))))).symm).trans (apc133 (q154 ◇ q154) (q154 ◇ (q153 ◇ q154)))).trans ((cg (fun t => (q154 ◇ (q153 ◇ q154)) ◇ t) (apc0 q154 q154)).trans (apc3 q153 q154 q154)))
  have apc156:=fun (q155 q156 q157:G)=>by
    exact (((apc155 q155 q157).symm).trans (apc155 q156 q157)).symm
  have apc159:=fun (q158 q159 q160:G)=>by
    exact ((cg (fun t => q159 ◇ t) (apc156 q158 q159 q160)).symm).trans (apc87 q159 q160)
  have apc160:=fun (q161 q162 q163:G)=>by
    exact ((((((cg (fun t => q163 ◇ t) (cg (fun t => (q162 ◇ (q161 ◇ q162)) ◇ t) (apc159 q161 (q162 ◇ (q161 ◇ q162)) q162))).trans (cg (fun t => q163 ◇ t) (cg (fun t => (q162 ◇ (q161 ◇ q162)) ◇ t) (apc151 q161 q162)))).trans (cg (fun t => q163 ◇ t) (apc154 ((q162 ◇ (q161 ◇ q162)) ◇ (q162 ◇ q162)) ((q162 ◇ (q161 ◇ q162)) ◇ (q162 ◇ q162)) q161 q162))).trans (apc79 q162 q163)).symm).trans (((cg (fun t => q163 ◇ t) (cg (fun t => (q162 ◇ (q161 ◇ q162)) ◇ t) (cg (fun t => (q162 ◇ (q161 ◇ q162)) ◇ t) (apc29 q161 q162)))).symm).trans (apc159 (q162 ◇ (q162 ◇ q162)) q163 (q162 ◇ (q161 ◇ q162))))).symm
  have apc162:=fun (q164 q165:G)=>by
    exact (((cg (fun t => (q165 ◇ q164) ◇ t) (apc57 q164 (q165 ◇ q164))).trans (apc135 q165 q164)).symm).trans ((((cg (fun t => (q165 ◇ q164) ◇ t) (cg (fun t => (q164 ◇ (q164 ◇ (q164 ◇ q164))) ◇ t) (apc97 q164 q165))).symm).trans (apc153 (q164 ◇ (q164 ◇ (q164 ◇ q164))) (q165 ◇ q164))).trans (((cg (fun t => (q164 ◇ (q164 ◇ (q164 ◇ q164))) ◇ t) (cg (fun t => (q165 ◇ q164) ◇ t) (apc159 q164 (q165 ◇ q164) q164))).trans (apc117 q164 (q165 ◇ q164) (q165 ◇ q164))).trans (apc98 q165 q164)))
  have apc166:=fun (q166 q167 q168:G)=>by
    exact (((cg (fun t => q168 ◇ t) (apc80 q166 q166 q167)).symm).trans (apc160 q167 (q166 ◇ q166) q168)).trans ((apc33 q168 q166 q166).trans (apc7 q168 q166))
  have apc167:=fun (q169 q170:G)=>by
    exact (((((cg (fun t => t ◇ (q169 ◇ q170)) (cg (fun t => q170 ◇ t) (cg (fun t => (q170 ◇ (q169 ◇ q170)) ◇ t) (apc151 q169 q170)))).trans (cg (fun t => t ◇ (q169 ◇ q170)) (cg (fun t => q170 ◇ t) (apc154 ((q170 ◇ (q169 ◇ q170)) ◇ (q170 ◇ q170)) ((q170 ◇ (q169 ◇ q170)) ◇ (q170 ◇ q170)) q169 q170)))).trans (apc57 q170 q169)).symm).trans (((cg (fun t => t ◇ (q169 ◇ q170)) (apc160 q169 q170 (q170 ◇ (q169 ◇ q170)))).symm).trans (apc28 q170 (q169 ◇ q170)))).symm
  have apc176:=fun (q171 q172:G)=>by
    exact (((((cg (fun t => t ◇ ((q171 ◇ q172) ◇ (q171 ◇ q172))) (cg (fun t => q172 ◇ t) (cg (fun t => (q172 ◇ (q171 ◇ q172)) ◇ t) (apc151 q171 q172)))).trans (cg (fun t => t ◇ ((q171 ◇ q172) ◇ (q171 ◇ q172))) (cg (fun t => q172 ◇ t) (apc154 ((q172 ◇ (q171 ◇ q172)) ◇ (q172 ◇ q172)) ((q172 ◇ (q171 ◇ q172)) ◇ (q172 ◇ q172)) q171 q172)))).trans (apc117 q172 q171 (q171 ◇ q172))).trans (apc162 q172 q171)).symm).trans (((cg (fun t => t ◇ ((q171 ◇ q172) ◇ (q171 ◇ q172))) (apc160 q171 q172 (q172 ◇ (q171 ◇ q172)))).symm).trans (apc27 q172 (q171 ◇ q172)))
  have apc177:=fun (q173 q174:G)=>by
    exact ((((cg (fun t => ((q174 ◇ (q174 ◇ q174)) ◇ ((q173 ◇ q174) ◇ (q174 ◇ (q173 ◇ q174)))) ◇ t) (apc3 q174 q174 q174)).trans (cg (fun t => t ◇ (q174 ◇ (q174 ◇ (q174 ◇ q174)))) (apc127 q173 q174))).trans (apc159 q174 ((q173 ◇ q174) ◇ q174) q174)).symm).trans ((((cg (fun t => t ◇ ((q174 ◇ (q174 ◇ q174)) ◇ (q174 ◇ (q174 ◇ q174)))) (cg (fun t => (q174 ◇ (q174 ◇ q174)) ◇ t) (apc176 q173 q174))).symm).trans (apc154 q173 q173 (q173 ◇ q174) (q174 ◇ (q174 ◇ q174)))).trans (((cg (fun t => (q174 ◇ (q174 ◇ q174)) ◇ t) (apc3 q174 q174 q174)).trans (apc53 q174 q174 q174)).trans (apc2 q174 q174 (q174 ◇ (q174 ◇ (q174 ◇ (q174 ◇ q174)))))))
  have apc179:=fun (q175 q176:G)=>by
    exact ((((cg (fun t => t ◇ (q175 ◇ q176)) (apc167 q175 q176)).trans (apc167 q175 q176)).symm).trans (((cg (fun t => t ◇ (q175 ◇ q176)) (cg (fun t => t ◇ (q175 ◇ q176)) (apc25 q175 q176))).symm).trans (apc177 (q176 ◇ q176) (q175 ◇ q176)))).symm
  have apc180:=fun (q177 q178:G)=>by
    exact (((((cg (fun t => t ◇ q177) (apc159 q177 (q178 ◇ q177) (q178 ◇ q177))).trans (cg (fun t => t ◇ q177) (apc179 q178 q177))).trans (apc151 q178 q177)).symm).trans ((((cg (fun t => t ◇ q177) (cg (fun t => (q178 ◇ q177) ◇ t) (cg (fun t => (q178 ◇ q177) ◇ t) (cg (fun t => (q178 ◇ q177) ◇ t) (apc179 q178 q177))))).symm).trans (apc78 (q178 ◇ q177) q177 q178)).trans ((((cg (fun t => q177 ◇ t) (cg (fun t => (q178 ◇ q177) ◇ t) (apc179 q178 q177))).trans (apc160 q177 (q178 ◇ q177) q177)).trans (cg (fun t => (q178 ◇ q177) ◇ t) (apc160 q178 q177 q177))).trans (apc159 q177 (q178 ◇ q177) q177)))).symm
  have apc181:=fun (q179 q180:G)=>by
    exact (((cg (fun t => (q179 ◇ q180) ◇ t) (apc2 q179 q180 (q180 ◇ (q179 ◇ (q179 ◇ (q179 ◇ q180)))))).trans (apc179 q179 q180)).symm).trans ((((cg (fun t => t ◇ (q180 ◇ (q179 ◇ (q179 ◇ (q179 ◇ q180))))) (apc2 q179 q180 q179)).symm).trans (apc179 q180 (q179 ◇ (q179 ◇ (q179 ◇ q180))))).trans ((cg (fun t => (q179 ◇ (q179 ◇ (q179 ◇ q180))) ◇ t) (apc2 q179 q180 (q180 ◇ (q179 ◇ (q179 ◇ (q179 ◇ q180)))))).trans (apc46 q179 q180)))
  have apc182:=fun (q181 q182:G)=>by
    exact ((((cg (fun t => q182 ◇ t) (apc166 q182 (q181 ◇ q182) (q181 ◇ q182))).trans (cg (fun t => q182 ◇ t) (apc180 q182 q181))).symm).trans (((cg (fun t => q182 ◇ t) (cg (fun t => (q181 ◇ q182) ◇ t) (cg (fun t => q182 ◇ t) (cg (fun t => (q181 ◇ q182) ◇ t) (apc180 q182 q181))))).symm).trans (apc133 q182 (q181 ◇ q182)))).symm
  have apc185:=fun (q0 q1 q179 q180:G)=>by
    exact ((apc182 q0 q1).symm).trans ((apc0 q0 q1).trans (apc181 q0 q1))
  have apc186:=fun (q183 q184:G)=>by
    exact (((apc7 q183 q184).symm).trans ((((cg (fun t => q184 ◇ t) (apc185 q183 (q184 ◇ q184) q183 q183)).symm).trans (apc7 (q184 ◇ q184) q184)).trans (apc180 q184 q184))).symm
  have apc189:=fun (q185 q186:G)=>by
    exact ((((((cg (fun t => q186 ◇ t) (cg (fun t => q185 ◇ t) (cg (fun t => (q186 ◇ q186) ◇ t) (apc182 q186 q186)))).trans (cg (fun t => q186 ◇ t) (cg (fun t => q185 ◇ t) (apc80 q186 q186 q186)))).trans (cg (fun t => q186 ◇ t) (apc166 q186 q186 q185))).trans (apc181 q185 q186)).symm).trans (((cg (fun t => q186 ◇ t) (cg (fun t => q185 ◇ t) ((apc185 q185 (q186 ◇ q186) q185 q185).symm))).symm).trans (apc132 q185 q186 q185))).symm
  have apc192:=fun (q187 q188 q189:G)=>by
    exact (((cg (fun t => q188 ◇ t) (apc186 q187 q189)).symm).trans (apc189 q188 q189)).symm
  exact ((apc192 y x z).symm).trans (apc192 (x ◇ z) x z)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_41890_to_55199 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_41890_to_55199
