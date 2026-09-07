-- Equation6718 → Equation40238
-- Recorded verdict: true
-- Premise: x = y ◇ (x ◇ ((y ◇ z) ◇ (z ◇ y)))
-- Conclusion: x = (((y ◇ (y ◇ z)) ◇ z) ◇ x) ◇ y
-- Original submission SHA-256: 3ee5cb89fc995166ad0d987a5233b4ae27eb5e87c0719fc56661e037dd5fb116
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (x ◇ ((y ◇ z) ◇ (z ◇ y)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (((y ◇ (y ◇ z)) ◇ z) ◇ x) ◇ y
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
    exact ((cg (fun t => (q0 ◇ q1) ◇ t) ((h ((q0 ◇ q1) ◇ (q1 ◇ q0)) q1 q0).symm)).symm).trans ((h q1 (q0 ◇ q1) (q1 ◇ q0)).symm)
  have apc3:=fun (q2 q0 q1 q3:G)=>by
    exact ((cg (fun t => q3 ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => t ◇ ((q2 ◇ ((q3 ◇ q0) ◇ (q0 ◇ q3))) ◇ q3)) ((h q2 q3 q0).symm)))).symm).trans ((h q1 q3 (q2 ◇ ((q3 ◇ q0) ◇ (q0 ◇ q3)))).symm)
  have apc4:=fun (q4 q5:G)=>by
    exact ((cg (fun t => q5 ◇ t) (cg (fun t => t ◇ (((q4 ◇ q5) ◇ (q5 ◇ q4)) ◇ (q4 ◇ q5))) (apc0 q4 q5))).symm).trans (((cg (fun t => t ◇ (((q4 ◇ q5) ◇ ((q4 ◇ q5) ◇ (q5 ◇ q4))) ◇ (((q4 ◇ q5) ◇ (q5 ◇ q4)) ◇ (q4 ◇ q5)))) (apc0 q4 q5)).symm).trans (apc0 (q4 ◇ q5) ((q4 ◇ q5) ◇ (q5 ◇ q4))))
  have apc6:=fun (q6 q7 q8:G)=>by
    exact ((cg (fun t => (q6 ◇ q7) ◇ t) (cg (fun t => q8 ◇ t) (cg (fun t => t ◇ (((q6 ◇ q7) ◇ (q7 ◇ q6)) ◇ (q6 ◇ q7))) (apc0 q6 q7)))).symm).trans ((h q8 (q6 ◇ q7) ((q6 ◇ q7) ◇ (q7 ◇ q6))).symm)
  have apc7:=fun (q6 q7 q8:G)=>by
    exact ((cg (fun t => ((q6 ◇ q7) ◇ (q7 ◇ q6)) ◇ t) (cg (fun t => q8 ◇ t) (cg (fun t => (((q6 ◇ q7) ◇ (q7 ◇ q6)) ◇ (q6 ◇ q7)) ◇ t) (apc0 q6 q7)))).symm).trans ((h q8 ((q6 ◇ q7) ◇ (q7 ◇ q6)) (q6 ◇ q7)).symm)
  have apc9:=fun (q2 q0 q1 q9:G)=>by
    exact ((cg (fun t => (q2 ◇ ((q9 ◇ q0) ◇ (q0 ◇ q9))) ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => ((q2 ◇ ((q9 ◇ q0) ◇ (q0 ◇ q9))) ◇ q9) ◇ t) ((h q2 q9 q0).symm)))).symm).trans ((h q1 (q2 ◇ ((q9 ◇ q0) ◇ (q0 ◇ q9))) q9).symm)
  have apc10:=fun (q10 q11 q12:G)=>by
    exact ((cg (fun t => q12 ◇ t) (apc9 q12 q10 (q12 ◇ ((q12 ◇ ((q11 ◇ q10) ◇ (q10 ◇ q11))) ◇ q11)) q11)).symm).trans ((h (q12 ◇ ((q11 ◇ q10) ◇ (q10 ◇ q11))) q12 ((q12 ◇ ((q11 ◇ q10) ◇ (q10 ◇ q11))) ◇ q11)).symm)
  have apc11:=fun (q13 q14:G)=>by
    exact (((apc4 q13 q14).symm).trans (((cg (fun t => q14 ◇ t) (cg (fun t => q14 ◇ t) (cg (fun t => t ◇ (q13 ◇ q14)) ((h ((q13 ◇ q14) ◇ (q14 ◇ q13)) q14 q13).symm)))).symm).trans (apc10 (q14 ◇ q13) (q13 ◇ q14) q14))).symm
  have apc26:=fun (q15 q16 q17 q18:G)=>by
    exact ((cg (fun t => ((q16 ◇ q15) ◇ (q15 ◇ q16)) ◇ t) (cg (fun t => q18 ◇ t) ((h (q16 ◇ ((((q16 ◇ q15) ◇ (q15 ◇ q16)) ◇ q17) ◇ (q17 ◇ ((q16 ◇ q15) ◇ (q15 ◇ q16))))) q16 q15).symm))).symm).trans (apc3 q16 q17 q18 ((q16 ◇ q15) ◇ (q15 ◇ q16)))
  have apc27:=fun (q19 q20:G)=>by
    exact ((cg (fun t => ((q20 ◇ q19) ◇ (q19 ◇ q20)) ◇ t) ((h q20 ((q20 ◇ q19) ◇ (q19 ◇ q20)) q19).symm)).symm).trans (apc26 q19 q20 q19 ((q20 ◇ q19) ◇ (q19 ◇ q20)))
  have apc30:=fun (q21 q22 q23:G)=>by
    exact ((cg (fun t => q23 ◇ t) (cg (fun t => q22 ◇ t) (cg (fun t => (q23 ◇ ((q23 ◇ q21) ◇ (q21 ◇ q23))) ◇ t) (apc27 q21 q23)))).symm).trans ((h q22 q23 ((q23 ◇ q21) ◇ (q21 ◇ q23))).symm)
  have apc31:=fun (q24 q25:G)=>by
    exact ((cg (fun t => q25 ◇ t) ((h (q25 ◇ ((q25 ◇ q24) ◇ (q24 ◇ q25))) q25 q24).symm)).symm).trans (apc30 q24 q25 q25)
  have apc32:=fun (q26 q27:G)=>by
    exact (((cg (fun t => t ◇ q27) (cg (fun t => t ◇ ((q27 ◇ ((q27 ◇ q26) ◇ (q26 ◇ q27))) ◇ q27)) (apc31 q26 q27))).symm).trans (apc27 (q27 ◇ ((q27 ◇ q26) ◇ (q26 ◇ q27))) q27)).trans (cg (fun t => t ◇ ((q27 ◇ ((q27 ◇ q26) ◇ (q26 ◇ q27))) ◇ q27)) (apc31 q26 q27))
  have apc33:=fun (q28 q29:G)=>by
    exact (((cg (fun t => t ◇ q29) (cg (fun t => (q29 ◇ ((q29 ◇ q28) ◇ (q28 ◇ q29))) ◇ t) (apc27 q28 q29))).symm).trans (apc27 ((q29 ◇ q28) ◇ (q28 ◇ q29)) q29)).trans (cg (fun t => (q29 ◇ ((q29 ◇ q28) ◇ (q28 ◇ q29))) ◇ t) (apc27 q28 q29))
  have apc35:=fun (q30 q31:G)=>by
    exact (((cg (fun t => t ◇ ((q30 ◇ q31) ◇ (q31 ◇ q30))) (cg (fun t => (((q30 ◇ q31) ◇ (q31 ◇ q30)) ◇ (q30 ◇ q31)) ◇ t) (apc0 q30 q31))).symm).trans (apc27 (q30 ◇ q31) ((q30 ◇ q31) ◇ (q31 ◇ q30)))).trans (cg (fun t => (((q30 ◇ q31) ◇ (q31 ◇ q30)) ◇ (q30 ◇ q31)) ◇ t) (apc0 q30 q31))
  have apc36:=fun (q32 q33:G)=>by
    exact ((cg (fun t => q32 ◇ t) (apc35 q32 q33)).symm).trans ((h ((((q32 ◇ q33) ◇ (q33 ◇ q32)) ◇ (q32 ◇ q33)) ◇ q33) q32 q33).symm)
  have apc37:=fun (q34 q35:G)=>by
    exact ((cg (fun t => ((q34 ◇ q35) ◇ (q35 ◇ q34)) ◇ t) (apc36 q34 q35)).symm).trans (apc7 q34 q35 q34)
  have apc38:=fun (q36 q37:G)=>by
    exact ((cg (fun t => ((q37 ◇ q36) ◇ (q36 ◇ q37)) ◇ t) (cg (fun t => t ◇ (q37 ◇ ((q37 ◇ q36) ◇ (q36 ◇ q37)))) (apc27 q36 q37))).symm).trans (((cg (fun t => t ◇ ((((q37 ◇ q36) ◇ (q36 ◇ q37)) ◇ q37) ◇ (q37 ◇ ((q37 ◇ q36) ◇ (q36 ◇ q37))))) (apc27 q36 q37)).symm).trans (apc0 ((q37 ◇ q36) ◇ (q36 ◇ q37)) q37))
  have apc39:=fun (q21 q23 q38:G)=>by
    exact ((cg (fun t => q23 ◇ t) (apc27 q21 ((q23 ◇ q38) ◇ (q38 ◇ q23)))).symm).trans ((h ((((q23 ◇ q38) ◇ (q38 ◇ q23)) ◇ q21) ◇ (q21 ◇ ((q23 ◇ q38) ◇ (q38 ◇ q23)))) q23 q38).symm)
  have apc40:=fun (q39 q40 q41 q42:G)=>by
    exact (((cg (fun t => t ◇ q42) (cg (fun t => t ◇ ((q41 ◇ (q39 ◇ ((q39 ◇ ((q42 ◇ q40) ◇ (q40 ◇ q42))) ◇ q42))) ◇ q42)) (apc3 q39 q40 q41 q42))).symm).trans (apc27 (q41 ◇ (q39 ◇ ((q39 ◇ ((q42 ◇ q40) ◇ (q40 ◇ q42))) ◇ q42))) q42)).trans (cg (fun t => t ◇ ((q41 ◇ (q39 ◇ ((q39 ◇ ((q42 ◇ q40) ◇ (q40 ◇ q42))) ◇ q42))) ◇ q42)) (apc3 q39 q40 q41 q42))
  have apc41:=fun (q43 q44 q45:G)=>by
    exact (((cg (fun t => t ◇ q45) (cg (fun t => q44 ◇ t) (cg (fun t => t ◇ q45) (cg (fun t => q44 ◇ t) (cg (fun t => (q45 ◇ q43) ◇ t) (cg (fun t => t ◇ q45) (apc0 q45 q43))))))).symm).trans (apc40 (q45 ◇ q43) q43 q44 q45)).trans (cg (fun t => q44 ◇ t) (cg (fun t => t ◇ q45) (cg (fun t => q44 ◇ t) (cg (fun t => (q45 ◇ q43) ◇ t) (cg (fun t => t ◇ q45) (apc0 q45 q43))))))
  have apc47:=fun (q46 q47 q48:G)=>by
    exact ((cg (fun t => ((q47 ◇ q46) ◇ (q46 ◇ q47)) ◇ t) (apc39 q48 q47 q46)).symm).trans ((h q47 ((q47 ◇ q46) ◇ (q46 ◇ q47)) q48).symm)
  have apc56:=fun (q15 q16 q17 q18 q21 q23 q38:G)=>by
    exact ((cg (fun t => ((q16 ◇ q15) ◇ (q15 ◇ q16)) ◇ t) (cg (fun t => q18 ◇ t) (apc39 q17 q16 q15))).symm).trans (apc26 q15 q16 q17 q18)
  have apc71:=fun (q49 q50:G)=>by
    exact ((((cg (fun t => q50 ◇ t) (cg (fun t => q50 ◇ t) (cg (fun t => t ◇ ((q50 ◇ ((q50 ◇ ((q50 ◇ q49) ◇ (q49 ◇ q50))) ◇ q50)) ◇ q50)) (cg (fun t => (q50 ◇ ((q50 ◇ ((q50 ◇ q49) ◇ (q49 ◇ q50))) ◇ q50)) ◇ t) (apc10 q49 q50 q50))))).trans (cg (fun t => q50 ◇ t) (cg (fun t => q50 ◇ t) (cg (fun t => ((q50 ◇ ((q50 ◇ ((q50 ◇ q49) ◇ (q49 ◇ q50))) ◇ q50)) ◇ (q50 ◇ ((q50 ◇ q49) ◇ (q49 ◇ q50)))) ◇ t) (apc41 q49 q50 q50))))).trans (cg (fun t => q50 ◇ t) (apc3 q50 q49 ((q50 ◇ ((q50 ◇ ((q50 ◇ q49) ◇ (q49 ◇ q50))) ◇ q50)) ◇ (q50 ◇ ((q50 ◇ q49) ◇ (q49 ◇ q50)))) q50))).symm).trans ((((cg (fun t => q50 ◇ t) (cg (fun t => q50 ◇ t) (cg (fun t => t ◇ ((q50 ◇ ((q50 ◇ ((q50 ◇ q49) ◇ (q49 ◇ q50))) ◇ q50)) ◇ q50)) (cg (fun t => t ◇ (q50 ◇ (q50 ◇ ((q50 ◇ ((q50 ◇ q49) ◇ (q49 ◇ q50))) ◇ q50)))) (apc32 q49 q50))))).symm).trans (apc4 (q50 ◇ ((q50 ◇ ((q50 ◇ q49) ◇ (q49 ◇ q50))) ◇ q50)) q50)).trans ((cg (fun t => t ◇ (q50 ◇ (q50 ◇ ((q50 ◇ ((q50 ◇ q49) ◇ (q49 ◇ q50))) ◇ q50)))) (apc41 q49 q50 q50)).trans (cg (fun t => (q50 ◇ ((q50 ◇ ((q50 ◇ q49) ◇ (q49 ◇ q50))) ◇ q50)) ◇ t) (apc10 q49 q50 q50))))
  have apc86:=fun (q51 q52:G)=>by
    exact ((((cg (fun t => ((q51 ◇ q52) ◇ (q52 ◇ q51)) ◇ t) (cg (fun t => (((q51 ◇ q52) ◇ (q52 ◇ q51)) ◇ ((((q51 ◇ q52) ◇ (q52 ◇ q51)) ◇ ((((q51 ◇ q52) ◇ (q52 ◇ q51)) ◇ (q51 ◇ q52)) ◇ q52)) ◇ ((q51 ◇ q52) ◇ (q52 ◇ q51)))) ◇ t) (cg (fun t => ((q51 ◇ q52) ◇ (q52 ◇ q51)) ◇ t) (cg (fun t => (((q51 ◇ q52) ◇ (q52 ◇ q51)) ◇ (q51 ◇ q52)) ◇ t) (apc0 q51 q52))))).trans (cg (fun t => ((q51 ◇ q52) ◇ (q52 ◇ q51)) ◇ t) (cg (fun t => t ◇ (((q51 ◇ q52) ◇ (q52 ◇ q51)) ◇ ((((q51 ◇ q52) ◇ (q52 ◇ q51)) ◇ (q51 ◇ q52)) ◇ q52))) (cg (fun t => ((q51 ◇ q52) ◇ (q52 ◇ q51)) ◇ t) (cg (fun t => t ◇ ((q51 ◇ q52) ◇ (q52 ◇ q51))) (apc37 q51 q52)))))).trans (cg (fun t => ((q51 ◇ q52) ◇ (q52 ◇ q51)) ◇ t) (cg (fun t => (((q51 ◇ q52) ◇ (q52 ◇ q51)) ◇ (q51 ◇ ((q51 ◇ q52) ◇ (q52 ◇ q51)))) ◇ t) (apc37 q51 q52)))).symm).trans ((((cg (fun t => ((q51 ◇ q52) ◇ (q52 ◇ q51)) ◇ t) (cg (fun t => t ◇ (((q51 ◇ q52) ◇ (q52 ◇ q51)) ◇ ((((q51 ◇ q52) ◇ (q52 ◇ q51)) ◇ (q51 ◇ q52)) ◇ ((q51 ◇ q52) ◇ ((q51 ◇ q52) ◇ (q52 ◇ q51)))))) (cg (fun t => ((q51 ◇ q52) ◇ (q52 ◇ q51)) ◇ t) (cg (fun t => t ◇ ((q51 ◇ q52) ◇ (q52 ◇ q51))) (cg (fun t => ((q51 ◇ q52) ◇ (q52 ◇ q51)) ◇ t) (cg (fun t => (((q51 ◇ q52) ◇ (q52 ◇ q51)) ◇ (q51 ◇ q52)) ◇ t) (apc0 q51 q52))))))).symm).trans (apc71 (q51 ◇ q52) ((q51 ◇ q52) ◇ (q52 ◇ q51)))).trans ((((cg (fun t => t ◇ (((q51 ◇ q52) ◇ (q52 ◇ q51)) ◇ ((((q51 ◇ q52) ◇ (q52 ◇ q51)) ◇ (q51 ◇ q52)) ◇ ((q51 ◇ q52) ◇ ((q51 ◇ q52) ◇ (q52 ◇ q51)))))) (cg (fun t => ((q51 ◇ q52) ◇ (q52 ◇ q51)) ◇ t) (cg (fun t => t ◇ ((q51 ◇ q52) ◇ (q52 ◇ q51))) (cg (fun t => ((q51 ◇ q52) ◇ (q52 ◇ q51)) ◇ t) (cg (fun t => (((q51 ◇ q52) ◇ (q52 ◇ q51)) ◇ (q51 ◇ q52)) ◇ t) (apc0 q51 q52)))))).trans (cg (fun t => (((q51 ◇ q52) ◇ (q52 ◇ q51)) ◇ ((((q51 ◇ q52) ◇ (q52 ◇ q51)) ◇ ((((q51 ◇ q52) ◇ (q52 ◇ q51)) ◇ (q51 ◇ q52)) ◇ q52)) ◇ ((q51 ◇ q52) ◇ (q52 ◇ q51)))) ◇ t) (cg (fun t => ((q51 ◇ q52) ◇ (q52 ◇ q51)) ◇ t) (cg (fun t => (((q51 ◇ q52) ◇ (q52 ◇ q51)) ◇ (q51 ◇ q52)) ◇ t) (apc0 q51 q52))))).trans (cg (fun t => t ◇ (((q51 ◇ q52) ◇ (q52 ◇ q51)) ◇ ((((q51 ◇ q52) ◇ (q52 ◇ q51)) ◇ (q51 ◇ q52)) ◇ q52))) (cg (fun t => ((q51 ◇ q52) ◇ (q52 ◇ q51)) ◇ t) (cg (fun t => t ◇ ((q51 ◇ q52) ◇ (q52 ◇ q51))) (apc37 q51 q52))))).trans (cg (fun t => (((q51 ◇ q52) ◇ (q52 ◇ q51)) ◇ (q51 ◇ ((q51 ◇ q52) ◇ (q52 ◇ q51)))) ◇ t) (apc37 q51 q52))))
  have apc95:=fun (q53 q54:G)=>by
    exact (((cg (fun t => (q53 ◇ q54) ◇ t) (cg (fun t => ((((q53 ◇ q54) ◇ (q54 ◇ q53)) ◇ ((q54 ◇ q53) ◇ (q53 ◇ q54))) ◇ q54) ◇ t) ((h ((q53 ◇ q54) ◇ (q54 ◇ q53)) q54 q53).symm))).symm).trans (apc39 q54 (q53 ◇ q54) (q54 ◇ q53))).trans (cg (fun t => ((((q53 ◇ q54) ◇ (q54 ◇ q53)) ◇ ((q54 ◇ q53) ◇ (q53 ◇ q54))) ◇ q54) ◇ t) (apc11 q53 q54))
  have apc111:=fun (q55 q15 q16 q17 q18:G)=>by
    exact ((cg (fun t => (q55 ◇ ((q17 ◇ q15) ◇ (q15 ◇ q17))) ◇ t) (cg (fun t => q18 ◇ t) (cg (fun t => q16 ◇ t) (cg (fun t => t ◇ (q55 ◇ ((q17 ◇ q15) ◇ (q15 ◇ q17)))) (cg (fun t => q16 ◇ t) (cg (fun t => ((q55 ◇ ((q17 ◇ q15) ◇ (q15 ◇ q17))) ◇ q17) ◇ t) ((h q55 q17 q15).symm))))))).symm).trans (apc3 q16 q17 q18 (q55 ◇ ((q17 ◇ q15) ◇ (q15 ◇ q17))))
  have apc137:=fun (q56 q57:G)=>by
    exact ((apc39 (q57 ◇ ((q57 ◇ q56) ◇ (q56 ◇ q57))) q57 q56).symm).trans (apc30 q56 (((q57 ◇ q56) ◇ (q56 ◇ q57)) ◇ (q57 ◇ ((q57 ◇ q56) ◇ (q56 ◇ q57)))) q57)
  have apc138:=fun (q58 q59:G)=>by
    exact ((cg (fun t => (((q59 ◇ q58) ◇ (q58 ◇ q59)) ◇ (q59 ◇ ((q59 ◇ q58) ◇ (q58 ◇ q59)))) ◇ t) (apc137 q58 q59)).symm).trans (apc0 ((q59 ◇ q58) ◇ (q58 ◇ q59)) (q59 ◇ ((q59 ◇ q58) ◇ (q58 ◇ q59))))
  have apc140:=fun (q60 q61:G)=>by
    exact (((cg (fun t => (q61 ◇ ((q61 ◇ q60) ◇ (q60 ◇ q61))) ◇ t) (cg (fun t => t ◇ ((((q61 ◇ q60) ◇ (q60 ◇ q61)) ◇ (q61 ◇ ((q61 ◇ q60) ◇ (q60 ◇ q61)))) ◇ (((q61 ◇ q60) ◇ (q60 ◇ q61)) ◇ (q61 ◇ ((q61 ◇ q60) ◇ (q60 ◇ q61)))))) (apc138 q60 q61))).trans (cg (fun t => (q61 ◇ ((q61 ◇ q60) ◇ (q60 ◇ q61))) ◇ t) (cg (fun t => (q61 ◇ ((q61 ◇ q60) ◇ (q60 ◇ q61))) ◇ t) (apc138 q60 q61)))).symm).trans (((cg (fun t => t ◇ (((((q61 ◇ q60) ◇ (q60 ◇ q61)) ◇ (q61 ◇ ((q61 ◇ q60) ◇ (q60 ◇ q61)))) ◇ (((q61 ◇ q60) ◇ (q60 ◇ q61)) ◇ (q61 ◇ ((q61 ◇ q60) ◇ (q60 ◇ q61))))) ◇ ((((q61 ◇ q60) ◇ (q60 ◇ q61)) ◇ (q61 ◇ ((q61 ◇ q60) ◇ (q60 ◇ q61)))) ◇ (((q61 ◇ q60) ◇ (q60 ◇ q61)) ◇ (q61 ◇ ((q61 ◇ q60) ◇ (q60 ◇ q61))))))) (apc138 q60 q61)).symm).trans (apc0 (((q61 ◇ q60) ◇ (q60 ◇ q61)) ◇ (q61 ◇ ((q61 ◇ q60) ◇ (q60 ◇ q61)))) (((q61 ◇ q60) ◇ (q60 ◇ q61)) ◇ (q61 ◇ ((q61 ◇ q60) ◇ (q60 ◇ q61))))))
  have apc141:=fun (q62 q63:G)=>by
    exact (((((((cg (fun t => (((q63 ◇ q62) ◇ (q62 ◇ q63)) ◇ (((q63 ◇ q62) ◇ (q62 ◇ q63)) ◇ (q63 ◇ ((q63 ◇ q62) ◇ (q62 ◇ q63))))) ◇ t) (cg (fun t => t ◇ (((q63 ◇ q62) ◇ (q62 ◇ q63)) ◇ ((((q63 ◇ q62) ◇ (q62 ◇ q63)) ◇ q63) ◇ (q63 ◇ ((q63 ◇ q62) ◇ (q62 ◇ q63)))))) (cg (fun t => ((q63 ◇ q62) ◇ (q62 ◇ q63)) ◇ t) (cg (fun t => t ◇ (q63 ◇ ((q63 ◇ q62) ◇ (q62 ◇ q63)))) (apc27 q62 q63))))).trans (cg (fun t => (((q63 ◇ q62) ◇ (q62 ◇ q63)) ◇ (((q63 ◇ q62) ◇ (q62 ◇ q63)) ◇ (q63 ◇ ((q63 ◇ q62) ◇ (q62 ◇ q63))))) ◇ t) (cg (fun t => (((q63 ◇ q62) ◇ (q62 ◇ q63)) ◇ (((q63 ◇ q62) ◇ (q62 ◇ q63)) ◇ (q63 ◇ ((q63 ◇ q62) ◇ (q62 ◇ q63))))) ◇ t) (cg (fun t => ((q63 ◇ q62) ◇ (q62 ◇ q63)) ◇ t) (cg (fun t => t ◇ (q63 ◇ ((q63 ◇ q62) ◇ (q62 ◇ q63)))) (apc27 q62 q63)))))).trans (cg (fun t => (((q63 ◇ q62) ◇ (q62 ◇ q63)) ◇ (((q63 ◇ q62) ◇ (q62 ◇ q63)) ◇ (q63 ◇ ((q63 ◇ q62) ◇ (q62 ◇ q63))))) ◇ t) (cg (fun t => t ◇ (((q63 ◇ q62) ◇ (q62 ◇ q63)) ◇ (((q63 ◇ q62) ◇ (q62 ◇ q63)) ◇ (q63 ◇ ((q63 ◇ q62) ◇ (q62 ◇ q63)))))) (apc38 q62 q63)))).trans (cg (fun t => (((q63 ◇ q62) ◇ (q62 ◇ q63)) ◇ (((q63 ◇ q62) ◇ (q62 ◇ q63)) ◇ (q63 ◇ ((q63 ◇ q62) ◇ (q62 ◇ q63))))) ◇ t) (cg (fun t => q63 ◇ t) (apc38 q62 q63)))).trans (cg (fun t => t ◇ (q63 ◇ q63)) (apc38 q62 q63))).symm).trans ((((cg (fun t => t ◇ ((((q63 ◇ q62) ◇ (q62 ◇ q63)) ◇ ((((q63 ◇ q62) ◇ (q62 ◇ q63)) ◇ q63) ◇ (q63 ◇ ((q63 ◇ q62) ◇ (q62 ◇ q63))))) ◇ (((q63 ◇ q62) ◇ (q62 ◇ q63)) ◇ ((((q63 ◇ q62) ◇ (q62 ◇ q63)) ◇ q63) ◇ (q63 ◇ ((q63 ◇ q62) ◇ (q62 ◇ q63))))))) (cg (fun t => ((q63 ◇ q62) ◇ (q62 ◇ q63)) ◇ t) (cg (fun t => t ◇ (q63 ◇ ((q63 ◇ q62) ◇ (q62 ◇ q63)))) (apc27 q62 q63)))).symm).trans (apc140 q63 ((q63 ◇ q62) ◇ (q62 ◇ q63)))).trans (((cg (fun t => ((((q63 ◇ q62) ◇ (q62 ◇ q63)) ◇ q63) ◇ (q63 ◇ ((q63 ◇ q62) ◇ (q62 ◇ q63)))) ◇ t) (cg (fun t => ((q63 ◇ q62) ◇ (q62 ◇ q63)) ◇ t) (cg (fun t => t ◇ (q63 ◇ ((q63 ◇ q62) ◇ (q62 ◇ q63)))) (apc27 q62 q63)))).trans (cg (fun t => t ◇ (((q63 ◇ q62) ◇ (q62 ◇ q63)) ◇ (((q63 ◇ q62) ◇ (q62 ◇ q63)) ◇ (q63 ◇ ((q63 ◇ q62) ◇ (q62 ◇ q63)))))) (cg (fun t => t ◇ (q63 ◇ ((q63 ◇ q62) ◇ (q62 ◇ q63)))) (apc27 q62 q63)))).trans (cg (fun t => (((q63 ◇ q62) ◇ (q62 ◇ q63)) ◇ (q63 ◇ ((q63 ◇ q62) ◇ (q62 ◇ q63)))) ◇ t) (apc38 q62 q63))))).symm
  have apc142:=fun (q51 q52 q62 q63:G)=>by
    exact ((cg (fun t => ((q51 ◇ q52) ◇ (q52 ◇ q51)) ◇ t) (apc141 q52 q51)).symm).trans ((apc86 q51 q52).trans (apc141 q52 q51))
  have apc143:=fun (q64 q65:G)=>by
    exact (((((cg (fun t => ((q64 ◇ q64) ◇ ((q64 ◇ q64) ◇ (q64 ◇ q64))) ◇ t) (cg (fun t => q65 ◇ t) (cg (fun t => t ◇ ((q64 ◇ q64) ◇ ((q64 ◇ q64) ◇ (q64 ◇ q64)))) (cg (fun t => (q64 ◇ q64) ◇ t) (cg (fun t => t ◇ q64) (apc0 q64 q64)))))).trans (cg (fun t => ((q64 ◇ q64) ◇ ((q64 ◇ q64) ◇ (q64 ◇ q64))) ◇ t) (cg (fun t => q65 ◇ t) (cg (fun t => ((q64 ◇ q64) ◇ (q64 ◇ q64)) ◇ t) (apc0 q64 q64))))).trans (cg (fun t => ((q64 ◇ q64) ◇ ((q64 ◇ q64) ◇ (q64 ◇ q64))) ◇ t) (cg (fun t => q65 ◇ t) (apc27 q64 q64)))).trans (cg (fun t => t ◇ (q65 ◇ ((q64 ◇ q64) ◇ (q64 ◇ q64)))) (apc0 q64 q64))).symm).trans (((cg (fun t => ((q64 ◇ q64) ◇ ((q64 ◇ q64) ◇ (q64 ◇ q64))) ◇ t) (cg (fun t => q65 ◇ t) (cg (fun t => ((q64 ◇ q64) ◇ (((q64 ◇ q64) ◇ ((q64 ◇ q64) ◇ (q64 ◇ q64))) ◇ q64)) ◇ t) (apc142 (q64 ◇ q64) (((q64 ◇ q64) ◇ ((q64 ◇ q64) ◇ (q64 ◇ q64))) ◇ q64) q64 q64)))).symm).trans (apc111 (q64 ◇ q64) q64 ((q64 ◇ q64) ◇ (((q64 ◇ q64) ◇ ((q64 ◇ q64) ◇ (q64 ◇ q64))) ◇ q64)) q64 q65))
  have apc144:=fun (q66 q67:G)=>by
    exact (((cg (fun t => (((q66 ◇ q66) ◇ q67) ◇ (q67 ◇ (q66 ◇ q66))) ◇ t) (apc0 q66 q66)).symm).trans (apc142 (q66 ◇ q66) q67 q66 q66)).trans (apc0 q66 q66)
  have apc146:=fun (q68:G)=>by
    exact (((cg (fun t => (q68 ◇ q68) ◇ t) (cg (fun t => (q68 ◇ q68) ◇ t) (apc142 q68 (q68 ◇ q68) q68 q68))).symm).trans (apc4 q68 (q68 ◇ q68))).symm
  have apc148:=fun (q69:G)=>by
    exact (((cg (fun t => (q69 ◇ q69) ◇ t) (cg (fun t => t ◇ ((q69 ◇ q69) ◇ (q69 ◇ q69))) (apc144 q69 (q69 ◇ q69)))).symm).trans (apc95 q69 q69)).trans (cg (fun t => t ◇ ((q69 ◇ q69) ◇ (q69 ◇ q69))) (apc144 q69 (q69 ◇ q69)))
  have apc150:=fun (q70 q71:G)=>by
    exact ((cg (fun t => (q70 ◇ (q70 ◇ q70)) ◇ t) (cg (fun t => q71 ◇ t) (cg (fun t => (q70 ◇ q70) ◇ t) (apc142 q70 (q70 ◇ q70) q70 q70)))).symm).trans (apc6 q70 (q70 ◇ q70) q71)
  have apc151:=fun (q72:G)=>by
    exact ((cg (fun t => t ◇ (q72 ◇ (q72 ◇ q72))) (apc0 (q72 ◇ (q72 ◇ q72)) (q72 ◇ q72))).symm).trans ((((cg (fun t => t ◇ (q72 ◇ (q72 ◇ q72))) (cg (fun t => t ◇ (((q72 ◇ (q72 ◇ q72)) ◇ (q72 ◇ q72)) ◇ ((q72 ◇ q72) ◇ (q72 ◇ (q72 ◇ q72))))) (apc150 q72 ((q72 ◇ (q72 ◇ q72)) ◇ (q72 ◇ q72))))).symm).trans (apc33 (q72 ◇ q72) (q72 ◇ (q72 ◇ q72)))).trans ((cg (fun t => t ◇ (((q72 ◇ (q72 ◇ q72)) ◇ (q72 ◇ q72)) ◇ ((q72 ◇ q72) ◇ (q72 ◇ (q72 ◇ q72))))) (apc150 q72 ((q72 ◇ (q72 ◇ q72)) ◇ (q72 ◇ q72)))).trans (apc0 (q72 ◇ (q72 ◇ q72)) (q72 ◇ q72))))
  have apc153:=fun (q68 q72:G)=>by
    exact (apc146 q68).trans (cg (fun t => (q68 ◇ q68) ◇ t) (apc151 q68))
  have apc154:=fun (q73 q74:G)=>by
    exact (((cg (fun t => (q73 ◇ (q73 ◇ q73)) ◇ t) (cg (fun t => q74 ◇ t) (cg (fun t => (q73 ◇ q73) ◇ t) (apc142 q73 q73 (((q73 ◇ q73) ◇ (q73 ◇ q73)) ◇ (q73 ◇ (q73 ◇ q73))) (((q73 ◇ q73) ◇ (q73 ◇ q73)) ◇ (q73 ◇ (q73 ◇ q73))))))).trans (cg (fun t => (q73 ◇ (q73 ◇ q73)) ◇ t) (cg (fun t => q74 ◇ t) (apc151 q73)))).symm).trans (((cg (fun t => (q73 ◇ (q73 ◇ q73)) ◇ t) (cg (fun t => q74 ◇ t) (cg (fun t => (q73 ◇ q73) ◇ t) (cg (fun t => t ◇ (q73 ◇ (q73 ◇ q73))) (apc153 q73 q73))))).symm).trans (apc6 q73 (q73 ◇ q73) q74))
  have apc155:=fun (q75:G)=>by
    exact ((cg (fun t => q75 ◇ t) (cg (fun t => (q75 ◇ (q75 ◇ q75)) ◇ t) (apc154 q75 q75))).symm).trans ((((cg (fun t => t ◇ ((q75 ◇ (q75 ◇ q75)) ◇ ((q75 ◇ (q75 ◇ q75)) ◇ (q75 ◇ (q75 ◇ q75))))) (apc154 q75 q75)).symm).trans (apc151 (q75 ◇ (q75 ◇ q75)))).trans (apc154 q75 q75))
  have apc156:=fun (q76 q77:G)=>by
    exact ((cg (fun t => ((q76 ◇ (q76 ◇ q76)) ◇ q76) ◇ t) (cg (fun t => q77 ◇ t) (apc154 q76 q76))).symm).trans (((cg (fun t => t ◇ (q77 ◇ ((q76 ◇ (q76 ◇ q76)) ◇ (q76 ◇ (q76 ◇ q76))))) (cg (fun t => (q76 ◇ (q76 ◇ q76)) ◇ t) (apc154 q76 q76))).symm).trans (apc154 (q76 ◇ (q76 ◇ q76)) q77))
  have apc157:=fun (q78:G)=>by
    exact ((cg (fun t => t ◇ (q78 ◇ q78)) (cg (fun t => t ◇ (q78 ◇ q78)) (apc142 q78 q78 (((q78 ◇ q78) ◇ (q78 ◇ q78)) ◇ (q78 ◇ (q78 ◇ q78))) (((q78 ◇ q78) ◇ (q78 ◇ q78)) ◇ (q78 ◇ (q78 ◇ q78)))))).symm).trans (((cg (fun t => t ◇ (q78 ◇ q78)) (cg (fun t => (((q78 ◇ q78) ◇ (q78 ◇ q78)) ◇ (q78 ◇ (q78 ◇ q78))) ◇ t) (apc154 q78 (q78 ◇ q78)))).symm).trans (apc144 (q78 ◇ q78) (q78 ◇ (q78 ◇ q78))))
  have apc158:=fun (q79:G)=>by
    exact (((cg (fun t => t ◇ ((q79 ◇ (q79 ◇ q79)) ◇ (q79 ◇ (q79 ◇ q79)))) (cg (fun t => ((q79 ◇ (q79 ◇ q79)) ◇ q79) ◇ t) (apc154 q79 q79))).trans (cg (fun t => (((q79 ◇ (q79 ◇ q79)) ◇ q79) ◇ q79) ◇ t) (apc154 q79 q79))).symm).trans ((((cg (fun t => t ◇ ((q79 ◇ (q79 ◇ q79)) ◇ (q79 ◇ (q79 ◇ q79)))) (cg (fun t => t ◇ ((q79 ◇ (q79 ◇ q79)) ◇ (q79 ◇ (q79 ◇ q79)))) (cg (fun t => (q79 ◇ (q79 ◇ q79)) ◇ t) (apc154 q79 q79)))).symm).trans (apc157 (q79 ◇ (q79 ◇ q79)))).trans (apc154 q79 q79))
  have apc159:=fun (q80 q81:G)=>by
    exact (((cg (fun t => ((q81 ◇ (q81 ◇ q81)) ◇ q81) ◇ t) (apc144 q81 q80)).symm).trans (apc156 q81 (((q81 ◇ q81) ◇ q80) ◇ (q80 ◇ (q81 ◇ q81))))).symm
  have apc160:=fun (q82:G)=>by
    exact ((cg (fun t => q82 ◇ t) (apc159 (q82 ◇ q82) q82)).symm).trans ((h ((q82 ◇ q82) ◇ (q82 ◇ q82)) q82 q82).symm)
  have apc163:=fun (q83:G)=>by
    exact ((((cg (fun t => q83 ◇ t) (cg (fun t => t ◇ (((q83 ◇ (q83 ◇ q83)) ◇ q83) ◇ q83)) (apc155 q83))).trans (cg (fun t => q83 ◇ t) (apc160 q83))).symm).trans (((cg (fun t => t ◇ ((q83 ◇ ((q83 ◇ (q83 ◇ q83)) ◇ q83)) ◇ (((q83 ◇ (q83 ◇ q83)) ◇ q83) ◇ q83))) (apc155 q83)).symm).trans (apc0 q83 ((q83 ◇ (q83 ◇ q83)) ◇ q83)))).symm
  have apc164:=fun (q84 q85:G)=>by
    exact ((cg (fun t => t ◇ (q85 ◇ q84)) (apc163 q84)).symm).trans (apc156 q84 q85)
  have apc165:=fun (q86:G)=>by
    exact ((cg (fun t => t ◇ q86) (cg (fun t => t ◇ q86) (apc163 q86))).symm).trans (apc158 q86)
  have apc166:=fun (q87:G)=>by
    exact (((cg (fun t => (q87 ◇ ((q87 ◇ q87) ◇ (q87 ◇ q87))) ◇ t) (apc158 q87)).symm).trans (apc164 q87 (((q87 ◇ (q87 ◇ q87)) ◇ q87) ◇ q87))).symm
  have apc167:=fun (q88 q89:G)=>by
    exact (((((((cg (fun t => (((q88 ◇ ((q88 ◇ q88) ◇ (q88 ◇ q88))) ◇ q88) ◇ (q88 ◇ ((q88 ◇ (q88 ◇ q88)) ◇ q88))) ◇ t) (cg (fun t => t ◇ (q89 ◇ ((((q88 ◇ (q88 ◇ q88)) ◇ q88) ◇ q88) ◇ (q88 ◇ ((q88 ◇ (q88 ◇ q88)) ◇ q88))))) (cg (fun t => t ◇ q89) (cg (fun t => (((q88 ◇ (q88 ◇ q88)) ◇ q88) ◇ q88) ◇ t) (apc155 q88))))).trans (cg (fun t => (((q88 ◇ ((q88 ◇ q88) ◇ (q88 ◇ q88))) ◇ q88) ◇ (q88 ◇ ((q88 ◇ (q88 ◇ q88)) ◇ q88))) ◇ t) (cg (fun t => (((((q88 ◇ (q88 ◇ q88)) ◇ q88) ◇ q88) ◇ q88) ◇ q89) ◇ t) (cg (fun t => q89 ◇ t) (cg (fun t => (((q88 ◇ (q88 ◇ q88)) ◇ q88) ◇ q88) ◇ t) (apc155 q88)))))).trans (cg (fun t => (((q88 ◇ ((q88 ◇ q88) ◇ (q88 ◇ q88))) ◇ q88) ◇ (q88 ◇ ((q88 ◇ (q88 ◇ q88)) ◇ q88))) ◇ t) (cg (fun t => t ◇ (q89 ◇ ((((q88 ◇ (q88 ◇ q88)) ◇ q88) ◇ q88) ◇ q88))) (cg (fun t => t ◇ q89) (apc158 q88))))).trans (cg (fun t => (((q88 ◇ ((q88 ◇ q88) ◇ (q88 ◇ q88))) ◇ q88) ◇ (q88 ◇ ((q88 ◇ (q88 ◇ q88)) ◇ q88))) ◇ t) (cg (fun t => (q88 ◇ q89) ◇ t) (cg (fun t => q89 ◇ t) (apc158 q88))))).trans (cg (fun t => t ◇ ((q88 ◇ q89) ◇ (q89 ◇ q88))) (cg (fun t => ((q88 ◇ ((q88 ◇ q88) ◇ (q88 ◇ q88))) ◇ q88) ◇ t) (apc155 q88)))).trans (cg (fun t => t ◇ ((q88 ◇ q89) ◇ (q89 ◇ q88))) (apc165 q88))).symm).trans (((cg (fun t => t ◇ ((((((q88 ◇ (q88 ◇ q88)) ◇ q88) ◇ q88) ◇ (q88 ◇ ((q88 ◇ (q88 ◇ q88)) ◇ q88))) ◇ q89) ◇ (q89 ◇ ((((q88 ◇ (q88 ◇ q88)) ◇ q88) ◇ q88) ◇ (q88 ◇ ((q88 ◇ (q88 ◇ q88)) ◇ q88)))))) (cg (fun t => t ◇ (q88 ◇ ((q88 ◇ (q88 ◇ q88)) ◇ q88))) (apc166 q88))).symm).trans (apc47 q88 ((q88 ◇ (q88 ◇ q88)) ◇ q88) q89))
  have apc173:=fun (q90 q91:G)=>by
    exact (((cg (fun t => (((q91 ◇ q90) ◇ (q90 ◇ q91)) ◇ ((q91 ◇ q90) ◇ (q90 ◇ q91))) ◇ t) (apc47 q90 q91 ((q91 ◇ q90) ◇ (q90 ◇ q91)))).symm).trans (apc148 ((q91 ◇ q90) ◇ (q90 ◇ q91)))).trans (apc47 q90 q91 ((q91 ◇ q90) ◇ (q90 ◇ q91)))
  have apc183:=fun (q92 q93:G)=>by
    exact (((cg (fun t => q92 ◇ t) (apc156 (q93 ◇ q92) (q92 ◇ q93))).symm).trans ((h (((q93 ◇ q92) ◇ ((q93 ◇ q92) ◇ (q93 ◇ q92))) ◇ (q93 ◇ q92)) q92 q93).symm)).symm
  have apc185:=fun (q94 q95 q96:G)=>by
    exact ((cg (fun t => t ◇ (q96 ◇ (q95 ◇ q94))) (apc183 q94 q95)).symm).trans (apc156 (q95 ◇ q94) q96)
  have apc186:=fun (q97 q98:G)=>by
    exact ((cg (fun t => (q97 ◇ (q97 ◇ q98)) ◇ t) (apc156 q97 q98)).symm).trans (apc185 q97 q98 ((q97 ◇ (q97 ◇ q97)) ◇ q97))
  have apc191:=fun (q99 q100 q101:G)=>by
    exact ((cg (fun t => t ◇ q101) (apc183 (q100 ◇ q99) q101)).symm).trans (((cg (fun t => (((q101 ◇ (q100 ◇ q99)) ◇ ((q101 ◇ (q100 ◇ q99)) ◇ (q101 ◇ (q100 ◇ q99)))) ◇ (q101 ◇ (q100 ◇ q99))) ◇ t) (apc185 q99 q100 q101)).symm).trans (apc156 (q101 ◇ (q100 ◇ q99)) (q99 ◇ (q99 ◇ q100))))
  have apc194:=fun (q94 q95:G)=>by
    exact (((cg (fun t => t ◇ (q94 ◇ (q94 ◇ q95))) (apc191 q94 q95 (q95 ◇ q94))).symm).trans (((cg (fun t => (((q95 ◇ q94) ◇ ((q95 ◇ q94) ◇ (q95 ◇ q94))) ◇ (q95 ◇ q94)) ◇ t) (apc183 q94 q95)).symm).trans (apc156 (q95 ◇ q94) ((q95 ◇ q94) ◇ ((q95 ◇ q94) ◇ (q95 ◇ q94)))))).symm
  have apc199:=fun (q102 q103 q104:G)=>by
    exact (((cg (fun t => q103 ◇ t) (apc186 q102 ((q103 ◇ q104) ◇ (q104 ◇ q103)))).symm).trans ((h (q102 ◇ (q102 ◇ ((q103 ◇ q104) ◇ (q104 ◇ q103)))) q103 q104).symm)).symm
  have apc201:=fun (q105:G)=>by
    exact ((cg (fun t => (q105 ◇ q105) ◇ t) (apc185 q105 q105 q105)).symm).trans ((((cg (fun t => (q105 ◇ q105) ◇ t) (apc194 q105 q105)).symm).trans (apc199 (q105 ◇ q105) q105 q105)).trans (cg (fun t => q105 ◇ t) (cg (fun t => t ◇ (q105 ◇ q105)) (apc0 q105 q105))))
  have apc205:=fun (q106:G)=>by
    exact ((((cg (fun t => ((q106 ◇ q106) ◇ ((q106 ◇ q106) ◇ (q106 ◇ q106))) ◇ t) (cg (fun t => (q106 ◇ q106) ◇ t) (apc0 q106 q106))).trans (cg (fun t => t ◇ ((q106 ◇ q106) ◇ q106)) (apc0 q106 q106))).symm).trans (((cg (fun t => ((q106 ◇ q106) ◇ ((q106 ◇ q106) ◇ (q106 ◇ q106))) ◇ t) (apc201 (q106 ◇ q106))).symm).trans (apc159 ((q106 ◇ q106) ◇ (q106 ◇ q106)) q106))).symm
  have apc228:=fun (q107:G)=>by
    exact (((cg (fun t => t ◇ ((q107 ◇ q107) ◇ (q107 ◇ q107))) (cg (fun t => t ◇ ((q107 ◇ q107) ◇ (q107 ◇ q107))) (apc173 q107 q107))).trans (cg (fun t => t ◇ ((q107 ◇ q107) ◇ (q107 ◇ q107))) (apc167 q107 q107))).symm).trans (((cg (fun t => t ◇ ((q107 ◇ q107) ◇ (q107 ◇ q107))) (cg (fun t => ((((q107 ◇ q107) ◇ (q107 ◇ q107)) ◇ ((q107 ◇ q107) ◇ (q107 ◇ q107))) ◇ q107) ◇ t) (apc143 q107 ((q107 ◇ q107) ◇ (q107 ◇ q107))))).symm).trans (apc144 ((q107 ◇ q107) ◇ (q107 ◇ q107)) q107))
  have apc229:=fun (q108 q109:G)=>by
    exact (((apc47 q108 q109 ((q109 ◇ q108) ◇ (q108 ◇ q109))).symm).trans ((((cg (fun t => ((q109 ◇ q108) ◇ (q108 ◇ q109)) ◇ t) (apc228 ((q109 ◇ q108) ◇ (q108 ◇ q109)))).symm).trans (apc56 q108 q109 ((q109 ◇ q108) ◇ (q108 ◇ q109)) ((((q109 ◇ q108) ◇ (q108 ◇ q109)) ◇ (((q109 ◇ q108) ◇ (q108 ◇ q109)) ◇ ((q109 ◇ q108) ◇ (q108 ◇ q109)))) ◇ ((q109 ◇ q108) ◇ (q108 ◇ q109))) q108 q108 q108)).trans (((cg (fun t => t ◇ ((q109 ◇ q108) ◇ (q108 ◇ q109))) (apc194 (q108 ◇ q109) (q109 ◇ q108))).trans (cg (fun t => t ◇ ((q109 ◇ q108) ◇ (q108 ◇ q109))) (cg (fun t => t ◇ ((q108 ◇ q109) ◇ ((q108 ◇ q109) ◇ (q109 ◇ q108)))) (apc0 q108 q109)))).trans (cg (fun t => t ◇ ((q109 ◇ q108) ◇ (q108 ◇ q109))) (cg (fun t => q109 ◇ t) (apc0 q108 q109)))))).symm
  have apc230:=fun (q110 q111:G)=>by
    exact ((cg (fun t => (q111 ◇ (((q111 ◇ q110) ◇ (q110 ◇ q111)) ◇ (q111 ◇ q111))) ◇ t) (apc0 q111 q111)).symm).trans ((((cg (fun t => t ◇ ((q111 ◇ q111) ◇ ((q111 ◇ q111) ◇ (q111 ◇ q111)))) (cg (fun t => t ◇ (((q111 ◇ q110) ◇ (q110 ◇ q111)) ◇ (q111 ◇ q111))) (apc229 q110 q111))).symm).trans (apc142 (q111 ◇ q111) ((q111 ◇ q110) ◇ (q110 ◇ q111)) q110 q110)).trans (apc0 q111 q111))
  have apc231:=fun (q112 q113:G)=>by
    exact (((apc205 q113).symm).trans (((cg (fun t => ((q113 ◇ (q113 ◇ q113)) ◇ q113) ◇ t) (apc230 q112 q113)).symm).trans (apc156 q113 (q113 ◇ (((q113 ◇ q112) ◇ (q112 ◇ q113)) ◇ (q113 ◇ q113)))))).symm
  have apc233:=fun (q114 q115:G)=>by
    exact (((cg (fun t => q115 ◇ t) (cg (fun t => t ◇ (((q115 ◇ q114) ◇ (q114 ◇ q115)) ◇ (q115 ◇ q115))) (apc229 q114 q115))).trans (cg (fun t => q115 ◇ t) (apc231 q114 q115))).symm).trans (((cg (fun t => t ◇ (((q115 ◇ q115) ◇ ((q115 ◇ q114) ◇ (q114 ◇ q115))) ◇ (((q115 ◇ q114) ◇ (q114 ◇ q115)) ◇ (q115 ◇ q115)))) (apc229 q114 q115)).symm).trans (apc0 (q115 ◇ q115) ((q115 ◇ q114) ◇ (q114 ◇ q115))))
  have apc234:=fun (q114 q115:G)=>by
    exact (((apc233 q114 q115).symm).trans (apc233 q115 q115)).symm
  have apc237:=fun (q116 q117:G)=>by
    exact ((cg (fun t => (q116 ◇ q117) ◇ t) ((apc234 q117 q116).symm)).symm).trans (apc0 q116 q117)
  have apc243:=fun (q118 q119:G)=>by
    exact (((cg (fun t => (((q118 ◇ (q118 ◇ q118)) ◇ q118) ◇ q119) ◇ t) (cg (fun t => (q118 ◇ (q118 ◇ q118)) ◇ t) (apc156 q118 (q118 ◇ (q118 ◇ q118))))).trans (cg (fun t => (((q118 ◇ (q118 ◇ q118)) ◇ q118) ◇ q119) ◇ t) (apc185 q118 q118 q118))).symm).trans (((cg (fun t => (((q118 ◇ (q118 ◇ q118)) ◇ q118) ◇ q119) ◇ t) (cg (fun t => t ◇ (((q118 ◇ (q118 ◇ q118)) ◇ q118) ◇ ((q118 ◇ (q118 ◇ q118)) ◇ q118))) (apc156 q118 (q118 ◇ (q118 ◇ q118))))).symm).trans (apc237 ((q118 ◇ (q118 ◇ q118)) ◇ q118) q119))
  exact (calc
    x=x:=rfl
    _=((((y ◇ (y ◇ z)) ◇ z) ◇ x) ◇ y):=((cg (fun t => t ◇ y) (cg (fun t => t ◇ x) (apc186 y z))).trans (apc243 y x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_6718_to_40238 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_6718_to_40238
