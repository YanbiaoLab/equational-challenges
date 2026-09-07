-- Equation19021 → Equation52524
-- Recorded verdict: true
-- Premise: x = (y * x) * ((z * y) * (x * x))
-- Conclusion: x * y = ((y * (z * z)) * z) * y
-- Original submission SHA-256: 8cc7b3519e1409ee516b0c7485db795789ba1c693bc0ae7f670889dec4ed2cd8
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ x) ◇ ((z ◇ y) ◇ (x ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = ((y ◇ (z ◇ z)) ◇ z) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a=b → f a=f b:=by
    intro f a b p
    exact congrArg f p
  have apc0:=fun (q0:G)=>by
    exact ((cg (fun t => (q0 ◇ (q0 ◇ q0)) ◇ t) ((h q0 q0 q0).symm)).symm).trans ((h (q0 ◇ q0) q0 q0).symm)
  have apc1:=fun (q1:G)=>by
    exact (((cg (fun t => t ◇ (q1 ◇ q1)) ((h q1 q1 q1).symm)).symm).trans (apc0 (q1 ◇ q1))).symm
  have apc2:=fun (q2:G)=>by
    exact ((cg (fun t => (q2 ◇ q2) ◇ t) (apc1 q2)).symm).trans ((h q2 q2 q2).symm)
  have apc4:=fun (q3:G)=>by
    exact ((cg (fun t => (q3 ◇ (q3 ◇ q3)) ◇ t) (apc1 q3)).symm).trans ((((cg (fun t => t ◇ ((q3 ◇ q3) ◇ (q3 ◇ q3))) (apc1 q3)).symm).trans (apc1 (q3 ◇ q3))).trans ((cg (fun t => (q3 ◇ q3) ◇ t) (apc1 q3)).trans (apc2 q3)))
  have apc5:=fun (q4 q5:G)=>by
    exact ((cg (fun t => q4 ◇ t) (cg (fun t => (q5 ◇ (q4 ◇ (q4 ◇ q4))) ◇ t) (apc4 q4))).symm).trans (((cg (fun t => t ◇ ((q5 ◇ (q4 ◇ (q4 ◇ q4))) ◇ ((q4 ◇ (q4 ◇ q4)) ◇ (q4 ◇ (q4 ◇ q4))))) (apc4 q4)).symm).trans ((h (q4 ◇ (q4 ◇ q4)) (q4 ◇ (q4 ◇ q4)) q5).symm))
  have apc6:=fun (q6 q7:G)=>by
    exact ((cg (fun t => (q6 ◇ q6) ◇ t) (cg (fun t => t ◇ (q6 ◇ q6)) (cg (fun t => q7 ◇ t) (apc2 q6)))).symm).trans ((((cg (fun t => (q6 ◇ q6) ◇ t) (cg (fun t => t ◇ (q6 ◇ q6)) (cg (fun t => q7 ◇ t) (cg (fun t => (q6 ◇ q6) ◇ t) (apc1 q6))))).symm).trans (apc5 (q6 ◇ q6) q7)).trans ((cg (fun t => (q6 ◇ q6) ◇ t) (apc1 q6)).trans (apc2 q6)))
  have apc7:=fun (q8 q9:G)=>by
    exact ((cg (fun t => ((q8 ◇ (q8 ◇ q8)) ◇ q9) ◇ t) (cg (fun t => t ◇ (q9 ◇ q9)) (apc2 q8))).symm).trans ((h q9 (q8 ◇ (q8 ◇ q8)) (q8 ◇ q8)).symm)
  have apc9:=fun (q10 q11 q12:G)=>by
    exact ((cg (fun t => ((q10 ◇ (q11 ◇ q11)) ◇ q12) ◇ t) (cg (fun t => t ◇ (q12 ◇ q12)) (apc7 q10 q11))).symm).trans ((h q12 (q10 ◇ (q11 ◇ q11)) ((q10 ◇ (q10 ◇ q10)) ◇ q11)).symm)
  have apc10:=fun (q13 q14:G)=>by
    exact ((cg (fun t => t ◇ ((q14 ◇ (q13 ◇ (q13 ◇ q13))) ◇ (q13 ◇ q13))) (apc0 q13)).symm).trans ((h q13 (q13 ◇ (q13 ◇ q13)) q14).symm)
  have apc11:=fun (q15 q16:G)=>by
    exact ((((cg (fun t => q15 ◇ t) (cg (fun t => t ◇ ((q15 ◇ (q15 ◇ q15)) ◇ (q15 ◇ (q15 ◇ q15)))) (cg (fun t => q16 ◇ t) (cg (fun t => (q15 ◇ (q15 ◇ q15)) ◇ t) (apc4 q15))))).trans (cg (fun t => q15 ◇ t) (cg (fun t => t ◇ ((q15 ◇ (q15 ◇ q15)) ◇ (q15 ◇ (q15 ◇ q15)))) (cg (fun t => q16 ◇ t) (apc0 q15))))).trans (cg (fun t => q15 ◇ t) (cg (fun t => (q16 ◇ (q15 ◇ q15)) ◇ t) (apc4 q15)))).symm).trans (((cg (fun t => t ◇ ((q16 ◇ ((q15 ◇ (q15 ◇ q15)) ◇ ((q15 ◇ (q15 ◇ q15)) ◇ (q15 ◇ (q15 ◇ q15))))) ◇ ((q15 ◇ (q15 ◇ q15)) ◇ (q15 ◇ (q15 ◇ q15))))) (apc4 q15)).symm).trans (apc10 (q15 ◇ (q15 ◇ q15)) q16))
  have apc12:=fun (q4 q17 q5:G)=>by
    exact ((cg (fun t => (q17 ◇ (q4 ◇ (q4 ◇ q4))) ◇ t) (cg (fun t => (q5 ◇ q17) ◇ t) (apc4 q4))).symm).trans ((h (q4 ◇ (q4 ◇ q4)) q17 q5).symm)
  have apc16:=fun (q18 q19 q20:G)=>by
    exact ((cg (fun t => (q19 ◇ (q18 ◇ q18)) ◇ t) (cg (fun t => (q20 ◇ q19) ◇ t) (apc1 q18))).symm).trans ((h (q18 ◇ q18) q19 q20).symm)
  have apc20:=fun (q21 q22 q23:G)=>by
    exact ((cg (fun t => t ◇ ((q21 ◇ (q21 ◇ q21)) ◇ (q23 ◇ q23))) (cg (fun t => t ◇ q23) (cg (fun t => q22 ◇ t) (apc4 q21)))).symm).trans (apc9 q22 (q21 ◇ (q21 ◇ q21)) q23)
  have apc23:=fun (q24 q25:G)=>by
    exact ((cg (fun t => ((q25 ◇ (q25 ◇ q25)) ◇ (q24 ◇ (q24 ◇ q24))) ◇ t) (cg (fun t => q25 ◇ t) (apc4 q24))).symm).trans (apc7 q25 (q24 ◇ (q24 ◇ q24)))
  have apc25:=fun (q21 q22 q26:G)=>by
    exact ((cg (fun t => ((q22 ◇ (q26 ◇ q26)) ◇ (q21 ◇ (q21 ◇ q21))) ◇ t) (cg (fun t => q26 ◇ t) (apc4 q21))).symm).trans (apc9 q22 q26 (q21 ◇ (q21 ◇ q21)))
  have apc30:=fun (q27 q28 q29 q0:G)=>by
    exact ((cg (fun t => t ◇ ((q0 ◇ (q28 ◇ q27)) ◇ (((q29 ◇ q28) ◇ (q27 ◇ q27)) ◇ ((q29 ◇ q28) ◇ (q27 ◇ q27))))) ((h q27 q28 q29).symm)).symm).trans ((h ((q29 ◇ q28) ◇ (q27 ◇ q27)) (q28 ◇ q27) q0).symm)
  have apc32:=fun (q30 q31:G)=>by
    exact (((cg (fun t => (q30 ◇ (q30 ◇ q30)) ◇ t) (cg (fun t => t ◇ ((q31 ◇ q30) ◇ (q31 ◇ q30))) (cg (fun t => (q30 ◇ (q30 ◇ q30)) ◇ t) (apc4 q30)))).trans (cg (fun t => (q30 ◇ (q30 ◇ q30)) ◇ t) (cg (fun t => t ◇ ((q31 ◇ q30) ◇ (q31 ◇ q30))) (apc0 q30)))).symm).trans (((cg (fun t => t ◇ (((q30 ◇ (q30 ◇ q30)) ◇ ((q30 ◇ (q30 ◇ q30)) ◇ (q30 ◇ (q30 ◇ q30)))) ◇ ((q31 ◇ q30) ◇ (q31 ◇ q30)))) (apc23 q30 q31)).symm).trans (apc20 (q30 ◇ (q30 ◇ q30)) (q31 ◇ (q31 ◇ q31)) (q31 ◇ q30)))
  have apc37:=fun (q32 q33:G)=>by
    exact ((cg (fun t => t ◇ ((q33 ◇ (q33 ◇ q33)) ◇ ((q32 ◇ (q33 ◇ q33)) ◇ (q32 ◇ (q33 ◇ q33))))) (apc9 q32 q32 q33)).symm).trans (apc20 q33 (q32 ◇ (q32 ◇ q32)) (q32 ◇ (q33 ◇ q33)))
  have apc38:=fun (q34 q35:G)=>by
    exact ((cg (fun t => t ◇ ((q35 ◇ q34) ◇ ((q35 ◇ q34) ◇ (q35 ◇ q34)))) (cg (fun t => q34 ◇ t) (apc4 (q35 ◇ q34)))).symm).trans ((((cg (fun t => (q34 ◇ (((q35 ◇ q34) ◇ ((q35 ◇ q34) ◇ (q35 ◇ q34))) ◇ ((q35 ◇ q34) ◇ ((q35 ◇ q34) ◇ (q35 ◇ q34))))) ◇ t) (apc37 (q35 ◇ q34) (q35 ◇ q34))).symm).trans (apc16 ((q35 ◇ q34) ◇ ((q35 ◇ q34) ◇ (q35 ◇ q34))) q34 q35)).trans (apc4 (q35 ◇ q34)))
  have apc51:=fun (q36 q37:G)=>by
    exact (((cg (fun t => ((q37 ◇ q36) ◇ ((q37 ◇ q36) ◇ (q37 ◇ q36))) ◇ t) (cg (fun t => ((q37 ◇ q36) ◇ (q37 ◇ q36)) ◇ t) (cg (fun t => (q36 ◇ (q36 ◇ q36)) ◇ t) (apc25 q36 q36 q37)))).trans (cg (fun t => ((q37 ◇ q36) ◇ ((q37 ◇ q36) ◇ (q37 ◇ q36))) ◇ t) (cg (fun t => ((q37 ◇ q36) ◇ (q37 ◇ q36)) ◇ t) (apc4 q36)))).symm).trans ((((cg (fun t => ((q37 ◇ q36) ◇ ((q37 ◇ q36) ◇ (q37 ◇ q36))) ◇ t) (cg (fun t => ((q37 ◇ q36) ◇ (q37 ◇ q36)) ◇ t) (cg (fun t => t ◇ (((q36 ◇ (q37 ◇ q37)) ◇ (q36 ◇ (q36 ◇ q36))) ◇ (q37 ◇ q36))) (apc25 q36 q36 q37)))).symm).trans (apc32 (q37 ◇ q36) ((q36 ◇ (q37 ◇ q37)) ◇ (q36 ◇ (q36 ◇ q36))))).trans (apc25 q36 q36 q37))
  have apc52:=fun (q38 q39:G)=>by
    exact (((((((((cg (fun t => t ◇ (((((q38 ◇ (q39 ◇ q39)) ◇ (q38 ◇ (q38 ◇ q38))) ◇ (q39 ◇ q38)) ◇ (((q38 ◇ (q39 ◇ q39)) ◇ (q38 ◇ (q38 ◇ q38))) ◇ (q39 ◇ q38))) ◇ (q39 ◇ q38))) (cg (fun t => (q38 ◇ (q38 ◇ q38)) ◇ t) (cg (fun t => t ◇ (((q38 ◇ (q39 ◇ q39)) ◇ (q38 ◇ (q38 ◇ q38))) ◇ (q39 ◇ q38))) (apc25 q38 q38 q39)))).trans (cg (fun t => t ◇ (((((q38 ◇ (q39 ◇ q39)) ◇ (q38 ◇ (q38 ◇ q38))) ◇ (q39 ◇ q38)) ◇ (((q38 ◇ (q39 ◇ q39)) ◇ (q38 ◇ (q38 ◇ q38))) ◇ (q39 ◇ q38))) ◇ (q39 ◇ q38))) (cg (fun t => (q38 ◇ (q38 ◇ q38)) ◇ t) (cg (fun t => (q38 ◇ (q38 ◇ q38)) ◇ t) (apc25 q38 q38 q39))))).trans (cg (fun t => ((q38 ◇ (q38 ◇ q38)) ◇ ((q38 ◇ (q38 ◇ q38)) ◇ (q38 ◇ (q38 ◇ q38)))) ◇ t) (cg (fun t => t ◇ (q39 ◇ q38)) (cg (fun t => t ◇ (((q38 ◇ (q39 ◇ q39)) ◇ (q38 ◇ (q38 ◇ q38))) ◇ (q39 ◇ q38))) (apc25 q38 q38 q39))))).trans (cg (fun t => ((q38 ◇ (q38 ◇ q38)) ◇ ((q38 ◇ (q38 ◇ q38)) ◇ (q38 ◇ (q38 ◇ q38)))) ◇ t) (cg (fun t => t ◇ (q39 ◇ q38)) (cg (fun t => (q38 ◇ (q38 ◇ q38)) ◇ t) (apc25 q38 q38 q39))))).trans (cg (fun t => t ◇ (((q38 ◇ (q38 ◇ q38)) ◇ (q38 ◇ (q38 ◇ q38))) ◇ (q39 ◇ q38))) (cg (fun t => (q38 ◇ (q38 ◇ q38)) ◇ t) (apc4 q38)))).trans (cg (fun t => ((q38 ◇ (q38 ◇ q38)) ◇ q38) ◇ t) (cg (fun t => t ◇ (q39 ◇ q38)) (apc4 q38)))).trans (cg (fun t => t ◇ (q38 ◇ (q39 ◇ q38))) (apc0 q38))).symm).trans (((cg (fun t => t ◇ (((((q38 ◇ (q39 ◇ q39)) ◇ (q38 ◇ (q38 ◇ q38))) ◇ (q39 ◇ q38)) ◇ (((q38 ◇ (q39 ◇ q39)) ◇ (q38 ◇ (q38 ◇ q38))) ◇ (q39 ◇ q38))) ◇ (q39 ◇ q38))) (cg (fun t => t ◇ ((((q38 ◇ (q39 ◇ q39)) ◇ (q38 ◇ (q38 ◇ q38))) ◇ (q39 ◇ q38)) ◇ (((q38 ◇ (q39 ◇ q39)) ◇ (q38 ◇ (q38 ◇ q38))) ◇ (q39 ◇ q38)))) (apc25 q38 q38 q39))).symm).trans (apc51 (q39 ◇ q38) ((q38 ◇ (q39 ◇ q39)) ◇ (q38 ◇ (q38 ◇ q38)))))).symm
  have apc53:=fun (q40 q41:G)=>by
    exact (((((cg (fun t => q40 ◇ t) (cg (fun t => t ◇ ((q40 ◇ q40) ◇ ((q41 ◇ q40) ◇ (q40 ◇ q40)))) (apc1 q40))).trans (cg (fun t => q40 ◇ t) (cg (fun t => (q40 ◇ (q40 ◇ q40)) ◇ t) (apc6 q40 q41)))).trans (cg (fun t => q40 ◇ t) (apc0 q40))).symm).trans (((cg (fun t => q40 ◇ t) (apc52 (q40 ◇ q40) (q41 ◇ q40))).symm).trans (apc30 q40 q40 q41 (q41 ◇ q40)))).symm
  have apc54:=fun (q42 q43:G)=>by
    exact (((cg (fun t => (q43 ◇ (q42 ◇ (q42 ◇ q42))) ◇ t) (apc4 q42)).symm).trans (apc53 (q42 ◇ (q42 ◇ q42)) q43)).trans ((cg (fun t => (q42 ◇ (q42 ◇ q42)) ◇ t) (apc4 q42)).trans (apc0 q42))
  have apc55:=fun (q44 q45:G)=>by
    exact (((cg (fun t => (q45 ◇ (q44 ◇ q44)) ◇ t) (apc53 q44 q44)).symm).trans (apc53 (q44 ◇ q44) q45)).trans ((cg (fun t => (q44 ◇ q44) ◇ t) (apc53 q44 q44)).trans (apc2 q44))
  have apc56:=fun (q46 q47 q48:G)=>by
    exact ((((cg (fun t => ((q47 ◇ (q47 ◇ q47)) ◇ (q47 ◇ (q47 ◇ q47))) ◇ t) (cg (fun t => t ◇ q47) (cg (fun t => q48 ◇ t) (cg (fun t => q46 ◇ t) (cg (fun t => (q47 ◇ (q47 ◇ q47)) ◇ t) (apc55 q47 q47)))))).trans (cg (fun t => ((q47 ◇ (q47 ◇ q47)) ◇ (q47 ◇ (q47 ◇ q47))) ◇ t) (cg (fun t => t ◇ q47) (cg (fun t => q48 ◇ t) (cg (fun t => q46 ◇ t) (apc0 q47)))))).trans (cg (fun t => t ◇ ((q48 ◇ (q46 ◇ (q47 ◇ q47))) ◇ q47)) (apc55 q47 q47))).symm).trans (((cg (fun t => t ◇ ((q48 ◇ (q46 ◇ ((q47 ◇ (q47 ◇ q47)) ◇ ((q47 ◇ (q47 ◇ q47)) ◇ (q47 ◇ (q47 ◇ q47)))))) ◇ q47)) (apc54 (q47 ◇ (q47 ◇ q47)) q46)).symm).trans (apc12 q47 (q46 ◇ ((q47 ◇ (q47 ◇ q47)) ◇ ((q47 ◇ (q47 ◇ q47)) ◇ (q47 ◇ (q47 ◇ q47))))) q48))
  have apc58:=fun (q38 q39 q34 q35:G)=>by
    exact ((cg (fun t => (q34 ◇ (q35 ◇ q34)) ◇ t) (apc52 q34 q35)).symm).trans (apc38 q34 q35)
  have apc59:=fun (q49 q50:G)=>by
    exact (((((cg (fun t => (q50 ◇ (q50 ◇ q50)) ◇ t) (cg (fun t => (q50 ◇ q50) ◇ t) (apc11 q50 q49))).trans (cg (fun t => (q50 ◇ (q50 ◇ q50)) ◇ t) (apc2 q50))).trans (apc0 q50)).symm).trans (((cg (fun t => t ◇ ((q50 ◇ q50) ◇ (q50 ◇ ((q49 ◇ (q50 ◇ q50)) ◇ q50)))) (apc11 q50 q49)).symm).trans (apc58 q49 q49 q50 (q49 ◇ (q50 ◇ q50))))).symm
  have apc60:=fun (q51 q52:G)=>by
    exact (((((cg (fun t => (q51 ◇ q51) ◇ t) (cg (fun t => t ◇ ((q51 ◇ (q51 ◇ q51)) ◇ ((q52 ◇ q51) ◇ (q51 ◇ (q51 ◇ q51))))) (apc55 q51 q51))).trans (cg (fun t => (q51 ◇ q51) ◇ t) (cg (fun t => q51 ◇ t) (apc16 q51 q51 q52)))).trans (apc2 q51)).symm).trans (((cg (fun t => t ◇ (((q51 ◇ (q51 ◇ q51)) ◇ (q51 ◇ (q51 ◇ q51))) ◇ ((q51 ◇ (q51 ◇ q51)) ◇ ((q52 ◇ q51) ◇ (q51 ◇ (q51 ◇ q51)))))) (apc16 q51 q51 q52)).symm).trans (apc58 q51 q51 (q51 ◇ (q51 ◇ q51)) (q52 ◇ q51)))).symm
  have apc61:=fun (q53 q54 q55:G)=>by
    exact (((cg (fun t => ((q54 ◇ (q54 ◇ q54)) ◇ (q54 ◇ (q54 ◇ q54))) ◇ t) (cg (fun t => t ◇ q54) (cg (fun t => q55 ◇ t) (cg (fun t => q53 ◇ t) (apc55 q54 q54))))).trans (cg (fun t => t ◇ ((q55 ◇ (q53 ◇ q54)) ◇ q54)) (apc55 q54 q54))).symm).trans (((cg (fun t => t ◇ ((q55 ◇ (q53 ◇ ((q54 ◇ (q54 ◇ q54)) ◇ (q54 ◇ (q54 ◇ q54))))) ◇ q54)) (apc59 q53 (q54 ◇ (q54 ◇ q54)))).symm).trans (apc12 q54 (q53 ◇ ((q54 ◇ (q54 ◇ q54)) ◇ (q54 ◇ (q54 ◇ q54)))) q55))
  have apc62:=fun (q56 q57 q58:G)=>by
    exact ((((((cg (fun t => (q58 ◇ (q58 ◇ q58)) ◇ t) (apc52 q58 (q57 ◇ (q56 ◇ q58)))).trans (cg (fun t => (q58 ◇ (q58 ◇ q58)) ◇ t) (cg (fun t => (q58 ◇ q58) ◇ t) (apc61 q56 q58 q57)))).trans (cg (fun t => (q58 ◇ (q58 ◇ q58)) ◇ t) (apc60 q58 q58))).trans (apc59 q58 q58)).symm).trans (((cg (fun t => t ◇ (((q57 ◇ (q56 ◇ q58)) ◇ q58) ◇ (((q57 ◇ (q56 ◇ q58)) ◇ q58) ◇ ((q57 ◇ (q56 ◇ q58)) ◇ q58)))) (apc61 q56 q58 q57)).symm).trans (apc60 ((q57 ◇ (q56 ◇ q58)) ◇ q58) q58))).symm
  have apc63:=fun (q59 q60 q61:G)=>by
    exact (((((cg (fun t => (q61 ◇ (q61 ◇ q61)) ◇ t) (cg (fun t => (q61 ◇ q61) ◇ t) (apc56 q59 q61 q60))).trans (cg (fun t => (q61 ◇ (q61 ◇ q61)) ◇ t) (apc60 q61 q61))).trans (apc62 q61 q61 q61)).symm).trans (((cg (fun t => t ◇ ((q61 ◇ q61) ◇ (q61 ◇ ((q60 ◇ (q59 ◇ (q61 ◇ q61))) ◇ q61)))) (apc56 q59 q61 q60)).symm).trans (apc58 q59 q59 q61 (q60 ◇ (q59 ◇ (q61 ◇ q61)))))).symm
  have apc64:=fun (q62 q63 q64:G)=>by
    exact (((cg (fun t => t ◇ (q62 ◇ (q62 ◇ q62))) (cg (fun t => q64 ◇ t) (cg (fun t => q63 ◇ t) (apc55 q62 q62)))).symm).trans (apc63 q63 q64 (q62 ◇ (q62 ◇ q62)))).trans (apc55 q62 q62)
  have apc67:=fun (q65 q66 q67:G)=>by
    exact ((cg (fun t => t ◇ (q66 ◇ q65)) (cg (fun t => q67 ◇ t) (apc25 q65 q65 q66))).symm).trans (apc62 ((q65 ◇ (q66 ◇ q66)) ◇ (q65 ◇ (q65 ◇ q65))) q67 (q66 ◇ q65))
  have apc68:=fun (q65 q66 q67 q21 q22 q26:G)=>by
    exact ((apc67 q21 q26 (q21 ◇ (q26 ◇ q26))).symm).trans (apc25 q21 q21 q26)
  have apc69:=fun (q68 q69:G)=>by
    exact (((((cg (fun t => (q68 ◇ (q68 ◇ q68)) ◇ t) (cg (fun t => (q68 ◇ (q69 ◇ q68)) ◇ t) (apc68 ((q69 ◇ q68) ◇ (q69 ◇ q68)) ((q69 ◇ q68) ◇ (q69 ◇ q68)) ((q69 ◇ q68) ◇ (q69 ◇ q68)) q68 ((q69 ◇ q68) ◇ (q69 ◇ q68)) q69))).trans (cg (fun t => (q68 ◇ (q68 ◇ q68)) ◇ t) (apc64 q68 q69 q68))).trans (apc62 q68 q68 q68)).symm).trans (((cg (fun t => t ◇ ((q68 ◇ (q69 ◇ q68)) ◇ ((q69 ◇ q68) ◇ (q69 ◇ q68)))) (apc68 q68 q68 q68 q68 q68 q69)).symm).trans ((h (q69 ◇ q68) (q69 ◇ q68) q68).symm))).symm
  exact (apc69 y x).trans ((apc69 y ((y ◇ (z ◇ z)) ◇ z)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_19021_to_52524 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_19021_to_52524
