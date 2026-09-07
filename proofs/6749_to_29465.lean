-- Equation6749 → Equation29465
-- Recorded verdict: true
-- Premise: x = y ◇ (x ◇ ((z ◇ y) ◇ (y ◇ z)))
-- Conclusion: x = (y ◇ (x ◇ (x ◇ (y ◇ x)))) ◇ y
-- Original submission SHA-256: 4762011dad7d97cfa45f9ecd67961e59276cb7506088be9ab12f7ab8520a6337
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (x ◇ ((z ◇ y) ◇ (y ◇ z)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (y ◇ (x ◇ (x ◇ (y ◇ x)))) ◇ y
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
    exact ((cg (fun t => (q0 ◇ q1) ◇ t) ((h ((q1 ◇ q0) ◇ (q0 ◇ q1)) q1 q0).symm)).symm).trans ((h q1 (q0 ◇ q1) (q1 ◇ q0)).symm)
  have apc3:=fun (q2 q0 q1 q3:G)=>by
    exact ((cg (fun t => q3 ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => ((q2 ◇ ((q0 ◇ q3) ◇ (q3 ◇ q0))) ◇ q3) ◇ t) ((h q2 q3 q0).symm)))).symm).trans ((h q1 q3 (q2 ◇ ((q0 ◇ q3) ◇ (q3 ◇ q0)))).symm)
  have apc6:=fun (q4 q5 q6 q7:G)=>by
    exact ((cg (fun t => q7 ◇ t) ((h ((((q4 ◇ q6) ◇ (q6 ◇ q4)) ◇ ((q5 ◇ q7) ◇ (q7 ◇ q5))) ◇ q7) q6 q4).symm)).symm).trans (apc3 ((q4 ◇ q6) ◇ (q6 ◇ q4)) q5 q6 q7)
  have apc7:=fun (q8 q9 q10:G)=>by
    exact ((cg (fun t => (q8 ◇ q9) ◇ t) (cg (fun t => q10 ◇ t) (cg (fun t => (((q9 ◇ q8) ◇ (q8 ◇ q9)) ◇ (q8 ◇ q9)) ◇ t) (apc0 q8 q9)))).symm).trans ((h q10 (q8 ◇ q9) ((q9 ◇ q8) ◇ (q8 ◇ q9))).symm)
  have apc20:=fun (q11 q12 q13 q14 q15:G)=>by
    exact ((cg (fun t => q15 ◇ t) (cg (fun t => t ◇ q15) (cg (fun t => ((q13 ◇ q14) ◇ (q14 ◇ q13)) ◇ t) (cg (fun t => ((q11 ◇ ((q12 ◇ q15) ◇ (q15 ◇ q12))) ◇ q15) ◇ t) ((h q11 q15 q12).symm))))).symm).trans (apc6 q13 (q11 ◇ ((q12 ◇ q15) ◇ (q15 ◇ q12))) q14 q15)
  have apc23:=fun (q16 q17:G)=>by
    exact ((cg (fun t => (((q17 ◇ ((q16 ◇ q17) ◇ (q17 ◇ q16))) ◇ q17) ◇ q17) ◇ t) (apc20 q17 q16 q17 ((q17 ◇ ((q16 ◇ q17) ◇ (q17 ◇ q16))) ◇ q17) q17)).symm).trans (apc7 ((q17 ◇ ((q16 ◇ q17) ◇ (q17 ◇ q16))) ◇ q17) q17 q17)
  have apc24:=fun (q18 q19 q20:G)=>by
    exact ((cg (fun t => ((q19 ◇ ((q18 ◇ q19) ◇ (q19 ◇ q18))) ◇ q19) ◇ t) (cg (fun t => q20 ◇ t) (apc3 q19 q18 ((q19 ◇ ((q18 ◇ q19) ◇ (q19 ◇ q18))) ◇ q19) q19))).symm).trans (((cg (fun t => ((q19 ◇ ((q18 ◇ q19) ◇ (q19 ◇ q18))) ◇ q19) ◇ t) (cg (fun t => q20 ◇ t) (cg (fun t => t ◇ (((q19 ◇ ((q18 ◇ q19) ◇ (q19 ◇ q18))) ◇ q19) ◇ (((q19 ◇ ((q18 ◇ q19) ◇ (q19 ◇ q18))) ◇ q19) ◇ q19))) (apc23 q18 q19)))).symm).trans ((h q20 ((q19 ◇ ((q18 ◇ q19) ◇ (q19 ◇ q18))) ◇ q19) (((q19 ◇ ((q18 ◇ q19) ◇ (q19 ◇ q18))) ◇ q19) ◇ q19)).symm))
  have apc25:=fun (q21 q22:G)=>by
    exact ((apc24 q21 q22 (q22 ◇ (q22 ◇ ((q21 ◇ q22) ◇ (q22 ◇ q21))))).symm).trans (apc0 (q22 ◇ ((q21 ◇ q22) ◇ (q22 ◇ q21))) q22)
  have apc31:=fun (q23 q24 q25 q26:G)=>by
    exact ((cg (fun t => q26 ◇ t) (cg (fun t => t ◇ q26) (cg (fun t => t ◇ ((q25 ◇ q26) ◇ (q26 ◇ q25))) (apc3 q24 q23 ((q24 ◇ ((q23 ◇ q24) ◇ (q24 ◇ q23))) ◇ q24) q24)))).symm).trans (((cg (fun t => q26 ◇ t) (cg (fun t => t ◇ q26) (cg (fun t => t ◇ ((q25 ◇ q26) ◇ (q26 ◇ q25))) (cg (fun t => t ◇ (((q24 ◇ ((q23 ◇ q24) ◇ (q24 ◇ q23))) ◇ q24) ◇ (((q24 ◇ ((q23 ◇ q24) ◇ (q24 ◇ q23))) ◇ q24) ◇ q24))) (apc23 q23 q24))))).symm).trans (apc6 (((q24 ◇ ((q23 ◇ q24) ◇ (q24 ◇ q23))) ◇ q24) ◇ q24) q25 ((q24 ◇ ((q23 ◇ q24) ◇ (q24 ◇ q23))) ◇ q24) q26))
  have apc36:=fun (q27 q28 q29 q30:G)=>by
    exact (((cg (fun t => ((q28 ◇ ((q27 ◇ q28) ◇ (q28 ◇ q27))) ◇ q28) ◇ t) (cg (fun t => t ◇ ((q28 ◇ ((q27 ◇ q28) ◇ (q28 ◇ q27))) ◇ q28)) (cg (fun t => ((q30 ◇ ((q29 ◇ q30) ◇ (q30 ◇ q29))) ◇ q30) ◇ t) (apc3 q28 q27 ((q28 ◇ ((q27 ◇ q28) ◇ (q28 ◇ q27))) ◇ q28) q28)))).trans (apc24 q27 q28 (((q30 ◇ ((q29 ◇ q30) ◇ (q30 ◇ q29))) ◇ q30) ◇ ((q28 ◇ ((q27 ◇ q28) ◇ (q28 ◇ q27))) ◇ q28)))).symm).trans (((cg (fun t => ((q28 ◇ ((q27 ◇ q28) ◇ (q28 ◇ q27))) ◇ q28) ◇ t) (cg (fun t => t ◇ ((q28 ◇ ((q27 ◇ q28) ◇ (q28 ◇ q27))) ◇ q28)) (cg (fun t => ((q30 ◇ ((q29 ◇ q30) ◇ (q30 ◇ q29))) ◇ q30) ◇ t) (cg (fun t => t ◇ (((q28 ◇ ((q27 ◇ q28) ◇ (q28 ◇ q27))) ◇ q28) ◇ (((q28 ◇ ((q27 ◇ q28) ◇ (q28 ◇ q27))) ◇ q28) ◇ q28))) (apc23 q27 q28))))).symm).trans (apc31 q29 q30 (((q28 ◇ ((q27 ◇ q28) ◇ (q28 ◇ q27))) ◇ q28) ◇ q28) ((q28 ◇ ((q27 ◇ q28) ◇ (q28 ◇ q27))) ◇ q28)))
  have apc37:=fun (q31 q32 q33 q34:G)=>by
    exact (((((cg (fun t => ((q34 ◇ ((q33 ◇ q34) ◇ (q34 ◇ q33))) ◇ q34) ◇ t) (cg (fun t => t ◇ (((q34 ◇ ((q33 ◇ q34) ◇ (q34 ◇ q33))) ◇ q34) ◇ ((q32 ◇ ((q31 ◇ q32) ◇ (q32 ◇ q31))) ◇ q32))) (apc36 q33 q34 q31 q32))).trans (cg (fun t => ((q34 ◇ ((q33 ◇ q34) ◇ (q34 ◇ q33))) ◇ q34) ◇ t) (cg (fun t => ((q32 ◇ ((q31 ◇ q32) ◇ (q32 ◇ q31))) ◇ q32) ◇ t) (apc36 q31 q32 q33 q34)))).trans (cg (fun t => ((q34 ◇ ((q33 ◇ q34) ◇ (q34 ◇ q33))) ◇ q34) ◇ t) (apc36 q33 q34 q31 q32))).trans (apc36 q31 q32 q33 q34)).symm).trans (((cg (fun t => t ◇ ((((q32 ◇ ((q31 ◇ q32) ◇ (q32 ◇ q31))) ◇ q32) ◇ ((q34 ◇ ((q33 ◇ q34) ◇ (q34 ◇ q33))) ◇ q34)) ◇ (((q34 ◇ ((q33 ◇ q34) ◇ (q34 ◇ q33))) ◇ q34) ◇ ((q32 ◇ ((q31 ◇ q32) ◇ (q32 ◇ q31))) ◇ q32)))) (apc36 q31 q32 q33 q34)).symm).trans (apc0 ((q34 ◇ ((q33 ◇ q34) ◇ (q34 ◇ q33))) ◇ q34) ((q32 ◇ ((q31 ◇ q32) ◇ (q32 ◇ q31))) ◇ q32)))
  have apc55:=fun (q35 q36 q37 q38:G)=>by
    exact ((cg (fun t => q38 ◇ t) (cg (fun t => q37 ◇ t) (cg (fun t => ((q36 ◇ ((q35 ◇ q36) ◇ (q36 ◇ q35))) ◇ q36) ◇ t) (apc25 q35 q38)))).symm).trans (((cg (fun t => q38 ◇ t) (cg (fun t => q37 ◇ t) (cg (fun t => t ◇ (q38 ◇ (q38 ◇ ((q35 ◇ q38) ◇ (q38 ◇ q35))))) (apc37 q35 q36 q35 q38)))).symm).trans ((h q37 q38 (q38 ◇ ((q35 ◇ q38) ◇ (q38 ◇ q35)))).symm))
  have apc66:=fun (q39 q40 q41 q42:G)=>by
    exact ((cg (fun t => t ◇ (q42 ◇ q41)) (cg (fun t => q41 ◇ t) (apc36 q39 q39 q39 q40))).symm).trans (((cg (fun t => (q41 ◇ (((q40 ◇ ((q39 ◇ q40) ◇ (q40 ◇ q39))) ◇ q40) ◇ ((q39 ◇ ((q39 ◇ q39) ◇ (q39 ◇ q39))) ◇ q39))) ◇ t) (cg (fun t => q42 ◇ t) (apc55 q39 q40 q41 ((q39 ◇ ((q39 ◇ q39) ◇ (q39 ◇ q39))) ◇ q39)))).symm).trans (apc55 q39 q39 q42 (q41 ◇ (((q40 ◇ ((q39 ◇ q40) ◇ (q40 ◇ q39))) ◇ q40) ◇ ((q39 ◇ ((q39 ◇ q39) ◇ (q39 ◇ q39))) ◇ q39)))))
  have apc67:=fun (q43 q44 q45 q46:G)=>by
    exact (((cg (fun t => q45 ◇ t) (apc66 q43 q44 (q45 ◇ q46) (q46 ◇ q45))).symm).trans ((h ((q45 ◇ q46) ◇ ((q44 ◇ ((q43 ◇ q44) ◇ (q44 ◇ q43))) ◇ q44)) q45 q46).symm)).symm
  have apc68:=fun (q47 q48 q49:G)=>by
    exact ((cg (fun t => t ◇ (q49 ◇ (q47 ◇ q48))) (apc67 q47 q47 q47 q48)).symm).trans (apc66 q47 q47 (q47 ◇ q48) q49)
  have apc69:=fun (q50 q51 q52:G)=>by
    exact ((cg (fun t => (q52 ◇ ((q50 ◇ q51) ◇ q52)) ◇ t) (apc68 q50 q51 q52)).symm).trans (apc68 q52 (q50 ◇ q51) (q50 ◇ (q51 ◇ q50)))
  have apc73:=fun (q53 q54 q55 q56:G)=>by
    exact (((cg (fun t => (q55 ◇ (q56 ◇ q55)) ◇ t) (apc69 q53 q54 (q55 ◇ q56))).symm).trans (apc68 q55 q56 ((q55 ◇ q56) ◇ ((q53 ◇ q54) ◇ (q55 ◇ q56))))).symm
  have apc76:=fun (q57 q58 q59 q60:G)=>by
    exact (((cg (fun t => (q59 ◇ (q60 ◇ q59)) ◇ t) (apc66 q57 q58 q60 q59)).symm).trans (apc68 q59 q60 (q60 ◇ ((q58 ◇ ((q57 ◇ q58) ◇ (q58 ◇ q57))) ◇ q58)))).symm
  have apc77:=fun (q57 q58 q59 q60:G)=>by
    exact ((apc76 q57 q57 q59 q60).symm).trans (apc76 q57 q57 q57 q60)
  have apc101:=fun (q61 q62 q63 q64:G)=>by
    exact (((cg (fun t => t ◇ q64) (cg (fun t => q64 ◇ t) (cg (fun t => t ◇ q64) ((h q61 q63 q62).symm)))).symm).trans (apc69 q63 (q61 ◇ ((q62 ◇ q63) ◇ (q63 ◇ q62))) q64)).symm
  have apc102:=fun (q65 q66 q67 q68:G)=>by
    exact ((((cg (fun t => t ◇ q68) (apc101 q65 q66 q68 q67)).symm).trans (apc77 q65 q65 q68 (q65 ◇ ((q66 ◇ q68) ◇ (q68 ◇ q66))))).trans (apc69 q65 ((q66 ◇ q68) ◇ (q68 ◇ q66)) q65)).symm
  have apc103:=fun (q69 q70 q71:G)=>by
    exact (((cg (fun t => t ◇ q71) (apc102 q71 q69 q69 q70)).symm).trans (apc77 q69 q69 q71 ((q69 ◇ q70) ◇ (q70 ◇ q69)))).trans (((apc69 (q69 ◇ q70) (q70 ◇ q69) q69).trans (apc73 q70 q69 q69 q70)).trans (apc68 q69 q70 q70))
  have apc104:=fun (q65 q66 q67 q68:G)=>by
    exact ((apc102 q65 q65 q67 q68).symm).trans (apc102 q65 q65 q65 q68)
  have apc109:=fun (q72 q73:G)=>by
    exact (((cg (fun t => q72 ◇ t) (apc103 q73 (q73 ◇ (q73 ◇ (q72 ◇ q73))) q72)).symm).trans (apc102 q72 (q73 ◇ (q72 ◇ q73)) q72 q73)).trans (apc104 q72 (((q72 ◇ (q72 ◇ q72)) ◇ q72) ◇ q73) q72 q73)
  exact (calc
    x=x:=rfl
    _=((y ◇ (x ◇ (x ◇ (y ◇ x)))) ◇ y):=((cg (fun t => t ◇ y) (apc109 y x)).trans (apc103 y x y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_6749_to_29465 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_6749_to_29465
