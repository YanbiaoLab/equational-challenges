-- Equation450 → Equation5574
-- Recorded verdict: true
-- Premise: x = x ◇ (y ◇ (z ◇ (y ◇ x)))
-- Conclusion: x = x ◇ (x ◇ (x ◇ ((x ◇ y) ◇ x)))
-- Original submission SHA-256: 0ee66b955d332f62620492810335d793c9a7de6fb873a6d611f5eba401534abe
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = x ◇ (y ◇ (z ◇ (y ◇ x)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = x ◇ (x ◇ (x ◇ ((x ◇ y) ◇ x)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1:G), ((q1 ◇ q0) ◇ q0) = (q1 ◇ q0):=by
    intro q0 q1
    exact ((cg (fun t => (q1 ◇ q0) ◇ t) ((h q0 q1 q0).symm)).symm).trans ((h (q1 ◇ q0) q0 q1).symm)
  have apc3 : forall (q2 q3 q4:G), (q3 ◇ ((q2 ◇ q3) ◇ (q4 ◇ (q2 ◇ q3)))) = q3:=by
    intro q2 q3 q4
    exact ((cg (fun t => q3 ◇ t) (cg (fun t => (q2 ◇ q3) ◇ t) (cg (fun t => q4 ◇ t) (apc0 q3 q2)))).symm).trans ((h q3 (q2 ◇ q3) q4).symm)
  have apc4 : forall (q5 q6 q0 q1:G), ((q5 ◇ (q6 ◇ (q5 ◇ q0))) ◇ (q0 ◇ (q1 ◇ q0))) = (q5 ◇ (q6 ◇ (q5 ◇ q0))):=by
    intro q5 q6 q0 q1
    exact ((cg (fun t => (q5 ◇ (q6 ◇ (q5 ◇ q0))) ◇ t) (cg (fun t => q0 ◇ t) (cg (fun t => q1 ◇ t) ((h q0 q5 q6).symm)))).symm).trans ((h (q5 ◇ (q6 ◇ (q5 ◇ q0))) q0 q1).symm)
  have apc5 : forall (q7 q8:G), (q7 ◇ (q8 ◇ (q7 ◇ (q8 ◇ q7)))) = q7:=by
    intro q7 q8
    exact (((apc3 q8 q7 q7).symm).trans (((cg (fun t => t ◇ ((q8 ◇ q7) ◇ (q7 ◇ (q8 ◇ q7)))) ((h q7 q8 q7).symm)).symm).trans (apc4 q7 q8 (q8 ◇ q7) q7))).symm
  have apc6 : forall (q9 q7 q8:G), (q7 ◇ (q8 ◇ (q7 ◇ (q9 ◇ (q7 ◇ q8))))) = (q7 ◇ q8):=by
    intro q9 q7 q8
    exact (((apc3 q9 (q7 ◇ q8) q9).symm).trans (((cg (fun t => t ◇ ((q9 ◇ (q7 ◇ q8)) ◇ (q9 ◇ (q9 ◇ (q7 ◇ q8))))) (cg (fun t => q7 ◇ t) ((h q8 q7 q9).symm))).symm).trans (apc4 q7 q8 (q9 ◇ (q7 ◇ q8)) q9))).symm
  have apc7 : forall (q10 q11 q12 q13:G), ((q12 ◇ q13) ◇ (q13 ◇ (q10 ◇ (q11 ◇ (q10 ◇ q13))))) = (q12 ◇ q13):=by
    intro q10 q11 q12 q13
    exact ((cg (fun t => (q12 ◇ q13) ◇ t) (cg (fun t => q13 ◇ t) (apc4 q10 q11 q13 q12))).symm).trans ((h (q12 ◇ q13) q13 (q10 ◇ (q11 ◇ (q10 ◇ q13)))).symm)
  have apc10 : forall (q14 q15 q16 q17:G), (((q14 ◇ q16) ◇ (q15 ◇ (q14 ◇ q16))) ◇ (q16 ◇ (q17 ◇ q16))) = ((q14 ◇ q16) ◇ (q15 ◇ (q14 ◇ q16))):=by
    intro q14 q15 q16 q17
    exact ((cg (fun t => ((q14 ◇ q16) ◇ (q15 ◇ (q14 ◇ q16))) ◇ t) (cg (fun t => q16 ◇ t) (cg (fun t => q17 ◇ t) (apc3 q14 q16 q15)))).symm).trans ((h ((q14 ◇ q16) ◇ (q15 ◇ (q14 ◇ q16))) q16 q17).symm)
  have apc15 : forall (q18 q19 q20 q21:G), ((q19 ◇ (q20 ◇ (q18 ◇ (q20 ◇ q19)))) ◇ (q20 ◇ (q21 ◇ (q20 ◇ q19)))) = (q19 ◇ (q20 ◇ (q18 ◇ (q20 ◇ q19)))):=by
    intro q18 q19 q20 q21
    exact ((cg (fun t => (q19 ◇ (q20 ◇ (q18 ◇ (q20 ◇ q19)))) ◇ t) (cg (fun t => q20 ◇ t) (cg (fun t => q21 ◇ t) (apc6 q18 q20 q19)))).symm).trans ((h (q19 ◇ (q20 ◇ (q18 ◇ (q20 ◇ q19)))) q20 q21).symm)
  have apc16 : forall (q22 q23 q24 q25:G), (q23 ◇ (q24 ◇ (q25 ◇ (q24 ◇ q23)))) = (q23 ◇ (q24 ◇ (q22 ◇ (q24 ◇ q23)))):=by
    intro q22 q23 q24 q25
    exact ((cg (fun t => t ◇ (q24 ◇ (q25 ◇ (q24 ◇ q23)))) ((h q23 q24 q22).symm)).symm).trans (apc15 q22 q23 q24 q25)
  have apc18 : forall (q26 q22 q24 q25:G), ((q26 ◇ (q24 ◇ q22)) ◇ (q24 ◇ (q25 ◇ (q24 ◇ (q26 ◇ (q24 ◇ q22)))))) = (q26 ◇ (q24 ◇ q22)):=by
    intro q26 q22 q24 q25
    exact ((cg (fun t => t ◇ (q24 ◇ (q25 ◇ (q24 ◇ (q26 ◇ (q24 ◇ q22)))))) (apc0 (q24 ◇ q22) q26)).symm).trans ((((cg (fun t => t ◇ (q24 ◇ (q25 ◇ (q24 ◇ (q26 ◇ (q24 ◇ q22)))))) (cg (fun t => (q26 ◇ (q24 ◇ q22)) ◇ t) (cg (fun t => q24 ◇ t) ((h q22 q24 q26).symm)))).symm).trans (apc15 q22 (q26 ◇ (q24 ◇ q22)) q24 q25)).trans ((cg (fun t => (q26 ◇ (q24 ◇ q22)) ◇ t) (apc6 q26 q24 q22)).trans (apc0 (q24 ◇ q22) q26)))
  have apc31 : forall (q27 q28 q29 q30:G), (q30 ◇ ((q27 ◇ (q30 ◇ (q27 ◇ q30))) ◇ (q28 ◇ (q29 ◇ (q28 ◇ (q27 ◇ (q30 ◇ (q27 ◇ q30)))))))) = q30:=by
    intro q27 q28 q29 q30
    exact (((cg (fun t => t ◇ ((q27 ◇ (q30 ◇ (q27 ◇ q30))) ◇ (q28 ◇ (q29 ◇ (q28 ◇ (q27 ◇ (q30 ◇ (q27 ◇ q30)))))))) (apc5 q30 q27)).symm).trans (apc7 q28 q29 q30 (q27 ◇ (q30 ◇ (q27 ◇ q30))))).trans (apc5 q30 q27)
  have apc38 : forall (q31 q32 q33 q34 q35:G), (q35 ◇ ((q31 ◇ (q32 ◇ (q31 ◇ q35))) ◇ (q33 ◇ (q34 ◇ (q33 ◇ (q31 ◇ (q32 ◇ (q31 ◇ q35)))))))) = q35:=by
    intro q31 q32 q33 q34 q35
    exact ((cg (fun t => q35 ◇ t) (cg (fun t => (q31 ◇ (q32 ◇ (q31 ◇ q35))) ◇ t) (cg (fun t => q33 ◇ t) (cg (fun t => q34 ◇ t) (cg (fun t => q33 ◇ t) (apc4 q31 q32 q35 (q31 ◇ (q32 ◇ (q31 ◇ q35))))))))).symm).trans (((cg (fun t => q35 ◇ t) (cg (fun t => t ◇ (q33 ◇ (q34 ◇ (q33 ◇ ((q31 ◇ (q32 ◇ (q31 ◇ q35))) ◇ (q35 ◇ ((q31 ◇ (q32 ◇ (q31 ◇ q35))) ◇ q35))))))) (apc4 q31 q32 q35 (q31 ◇ (q32 ◇ (q31 ◇ q35)))))).symm).trans (apc31 (q31 ◇ (q32 ◇ (q31 ◇ q35))) q33 q34 q35))
  have apc39 : forall (q36 q37 q38:G), ((q38 ◇ q36) ◇ (q37 ◇ (q38 ◇ (q37 ◇ (q38 ◇ q36))))) = (q38 ◇ q36):=by
    intro q36 q37 q38
    exact ((cg (fun t => (q38 ◇ q36) ◇ t) (apc0 (q38 ◇ (q37 ◇ (q38 ◇ q36))) q37)).symm).trans (((cg (fun t => (q38 ◇ q36) ◇ t) (cg (fun t => (q37 ◇ (q38 ◇ (q37 ◇ (q38 ◇ q36)))) ◇ t) (cg (fun t => q38 ◇ t) (apc18 q37 q36 q38 q37)))).symm).trans (apc38 q37 q38 q38 (q37 ◇ (q38 ◇ q36)) (q38 ◇ q36)))
  have apc40 : forall (q39 q40 q41 q42:G), ((q42 ◇ q39) ◇ (q41 ◇ (q40 ◇ (q41 ◇ (q42 ◇ q39))))) = (q42 ◇ q39):=by
    intro q39 q40 q41 q42
    exact (((apc39 q39 q41 q42).symm).trans (apc16 q40 (q42 ◇ q39) q41 q42)).symm
  have apc79 : forall (q43 q44 q45 q46 q47 q48:G), ((q47 ◇ (q48 ◇ (q47 ◇ (q45 ◇ (q46 ◇ q45))))) ◇ ((q45 ◇ (q46 ◇ q45)) ◇ (q43 ◇ (q44 ◇ (q43 ◇ q45))))) = (q47 ◇ (q48 ◇ (q47 ◇ (q45 ◇ (q46 ◇ q45))))):=by
    intro q43 q44 q45 q46 q47 q48
    exact ((cg (fun t => (q47 ◇ (q48 ◇ (q47 ◇ (q45 ◇ (q46 ◇ q45))))) ◇ t) (cg (fun t => (q45 ◇ (q46 ◇ q45)) ◇ t) (apc4 q43 q44 q45 q46))).symm).trans (apc4 q47 q48 (q45 ◇ (q46 ◇ q45)) (q43 ◇ (q44 ◇ (q43 ◇ q45))))
  have apc150 : forall (q49 q50 q51 q52 q53 q54:G), ((q53 ◇ (q54 ◇ (q53 ◇ (q51 ◇ (q52 ◇ q51))))) ◇ ((q51 ◇ (q52 ◇ q51)) ◇ ((q49 ◇ q51) ◇ (q50 ◇ (q49 ◇ q51))))) = (q53 ◇ (q54 ◇ (q53 ◇ (q51 ◇ (q52 ◇ q51))))):=by
    intro q49 q50 q51 q52 q53 q54
    exact ((cg (fun t => (q53 ◇ (q54 ◇ (q53 ◇ (q51 ◇ (q52 ◇ q51))))) ◇ t) (cg (fun t => (q51 ◇ (q52 ◇ q51)) ◇ t) (apc10 q49 q50 q51 q52))).symm).trans (apc4 q53 q54 (q51 ◇ (q52 ◇ q51)) ((q49 ◇ q51) ◇ (q50 ◇ (q49 ◇ q51))))
  have apc197 : forall (q55 q56 q57 q58 q59:G), ((q55 ◇ ((q58 ◇ (q59 ◇ (q58 ◇ (q56 ◇ (q57 ◇ q56))))) ◇ q56)) ◇ (q58 ◇ (q59 ◇ (q58 ◇ (q56 ◇ (q57 ◇ q56)))))) = (q55 ◇ ((q58 ◇ (q59 ◇ (q58 ◇ (q56 ◇ (q57 ◇ q56))))) ◇ q56)):=by
    intro q55 q56 q57 q58 q59
    exact ((cg (fun t => (q55 ◇ ((q58 ◇ (q59 ◇ (q58 ◇ (q56 ◇ (q57 ◇ q56))))) ◇ q56)) ◇ t) (apc79 (q58 ◇ (q59 ◇ (q58 ◇ (q56 ◇ (q57 ◇ q56))))) q55 q56 q57 q58 q59)).symm).trans ((h (q55 ◇ ((q58 ◇ (q59 ◇ (q58 ◇ (q56 ◇ (q57 ◇ q56))))) ◇ q56)) (q58 ◇ (q59 ◇ (q58 ◇ (q56 ◇ (q57 ◇ q56))))) (q56 ◇ (q57 ◇ q56))).symm)
  have apc198 : forall (q60 q61 q62 q63 q64:G), ((q63 ◇ (q64 ◇ (q61 ◇ (q62 ◇ q61)))) ◇ (q64 ◇ (q60 ◇ ((q64 ◇ (q63 ◇ (q64 ◇ (q61 ◇ (q62 ◇ q61))))) ◇ q61)))) = (q63 ◇ (q64 ◇ (q61 ◇ (q62 ◇ q61)))):=by
    intro q60 q61 q62 q63 q64
    exact ((cg (fun t => (q63 ◇ (q64 ◇ (q61 ◇ (q62 ◇ q61)))) ◇ t) (cg (fun t => q64 ◇ t) (apc197 q60 q61 q62 q64 q63))).symm).trans ((h (q63 ◇ (q64 ◇ (q61 ◇ (q62 ◇ q61)))) q64 (q60 ◇ ((q64 ◇ (q63 ◇ (q64 ◇ (q61 ◇ (q62 ◇ q61))))) ◇ q61))).symm)
  have apc201 : forall (q65 q66 q67 q68:G), (((q68 ◇ (q67 ◇ (q68 ◇ (q65 ◇ (q66 ◇ q65))))) ◇ q65) ◇ (q67 ◇ (q68 ◇ (q65 ◇ (q66 ◇ q65))))) = ((q68 ◇ (q67 ◇ (q68 ◇ (q65 ◇ (q66 ◇ q65))))) ◇ q65):=by
    intro q65 q66 q67 q68
    exact ((cg (fun t => ((q68 ◇ (q67 ◇ (q68 ◇ (q65 ◇ (q66 ◇ q65))))) ◇ q65) ◇ t) (apc198 (q67 ◇ (q68 ◇ (q65 ◇ (q66 ◇ q65)))) q65 q66 q67 q68)).symm).trans ((h ((q68 ◇ (q67 ◇ (q68 ◇ (q65 ◇ (q66 ◇ q65))))) ◇ q65) (q67 ◇ (q68 ◇ (q65 ◇ (q66 ◇ q65)))) q68).symm)
  have apc202 : forall (q69 q70 q71 q72 q73:G), (((q70 ◇ (q71 ◇ q70)) ◇ (q69 ◇ q70)) ◇ (q72 ◇ (q73 ◇ (q72 ◇ (q70 ◇ (q71 ◇ q70)))))) = ((q70 ◇ (q71 ◇ q70)) ◇ (q69 ◇ q70)):=by
    intro q69 q70 q71 q72 q73
    exact (((cg (fun t => t ◇ ((q72 ◇ (q73 ◇ (q72 ◇ (q70 ◇ (q71 ◇ q70))))) ◇ ((q70 ◇ (q71 ◇ q70)) ◇ ((q69 ◇ q70) ◇ (q69 ◇ (q69 ◇ q70)))))) (cg (fun t => t ◇ (q69 ◇ q70)) (apc40 (q71 ◇ q70) q73 q72 q70))).trans (cg (fun t => ((q70 ◇ (q71 ◇ q70)) ◇ (q69 ◇ q70)) ◇ t) (apc150 q69 q69 q70 q71 q72 q73))).symm).trans ((((cg (fun t => t ◇ ((q72 ◇ (q73 ◇ (q72 ◇ (q70 ◇ (q71 ◇ q70))))) ◇ ((q70 ◇ (q71 ◇ q70)) ◇ ((q69 ◇ q70) ◇ (q69 ◇ (q69 ◇ q70)))))) (cg (fun t => t ◇ (q69 ◇ q70)) (cg (fun t => (q70 ◇ (q71 ◇ q70)) ◇ t) (apc150 q69 q69 q70 q71 q72 q73)))).symm).trans (apc201 (q69 ◇ q70) q69 (q72 ◇ (q73 ◇ (q72 ◇ (q70 ◇ (q71 ◇ q70))))) (q70 ◇ (q71 ◇ q70)))).trans ((cg (fun t => t ◇ (q69 ◇ q70)) (cg (fun t => (q70 ◇ (q71 ◇ q70)) ◇ t) (apc150 q69 q69 q70 q71 q72 q73))).trans (cg (fun t => t ◇ (q69 ◇ q70)) (apc40 (q71 ◇ q70) q73 q72 q70))))
  have apc203 : forall (q74 q75 q76 q77:G), ((q77 ◇ (q75 ◇ (q76 ◇ q75))) ◇ ((q75 ◇ (q76 ◇ q75)) ◇ (q74 ◇ q75))) = (q77 ◇ (q75 ◇ (q76 ◇ q75))):=by
    intro q74 q75 q76 q77
    exact ((cg (fun t => (q77 ◇ (q75 ◇ (q76 ◇ q75))) ◇ t) (apc202 q74 q75 q76 q77 ((q75 ◇ (q76 ◇ q75)) ◇ (q74 ◇ q75)))).symm).trans ((h (q77 ◇ (q75 ◇ (q76 ◇ q75))) ((q75 ◇ (q76 ◇ q75)) ◇ (q74 ◇ q75)) q77).symm)
  have apc204 : forall (q78 q79 q80:G), (q80 ◇ (q79 ◇ (q80 ◇ (q78 ◇ q80)))) = q80:=by
    intro q78 q79 q80
    exact ((cg (fun t => q80 ◇ t) (apc203 (q79 ◇ (q80 ◇ (q78 ◇ q80))) q80 q78 q79)).symm).trans ((h q80 (q79 ◇ (q80 ◇ (q78 ◇ q80))) (q80 ◇ (q78 ◇ q80))).symm)
  exact (calc
    x = x:=rfl
    _ = (x ◇ (x ◇ (x ◇ ((x ◇ y) ◇ x)))):=(apc204 (x ◇ y) x x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_450_to_5574 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_450_to_5574
