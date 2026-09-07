-- Equation56101 → Equation54749
-- Recorded verdict: true
-- Premise: x ◇ (y ◇ z) = (x ◇ z) ◇ (x ◇ y)
-- Conclusion: x ◇ (x ◇ y) = x ◇ ((y ◇ y) ◇ x)
-- Original submission SHA-256: 90b370726bd0177735bf1338f5dd536f70c1a043fdff4ff1cc477afab35806bf
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ z) = (x ◇ z) ◇ (x ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ (x ◇ y) = x ◇ ((y ◇ y) ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   

def submission : Goal := by
  intro G _ h
  intro x y
  have cg : ∀ (f : G → G) {a b : G}, a=b → f a=f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1 q2 q3 : G), ((q0 ◇ (q1 ◇ q2)) ◇ ((q0 ◇ q2) ◇ q3))=((q0 ◇ q2) ◇ (q3 ◇ (q0 ◇ q1))):=by
    intro q0 q1 q2 q3
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ ((q0 ◇ q2) ◇ q3)) ((h q0 q1 q2).symm)).symm).trans ((h (q0 ◇ q2) q3 (q0 ◇ q1)).symm)).trans (rfl))
  have apc1 : forall (q0 q1 q2 q4 : G), (((q0 ◇ q2) ◇ q4) ◇ (q0 ◇ (q1 ◇ q2)))=((q0 ◇ q2) ◇ ((q0 ◇ q1) ◇ q4)):=by
    intro q0 q1 q2 q4
    exact ((rfl).symm).trans ((((cg (fun t => ((q0 ◇ q2) ◇ q4) ◇ t) ((h q0 q1 q2).symm)).symm).trans ((h (q0 ◇ q2) (q0 ◇ q1) q4).symm)).trans (rfl))
  have apc2 : forall (q5 q6 q7 q8 : G), ((q6 ◇ q8) ◇ ((q6 ◇ q5) ◇ (q6 ◇ q7)))=((q6 ◇ (q7 ◇ q8)) ◇ (q6 ◇ (q5 ◇ q8))):=by
    intro q5 q6 q7 q8
    exact (((rfl).symm).trans ((((cg (fun t => (q6 ◇ (q7 ◇ q8)) ◇ t) ((h q6 q5 q8).symm)).symm).trans (apc0 q6 q7 q8 (q6 ◇ q5))).trans (rfl))).symm
  have apc3 : forall (q9 q10 q11 q12 : G), ((q10 ◇ (q11 ◇ q12)) ◇ (q10 ◇ (q9 ◇ q12)))=((q10 ◇ q12) ◇ (q10 ◇ (q11 ◇ q9))):=by
    intro q9 q10 q11 q12
    exact (((rfl).symm).trans ((((cg (fun t => (q10 ◇ q12) ◇ t) ((h q10 q11 q9).symm)).symm).trans (apc2 q9 q10 q11 q12)).trans (rfl))).symm
  have apc4 : forall (q13 q14 q15 q16 : G), (q16 ◇ ((q13 ◇ q15) ◇ (q14 ◇ q15)))=((q16 ◇ q15) ◇ (q16 ◇ (q14 ◇ q13))):=by
    intro q13 q14 q15 q16
    exact (((rfl).symm).trans ((((apc3 q13 q16 q14 q15).symm).trans ((h q16 (q13 ◇ q15) (q14 ◇ q15)).symm)).trans (rfl))).symm
  have apc5 : forall (q17 q18 q19 : G), ((q19 ◇ q18) ◇ (q19 ◇ (q17 ◇ q17)))=(q19 ◇ (q17 ◇ (q18 ◇ q18))):=by
    intro q17 q18 q19
    exact (((rfl).symm).trans ((((cg (fun t => q19 ◇ t) ((h q17 q18 q18).symm)).symm).trans (apc4 q17 q17 q18 q19)).trans (rfl))).symm
  have apc6 : forall (q20 q21 q22 : G), (q21 ◇ (q20 ◇ (q22 ◇ q22)))=(q21 ◇ ((q20 ◇ q20) ◇ q22)):=by
    intro q20 q21 q22
    exact ((rfl).symm).trans ((((apc5 q20 q22 q21).symm).trans ((h q21 (q20 ◇ q20) q22).symm)).trans (rfl))
  have apc8 : forall (q17 q18 q19 q20 q21 q22 : G), ((q19 ◇ q18) ◇ ((q19 ◇ q19) ◇ q17))=(q19 ◇ ((q17 ◇ q17) ◇ q18)):=by
    intro q17 q18 q19 q20 q21 q22
    exact ((rfl).symm).trans ((((apc6 q19 (q19 ◇ q18) q17).symm).trans ((apc5 q17 q18 q19).trans (apc6 q17 q19 q18))).trans (rfl))
  have apc9 : forall (q5 q6 q7 q8 q9 q10 q11 q12 : G), ((q6 ◇ q8) ◇ ((q6 ◇ q5) ◇ (q6 ◇ q7)))=((q6 ◇ q8) ◇ (q6 ◇ (q7 ◇ q5))):=by
    intro q5 q6 q7 q8 q9 q10 q11 q12
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc2 q5 q6 q7 q8).trans (apc3 q5 q6 q7 q8))).trans (rfl))
  have apc12 : forall (q23 q24 q25 q26 : G), (q26 ◇ (q25 ◇ ((q23 ◇ q23) ◇ q24)))=(q26 ◇ ((q25 ◇ q25) ◇ (q23 ◇ q24))):=by
    intro q23 q24 q25 q26
    exact ((cg (fun t => q26 ◇ t) (apc6 q23 q25 q24)).symm).trans ((((cg (fun t => q26 ◇ t) (cg (fun t => q25 ◇ t) ((h q23 q24 q24).symm))).symm).trans (apc6 q25 q26 (q23 ◇ q24))).trans (rfl))
  have apc13 : forall (q27 q28 q29 : G), (q28 ◇ ((q29 ◇ q29) ◇ (q27 ◇ q28)))=((q28 ◇ q28) ◇ (q29 ◇ (q28 ◇ q27))):=by
    intro q27 q28 q29
    exact ((rfl).symm).trans ((((apc8 q29 (q27 ◇ q28) q28 q27 q27 q27).symm).trans (apc0 q28 q27 q28 q29)).trans (rfl))
  have apc16 : forall (q30 q31 q32 q33 : G), ((q33 ◇ q32) ◇ ((q33 ◇ q33) ◇ (q30 ◇ q31)))=(q33 ◇ ((q30 ◇ q31) ◇ (q32 ◇ q32))):=by
    intro q30 q31 q32 q33
    exact (((cg (fun t => (q33 ◇ q32) ◇ t) (apc6 q30 q33 q31)).trans (apc12 q30 q31 q33 (q33 ◇ q32))).symm).trans ((((cg (fun t => (q33 ◇ q32) ◇ t) (cg (fun t => q33 ◇ t) ((h q30 q31 q31).symm))).symm).trans (apc5 (q30 ◇ q31) q32 q33)).trans (rfl))
  have apc23 : forall (q34 q35 q36 : G), (((q34 ◇ q35) ◇ q36) ◇ ((q34 ◇ q34) ◇ q35))=((q34 ◇ q35) ◇ ((q34 ◇ q35) ◇ q36)):=by
    intro q34 q35 q36
    exact ((rfl).symm).trans ((((apc6 q34 ((q34 ◇ q35) ◇ q36) q35).symm).trans (apc1 q34 q35 q35 q36)).trans (rfl))
  have apc24 : forall (q37 q38 : G), (q37 ◇ ((q38 ◇ q38) ◇ q37))=((q37 ◇ q37) ◇ (q37 ◇ q38)):=by
    intro q37 q38
    exact ((apc8 q38 q37 q37 ((q37 ◇ q37) ◇ ((q37 ◇ q37) ◇ q38)) ((q37 ◇ q37) ◇ ((q37 ◇ q37) ◇ q38)) ((q37 ◇ q37) ◇ ((q37 ◇ q37) ◇ q38))).symm).trans ((((apc23 q37 q37 q38).symm).trans ((h (q37 ◇ q37) q37 q38).symm)).trans (rfl))
  have apc26 : forall (q39 q40 q41 : G), (q41 ◇ ((q40 ◇ q40) ◇ (q40 ◇ q39)))=((q41 ◇ q40) ◇ (q41 ◇ (q39 ◇ q40))):=by
    intro q39 q40 q41
    exact ((rfl).symm).trans ((((cg (fun t => q41 ◇ t) (apc24 q40 q39)).symm).trans (apc12 q39 q40 q40 q41)).trans (apc4 q40 q39 q40 q41))
  have apc27 : forall (q42 q43 q44 : G), ((q44 ◇ q43) ◇ (q44 ◇ (q42 ◇ q43)))=(q44 ◇ (q43 ◇ (q42 ◇ q43))):=by
    intro q42 q43 q44
    exact (((rfl).symm).trans ((((cg (fun t => q44 ◇ t) ((h q43 q42 q43).symm)).symm).trans (apc26 q42 q43 q44)).trans (rfl))).symm
  have apc29 : forall (q45 q46 q47 : G), (q46 ◇ ((q45 ◇ q47) ◇ q47))=(q46 ◇ (q47 ◇ (q45 ◇ q47))):=by
    intro q45 q46 q47
    exact (((rfl).symm).trans ((((apc27 q45 q47 q46).symm).trans ((h q46 (q45 ◇ q47) q47).symm)).trans (rfl))).symm
  have apc33 : forall (q42 q43 q44 q39 q40 q41 : G), (q41 ◇ ((q40 ◇ q40) ◇ (q40 ◇ q39)))=(q41 ◇ (q40 ◇ (q39 ◇ q40))):=by
    intro q42 q43 q44 q39 q40 q41
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc26 q39 q40 q41).trans (apc27 q39 q40 q41))).trans (rfl))
  have apc36 : forall (q48 q49 q50 : G), (q50 ◇ ((q48 ◇ (q49 ◇ q49)) ◇ q50))=((q50 ◇ q50) ◇ (q50 ◇ (q48 ◇ q49))):=by
    intro q48 q49 q50
    exact ((rfl).symm).trans ((((cg (fun t => q50 ◇ t) (cg (fun t => t ◇ q50) ((h q48 q49 q49).symm))).symm).trans (apc24 q50 (q48 ◇ q49))).trans (rfl))
  have apc37 : forall (q51 q52 q53 q54 : G), ((q53 ◇ ((q51 ◇ q51) ◇ q52)) ◇ (q53 ◇ q54))=(q53 ◇ ((q54 ◇ q54) ◇ (q51 ◇ q52))):=by
    intro q51 q52 q53 q54
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (q53 ◇ q54)) (apc6 q51 q53 q52)).symm).trans ((h q53 q54 (q51 ◇ (q52 ◇ q52))).symm)).trans ((cg (fun t => q53 ◇ t) (apc6 q51 q54 q52)).trans (apc12 q51 q52 q54 q53)))
  have apc38 : forall (q51 q52 q53 q55 : G), (q53 ◇ ((q51 ◇ (q52 ◇ q52)) ◇ q55))=(q53 ◇ ((q51 ◇ q52) ◇ (q55 ◇ q55))):=by
    intro q51 q52 q53 q55
    exact ((((apc12 q51 q52 q53 (q53 ◇ q55)).trans (apc16 q51 q52 q55 q53)).symm).trans ((((cg (fun t => (q53 ◇ q55) ◇ t) (apc6 q51 q53 q52)).symm).trans ((h q53 (q51 ◇ (q52 ◇ q52)) q55).symm)).trans (rfl))).symm
  have apc44 : forall (q48 q49 q50 q51 q52 q53 q55 : G), ((q50 ◇ q50) ◇ (q50 ◇ (q48 ◇ q49)))=(q50 ◇ ((q48 ◇ q49) ◇ (q50 ◇ q50))):=by
    intro q48 q49 q50 q51 q52 q53 q55
    exact (((rfl).symm).trans ((((apc38 q48 q49 q50 q50).symm).trans ((apc36 q48 q49 q50).trans (rfl))).trans (rfl))).symm
  have apc51 : forall (q56 q57 q58 q59 : G), (q58 ◇ (((q56 ◇ q56) ◇ q57) ◇ q59))=(q58 ◇ ((q56 ◇ q57) ◇ (q59 ◇ q59))):=by
    intro q56 q57 q58 q59
    exact (((apc16 q56 q57 q59 q58).symm).trans ((((apc12 q56 q57 q58 (q58 ◇ q59)).symm).trans ((h q58 ((q56 ◇ q56) ◇ q57) q59).symm)).trans (rfl))).symm
  have apc59 : forall (q60 q61 : G), ((q60 ◇ q60) ◇ ((q61 ◇ q61) ◇ q60))=((q60 ◇ q60) ◇ (q60 ◇ q61)):=by
    intro q60 q61
    exact (((apc13 q60 q60 q61).trans (apc6 q61 (q60 ◇ q60) q60)).symm).trans ((((apc44 q61 q61 q60 q60 q60 q60 q60).symm).trans (apc6 q60 (q60 ◇ q60) q61)).trans ((apc8 q61 q60 q60 ((q60 ◇ q60) ◇ ((q60 ◇ q60) ◇ q61)) ((q60 ◇ q60) ◇ ((q60 ◇ q60) ◇ q61)) ((q60 ◇ q60) ◇ ((q60 ◇ q60) ◇ q61))).trans (apc24 q60 q61)))
  have apc60 : forall (q62 q63 q64 : G), (((q63 ◇ q63) ◇ (q63 ◇ q62)) ◇ (q63 ◇ q64))=((q63 ◇ q63) ◇ (q64 ◇ (q63 ◇ q62))):=by
    intro q62 q63 q64
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (q63 ◇ q64)) (apc24 q63 q62)).symm).trans (apc37 q62 q63 q63 q64)).trans (apc13 q62 q63 q64))
  have apc61 : forall (q65 q66 q67 : G), ((q66 ◇ (q65 ◇ q66)) ◇ (q66 ◇ q67))=((q66 ◇ q66) ◇ (q67 ◇ (q66 ◇ q65))):=by
    intro q65 q66 q67
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (q66 ◇ q67)) ((h q66 q65 q66).symm)).symm).trans (apc60 q65 q66 q67)).trans (rfl))
  have apc62 : forall (q68 q69 q70 : G), ((q69 ◇ q69) ◇ (q70 ◇ (q69 ◇ q68)))=(q69 ◇ (q70 ◇ (q68 ◇ q69))):=by
    intro q68 q69 q70
    exact ((rfl).symm).trans ((((apc61 q68 q69 q70).symm).trans ((h q69 q70 (q68 ◇ q69)).symm)).trans (rfl))
  have apc79 : forall (q71 q72 q73 q74 q75 : G), (((q74 ◇ q73) ◇ (q74 ◇ (q72 ◇ q71))) ◇ (q74 ◇ q75))=(q74 ◇ ((q75 ◇ q73) ◇ (q75 ◇ (q72 ◇ q71)))):=by
    intro q71 q72 q73 q74 q75
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (q74 ◇ q75)) (apc4 q71 q72 q73 q74)).symm).trans ((h q74 q75 ((q71 ◇ q73) ◇ (q72 ◇ q73))).symm)).trans (cg (fun t => q74 ◇ t) (apc4 q71 q72 q73 q75)))
  have apc80 : forall (q76 q77 q78 q79 q80 : G), (q79 ◇ ((q80 ◇ q78) ◇ (q80 ◇ (q77 ◇ q76))))=((q79 ◇ ((q77 ◇ q76) ◇ q78)) ◇ (q79 ◇ q80)):=by
    intro q76 q77 q78 q79 q80
    exact (((rfl).symm).trans ((((cg (fun t => t ◇ (q79 ◇ q80)) ((h q79 (q77 ◇ q76) q78).symm)).symm).trans (apc79 q76 q77 q78 q79 q80)).trans (rfl))).symm
  have apc82 : forall (q81 q82 q83 q84 q85 : G), ((q84 ◇ ((q82 ◇ q81) ◇ q83)) ◇ (q84 ◇ q85))=(q84 ◇ (q85 ◇ ((q82 ◇ q81) ◇ q83))):=by
    intro q81 q82 q83 q84 q85
    exact (((rfl).symm).trans ((((cg (fun t => q84 ◇ t) ((h q85 (q82 ◇ q81) q83).symm)).symm).trans (apc80 q81 q82 q83 q84 q85)).trans (rfl))).symm
  have apc83 : forall (q76 q77 q78 q79 q80 q81 q82 q83 q84 q85 : G), (q79 ◇ ((q80 ◇ q78) ◇ (q80 ◇ (q77 ◇ q76))))=(q79 ◇ (q80 ◇ ((q77 ◇ q76) ◇ q78))):=by
    intro q76 q77 q78 q79 q80 q81 q82 q83 q84 q85
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc80 q76 q77 q78 q79 q80).trans (apc82 q76 q77 q78 q79 q80))).trans (rfl))
  have apc91 : forall (q86 q87 q88 : G), ((q87 ◇ q88) ◇ (q87 ◇ (q88 ◇ q86)))=(q87 ◇ (q88 ◇ (q86 ◇ q88))):=by
    intro q86 q87 q88
    exact ((apc4 q86 q88 q88 q87).symm).trans ((((apc51 q86 q88 q87 q88).symm).trans (apc29 (q86 ◇ q86) q87 q88)).trans ((cg (fun t => q87 ◇ t) (apc24 q88 q86)).trans (apc33 (q87 ◇ ((q88 ◇ q88) ◇ (q88 ◇ q86))) (q87 ◇ ((q88 ◇ q88) ◇ (q88 ◇ q86))) (q87 ◇ ((q88 ◇ q88) ◇ (q88 ◇ q86))) q86 q88 q87)))
  have apc92 : forall (q89 q90 q91 : G), (q90 ◇ ((q91 ◇ q89) ◇ q91))=(q90 ◇ (q91 ◇ (q89 ◇ q91))):=by
    intro q89 q90 q91
    exact (((rfl).symm).trans ((((apc91 q89 q90 q91).symm).trans ((h q90 (q91 ◇ q89) q91).symm)).trans (rfl))).symm
  have apc136 : forall (q92 q93 q94 q95 q96 : G), (q95 ◇ (q96 ◇ ((q94 ◇ q93) ◇ (q94 ◇ q92))))=((q95 ◇ (q94 ◇ (q92 ◇ q93))) ◇ (q95 ◇ q96)):=by
    intro q92 q93 q94 q95 q96
    exact (((rfl).symm).trans ((((cg (fun t => t ◇ (q95 ◇ q96)) (cg (fun t => q95 ◇ t) ((h q94 q92 q93).symm))).symm).trans (apc82 q93 q94 (q94 ◇ q92) q95 q96)).trans (rfl))).symm
  have apc137 : forall (q97 q98 q99 q100 q101 : G), ((q100 ◇ (q99 ◇ (q97 ◇ q98))) ◇ (q100 ◇ q101))=(q100 ◇ (q101 ◇ (q99 ◇ (q97 ◇ q98)))):=by
    intro q97 q98 q99 q100 q101
    exact (((rfl).symm).trans ((((cg (fun t => q100 ◇ t) (cg (fun t => q101 ◇ t) ((h q99 q97 q98).symm))).symm).trans (apc136 q97 q98 q99 q100 q101)).trans (rfl))).symm
  have apc138 : forall (q97 q98 q99 q100 q101 q92 q93 q94 q95 q96 : G), (q95 ◇ (q96 ◇ ((q94 ◇ q93) ◇ (q94 ◇ q92))))=(q95 ◇ (q96 ◇ (q94 ◇ (q92 ◇ q93)))):=by
    intro q97 q98 q99 q100 q101 q92 q93 q94 q95 q96
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc136 q92 q93 q94 q95 q96).trans (apc137 q92 q93 q94 q95 q96))).trans (rfl))
  have apc162 : forall (q102 q103 q104 q105 : G), (q105 ◇ ((q104 ◇ q104) ◇ (q103 ◇ (q102 ◇ q104))))=(q105 ◇ (q104 ◇ (q103 ◇ (q102 ◇ q104)))):=by
    intro q102 q103 q104 q105
    exact (((cg (fun t => q105 ◇ t) (apc62 q102 q104 q103)).symm).trans ((((cg (fun t => q105 ◇ t) (apc13 q102 q104 q103)).symm).trans (apc12 q103 (q102 ◇ q104) q104 q105)).trans (rfl))).symm
  have apc176 : forall (q106 q107 q108 : G), (((q107 ◇ q106) ◇ q108) ◇ (q107 ◇ (q106 ◇ q107)))=((q107 ◇ q106) ◇ (q107 ◇ q108)):=by
    intro q106 q107 q108
    exact ((rfl).symm).trans ((((apc92 q106 ((q107 ◇ q106) ◇ q108) q107).symm).trans ((h (q107 ◇ q106) q107 q108).symm)).trans (rfl))
  have apc260 : forall (q109 q110 q111 q112 : G), (q112 ◇ (q111 ◇ (q110 ◇ (q111 ◇ q109))))=(q112 ◇ (q111 ◇ (q110 ◇ (q109 ◇ q111)))):=by
    intro q109 q110 q111 q112
    exact (((cg (fun t => q112 ◇ t) (apc62 q109 q111 q110)).symm).trans ((((cg (fun t => q112 ◇ t) (cg (fun t => (q111 ◇ q111) ◇ t) ((h q110 q111 q109).symm))).symm).trans (apc162 q110 (q110 ◇ q109) q111 q112)).trans (apc138 (q112 ◇ (q111 ◇ ((q110 ◇ q109) ◇ (q110 ◇ q111)))) (q112 ◇ (q111 ◇ ((q110 ◇ q109) ◇ (q110 ◇ q111)))) (q112 ◇ (q111 ◇ ((q110 ◇ q109) ◇ (q110 ◇ q111)))) (q112 ◇ (q111 ◇ ((q110 ◇ q109) ◇ (q110 ◇ q111)))) (q112 ◇ (q111 ◇ ((q110 ◇ q109) ◇ (q110 ◇ q111)))) q111 q109 q110 q112 q111))).symm
  have apc261 : forall (q113 q114 q115 q116 : G), ((q115 ◇ q116) ◇ (q115 ◇ (q114 ◇ (q113 ◇ q115))))=(q115 ◇ ((q114 ◇ (q115 ◇ q113)) ◇ q116)):=by
    intro q113 q114 q115 q116
    exact ((rfl).symm).trans ((((apc260 q113 q114 q115 (q115 ◇ q116)).symm).trans ((h q115 (q114 ◇ (q115 ◇ q113)) q116).symm)).trans (rfl))
  have apc262 : forall (q117 q118 q119 q120 : G), (q119 ◇ ((q118 ◇ (q119 ◇ q117)) ◇ q120))=(q119 ◇ ((q118 ◇ (q117 ◇ q119)) ◇ q120)):=by
    intro q117 q118 q119 q120
    exact ((rfl).symm).trans ((((apc261 q117 q118 q119 q120).symm).trans ((h q119 (q118 ◇ (q117 ◇ q119)) q120).symm)).trans (rfl))
  have apc277 : forall (q121 q122 q123 q124 : G), (((q122 ◇ q123) ◇ q124) ◇ ((q122 ◇ q122) ◇ (q121 ◇ q123)))=((q122 ◇ q123) ◇ ((q122 ◇ q121) ◇ (q124 ◇ q124))):=by
    intro q121 q122 q123 q124
    exact ((rfl).symm).trans ((((apc12 q121 q123 q122 ((q122 ◇ q123) ◇ q124)).symm).trans (apc1 q122 (q121 ◇ q121) q123 q124)).trans (apc38 q122 q121 (q122 ◇ q123) q124))
  have apc280 : forall (q125 q126 q127 : G), (q125 ◇ ((q127 ◇ q127) ◇ (q126 ◇ q126)))=((q125 ◇ q126) ◇ (q125 ◇ q127)):=by
    intro q125 q126 q127
    exact (((apc176 q126 q125 q127).symm).trans ((((cg (fun t => ((q125 ◇ q126) ◇ q127) ◇ t) ((h q125 q126 q125).symm)).symm).trans (apc277 q125 q125 q126 q127)).trans (apc16 q127 q127 q126 q125))).symm
  have apc282 : forall (q128 q129 q130 : G), (q130 ◇ ((q129 ◇ q129) ◇ q128))=((q130 ◇ q128) ◇ (q130 ◇ q129)):=by
    intro q128 q129 q130
    exact ((((apc4 q129 q129 q128 q130).trans (apc6 q130 (q130 ◇ q128) q129)).trans (apc8 q129 q128 q130 ((q130 ◇ q128) ◇ ((q130 ◇ q130) ◇ q129)) ((q130 ◇ q128) ◇ ((q130 ◇ q130) ◇ q129)) ((q130 ◇ q128) ◇ ((q130 ◇ q130) ◇ q129)))).symm).trans ((((cg (fun t => q130 ◇ t) (apc280 q129 q128 q128)).symm).trans (apc6 q129 q130 (q128 ◇ q128))).trans (apc280 q130 q128 q129))
  have apc283 : forall (q128 q129 q130 q20 q21 q22 : G), (q21 ◇ (q20 ◇ (q22 ◇ q22)))=((q21 ◇ q22) ◇ (q21 ◇ q20)):=by
    intro q128 q129 q130 q20 q21 q22
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc6 q20 q21 q22).trans (apc282 q22 q20 q21))).trans (rfl))
  have apc288 : forall (q30 q131 q31 q132 : G), ((q30 ◇ q31) ◇ ((q132 ◇ q132) ◇ (q30 ◇ q131)))=((q30 ◇ q31) ◇ ((q132 ◇ q131) ◇ (q132 ◇ q30))):=by
    intro q30 q131 q31 q132
    exact ((apc0 q30 q131 q31 (q132 ◇ q132)).symm).trans ((((cg (fun t => t ◇ ((q30 ◇ q31) ◇ (q132 ◇ q132))) ((h q30 q131 q31).symm)).symm).trans (apc5 q132 (q30 ◇ q131) (q30 ◇ q31))).trans (((cg (fun t => (q30 ◇ q31) ◇ t) (apc4 q30 q30 q131 q132)).trans (apc83 q30 q30 q131 (q30 ◇ q31) q132 ((q30 ◇ q31) ◇ ((q132 ◇ q131) ◇ (q132 ◇ (q30 ◇ q30)))) ((q30 ◇ q31) ◇ ((q132 ◇ q131) ◇ (q132 ◇ (q30 ◇ q30)))) ((q30 ◇ q31) ◇ ((q132 ◇ q131) ◇ (q132 ◇ (q30 ◇ q30)))) ((q30 ◇ q31) ◇ ((q132 ◇ q131) ◇ (q132 ◇ (q30 ◇ q30)))) ((q30 ◇ q31) ◇ ((q132 ◇ q131) ◇ (q132 ◇ (q30 ◇ q30)))))).trans (cg (fun t => (q30 ◇ q31) ◇ t) (apc282 q131 q30 q132))))
  have apc289 : forall (q133 q134 q135 : G), ((q133 ◇ q135) ◇ (q133 ◇ (q134 ◇ q133)))=((q133 ◇ q135) ◇ (q133 ◇ (q133 ◇ q134))):=by
    intro q133 q134 q135
    exact ((rfl).symm).trans ((((cg (fun t => (q133 ◇ q135) ◇ t) ((h q133 q134 q133).symm)).symm).trans (apc288 q133 q134 q135 q133)).trans (apc9 q134 q133 q133 q135 ((q133 ◇ q135) ◇ ((q133 ◇ q134) ◇ (q133 ◇ q133))) ((q133 ◇ q135) ◇ ((q133 ◇ q134) ◇ (q133 ◇ q133))) ((q133 ◇ q135) ◇ ((q133 ◇ q134) ◇ (q133 ◇ q133))) ((q133 ◇ q135) ◇ ((q133 ◇ q134) ◇ (q133 ◇ q133)))))
  have apc290 : forall (q136 q137 q138 : G), ((q137 ◇ q138) ◇ (q137 ◇ (q137 ◇ q136)))=(q137 ◇ ((q136 ◇ q137) ◇ q138)):=by
    intro q136 q137 q138
    exact ((rfl).symm).trans ((((apc289 q137 q136 q138).symm).trans ((h q137 (q136 ◇ q137) q138).symm)).trans (rfl))
  have apc291 : forall (q139 q140 q141 : G), (q140 ◇ ((q140 ◇ q139) ◇ q141))=(q140 ◇ ((q139 ◇ q140) ◇ q141)):=by
    intro q139 q140 q141
    exact (((rfl).symm).trans ((((apc290 q139 q140 q141).symm).trans ((h q140 (q140 ◇ q139) q141).symm)).trans (rfl))).symm
  have apc294 : forall (q142 q143 q144 : G), (q144 ◇ ((q143 ◇ q144) ◇ (q144 ◇ q142)))=(q144 ◇ (q144 ◇ (q142 ◇ q143))):=by
    intro q142 q143 q144
    exact (((rfl).symm).trans ((((cg (fun t => q144 ◇ t) ((h q144 q142 q143).symm)).symm).trans (apc291 q143 q144 (q144 ◇ q142))).trans (rfl))).symm
  have apc303 : forall (q23 q24 q25 q26 q128 q129 q130 : G), (q26 ◇ ((q25 ◇ q24) ◇ (q25 ◇ q23)))=((q26 ◇ (q23 ◇ q24)) ◇ (q26 ◇ q25)):=by
    intro q23 q24 q25 q26 q128 q129 q130
    exact ((rfl).symm).trans ((((cg (fun t => q26 ◇ t) (apc282 q24 q23 q25)).symm).trans ((apc12 q23 q24 q25 q26).trans (apc282 (q23 ◇ q24) q25 q26))).trans (rfl))
  have apc304 : forall (q145 q146 q147 q148 : G), ((q148 ◇ (q145 ◇ q146)) ◇ (q148 ◇ q147))=(q148 ◇ (q147 ◇ (q145 ◇ q146))):=by
    intro q145 q146 q147 q148
    exact (((rfl).symm).trans ((((cg (fun t => q148 ◇ t) ((h q147 q145 q146).symm)).symm).trans (apc303 q145 q146 q147 q148 q145 q145 q145)).trans (rfl))).symm
  have apc305 : forall (q145 q146 q147 q148 q23 q24 q25 q26 q128 q129 q130 : G), (q26 ◇ ((q25 ◇ q24) ◇ (q25 ◇ q23)))=(q26 ◇ (q25 ◇ (q23 ◇ q24))):=by
    intro q145 q146 q147 q148 q23 q24 q25 q26 q128 q129 q130
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc303 q23 q24 q25 q26 q23 q23 q23).trans (apc304 q23 q24 q25 q26))).trans (rfl))
  have apc312 : forall (q149 q150 : G), (((q149 ◇ q149) ◇ q149) ◇ ((q149 ◇ q149) ◇ q150))=((q149 ◇ q149) ◇ (q149 ◇ q150)):=by
    intro q149 q150
    exact ((rfl).symm).trans ((((apc282 q149 q150 (q149 ◇ q149)).symm).trans (apc59 q149 q150)).trans (rfl))
  have apc313 : forall (q151 q152 : G), ((q152 ◇ q152) ◇ (q152 ◇ q151))=((q152 ◇ q152) ◇ (q151 ◇ q152)):=by
    intro q151 q152
    exact ((rfl).symm).trans ((((apc312 q152 q151).symm).trans ((h (q152 ◇ q152) q151 q152).symm)).trans (rfl))
  have apc314 : forall (q153 q154 : G), ((q154 ◇ q154) ◇ (q153 ◇ q154))=(q154 ◇ (q153 ◇ q154)):=by
    intro q153 q154
    exact ((rfl).symm).trans ((((apc313 q153 q154).symm).trans ((h q154 q153 q154).symm)).trans (rfl))
  have apc316 : forall (q151 q152 q153 q154 : G), ((q152 ◇ q152) ◇ (q152 ◇ q151))=(q152 ◇ (q151 ◇ q152)):=by
    intro q151 q152 q153 q154
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc313 q151 q152).trans (apc314 q151 q152))).trans (rfl))
  have apc418 : forall (q155 q156 q157 q158 : G), (q158 ◇ (q157 ◇ (q155 ◇ (q158 ◇ q156))))=(q158 ◇ (q157 ◇ (q155 ◇ (q156 ◇ q158)))):=by
    intro q155 q156 q157 q158
    exact ((rfl).symm).trans ((((cg (fun t => q158 ◇ t) ((h q157 q155 (q158 ◇ q156)).symm)).symm).trans (apc262 q156 q157 q158 (q157 ◇ q155))).trans (cg (fun t => q158 ◇ t) (apc304 q156 q158 q155 q157)))
  have apc437 : forall (q159 q160 q161 q162 : G), (q161 ◇ (q162 ◇ (q161 ◇ (q159 ◇ q160))))=(q161 ◇ (q162 ◇ ((q159 ◇ q160) ◇ q161))):=by
    intro q159 q160 q161 q162
    exact ((apc304 q161 (q159 ◇ q160) q162 q161).symm).trans ((((cg (fun t => t ◇ (q161 ◇ q162)) (apc294 q159 q160 q161)).symm).trans ((h q161 q162 ((q160 ◇ q161) ◇ (q161 ◇ q159))).symm)).trans (((apc418 (q160 ◇ q161) q159 q162 q161).trans (cg (fun t => q161 ◇ t) (apc4 q160 q159 q161 q162))).trans (apc305 (q161 ◇ ((q162 ◇ q161) ◇ (q162 ◇ (q159 ◇ q160)))) (q161 ◇ ((q162 ◇ q161) ◇ (q162 ◇ (q159 ◇ q160)))) (q161 ◇ ((q162 ◇ q161) ◇ (q162 ◇ (q159 ◇ q160)))) (q161 ◇ ((q162 ◇ q161) ◇ (q162 ◇ (q159 ◇ q160)))) (q159 ◇ q160) q161 q162 q161 (q161 ◇ ((q162 ◇ q161) ◇ (q162 ◇ (q159 ◇ q160)))) (q161 ◇ ((q162 ◇ q161) ◇ (q162 ◇ (q159 ◇ q160)))) (q161 ◇ ((q162 ◇ q161) ◇ (q162 ◇ (q159 ◇ q160)))))))
  have apc439 : forall (q163 q164 q165 : G), (q164 ◇ (q165 ◇ (q164 ◇ q163)))=(q164 ◇ (q165 ◇ (q163 ◇ q164))):=by
    intro q163 q164 q165
    exact ((apc305 (q164 ◇ ((q165 ◇ q163) ◇ (q165 ◇ q164))) (q164 ◇ ((q165 ◇ q163) ◇ (q165 ◇ q164))) (q164 ◇ ((q165 ◇ q163) ◇ (q165 ◇ q164))) (q164 ◇ ((q165 ◇ q163) ◇ (q165 ◇ q164))) q164 q163 q165 q164 (q164 ◇ ((q165 ◇ q163) ◇ (q165 ◇ q164))) (q164 ◇ ((q165 ◇ q163) ◇ (q165 ◇ q164))) (q164 ◇ ((q165 ◇ q163) ◇ (q165 ◇ q164)))).symm).trans ((((cg (fun t => q164 ◇ t) (apc283 q163 q163 q163 q164 q165 q163)).symm).trans (apc437 q163 q163 q164 q165)).trans ((cg (fun t => q164 ◇ t) (apc282 q164 q163 q165)).trans (apc305 (q164 ◇ ((q165 ◇ q164) ◇ (q165 ◇ q163))) (q164 ◇ ((q165 ◇ q164) ◇ (q165 ◇ q163))) (q164 ◇ ((q165 ◇ q164) ◇ (q165 ◇ q163))) (q164 ◇ ((q165 ◇ q164) ◇ (q165 ◇ q163))) q163 q164 q165 q164 (q164 ◇ ((q165 ◇ q164) ◇ (q165 ◇ q163))) (q164 ◇ ((q165 ◇ q164) ◇ (q165 ◇ q163))) (q164 ◇ ((q165 ◇ q164) ◇ (q165 ◇ q163))))))
  have apc440 : forall (q142 q143 q144 q163 q164 q165 : G), (q144 ◇ (q144 ◇ (q142 ◇ q143)))=(q144 ◇ ((q142 ◇ q143) ◇ q144)):=by
    intro q142 q143 q144 q163 q164 q165
    exact ((((apc4 q143 q142 q144 q144).trans (apc316 (q142 ◇ q143) q144 ((q144 ◇ q144) ◇ (q144 ◇ (q142 ◇ q143))) ((q144 ◇ q144) ◇ (q144 ◇ (q142 ◇ q143))))).symm).trans ((((apc439 q142 q144 (q143 ◇ q144)).symm).trans ((apc294 q142 q143 q144).trans (rfl))).trans (rfl))).symm
  have apc441 : forall (q166 q167 : G), ((q166 ◇ q167) ◇ (q166 ◇ q166))=(q166 ◇ (q167 ◇ q166)):=by
    intro q166 q167
    exact ((((apc282 q166 q167 q166).trans (apc316 q167 q166 ((q166 ◇ q166) ◇ (q166 ◇ q167)) ((q166 ◇ q166) ◇ (q166 ◇ q167)))).symm).trans ((((apc440 q167 q167 q166 q166 q166 q166).symm).trans (apc283 q166 q166 q166 q166 q166 q167)).trans (rfl))).symm
  have apc442 : forall (q168 q169 : G), (q168 ◇ (q169 ◇ q168))=(q168 ◇ (q168 ◇ q169)):=by
    intro q168 q169
    exact ((rfl).symm).trans ((((apc441 q168 q169).symm).trans ((h q168 q168 q169).symm)).trans (rfl))
  exact (calc
    (x ◇ (x ◇ y))=(x ◇ (x ◇ y)):=rfl
    _=(x ◇ ((y ◇ y) ◇ x)):=(((apc282 x y x).trans (apc316 y x ((x ◇ x) ◇ (x ◇ y)) ((x ◇ x) ◇ (x ◇ y)))).trans (apc442 x y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_56101_to_54749 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_56101_to_54749
