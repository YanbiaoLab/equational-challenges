-- Equation60566 → Equation62248
-- Recorded verdict: true
-- Premise: (x ◇ y) ◇ z = (y ◇ z) ◇ (y ◇ x)
-- Conclusion: (x ◇ y) ◇ z = ((x ◇ z) ◇ z) ◇ y
-- Original submission SHA-256: 140327376a89be5a6d5491c681e0c3957801da5a7ae21b93cc28be97d0a9cdad
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ z = (y ◇ z) ◇ (y ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ z = ((x ◇ z) ◇ z) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f : G → G) {a b : G}, a=b → f a=f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1 q2 q3 : G), (((q0 ◇ q1) ◇ q2) ◇ ((q1 ◇ q2) ◇ q3))=((q3 ◇ (q1 ◇ q2)) ◇ (q1 ◇ q0)):=by
    intro q0 q1 q2 q3
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ ((q1 ◇ q2) ◇ q3)) ((h q0 q1 q2).symm)).symm).trans ((h q3 (q1 ◇ q2) (q1 ◇ q0)).symm)).trans (rfl))
  have apc1 : forall (q0 q1 q2 q4 : G), (((q1 ◇ q2) ◇ q4) ◇ ((q0 ◇ q1) ◇ q2))=(((q1 ◇ q0) ◇ (q1 ◇ q2)) ◇ q4):=by
    intro q0 q1 q2 q4
    exact ((rfl).symm).trans ((((cg (fun t => ((q1 ◇ q2) ◇ q4) ◇ t) ((h q0 q1 q2).symm)).symm).trans ((h (q1 ◇ q0) (q1 ◇ q2) q4).symm)).trans (rfl))
  have apc2 : forall (q5 q6 : G), (((q5 ◇ q5) ◇ (q5 ◇ q5)) ◇ q6)=((q5 ◇ (q5 ◇ q5)) ◇ q6):=by
    intro q5 q6
    exact ((rfl).symm).trans ((((apc1 q5 q5 q5 q6).symm).trans ((h q5 (q5 ◇ q5) q6).symm)).trans (rfl))
  have apc3 : forall (q7 q8 : G), ((q7 ◇ (q7 ◇ q7)) ◇ q8)=(((q7 ◇ q7) ◇ q7) ◇ q8):=by
    intro q7 q8
    exact (((rfl).symm).trans ((((cg (fun t => t ◇ q8) ((h q7 q7 q7).symm)).symm).trans (apc2 q7 q8)).trans (rfl))).symm
  have apc4 : forall (q9 q10 : G), (((q10 ◇ q10) ◇ q10) ◇ (q10 ◇ q9))=((q9 ◇ q10) ◇ (q10 ◇ q10)):=by
    intro q9 q10
    exact ((rfl).symm).trans ((((apc3 q10 (q10 ◇ q9)).symm).trans ((h q9 q10 (q10 ◇ q10)).symm)).trans (rfl))
  have apc5 : forall (q7 q8 q5 q6 : G), (((q5 ◇ q5) ◇ (q5 ◇ q5)) ◇ q6)=(((q5 ◇ q5) ◇ q5) ◇ q6):=by
    intro q7 q8 q5 q6
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc2 q5 q6).trans (apc3 q5 q6))).trans (rfl))
  have apc6 : forall (q11 q12 : G), ((q12 ◇ (q12 ◇ q11)) ◇ (q12 ◇ q11))=(((q11 ◇ q12) ◇ (q11 ◇ q12)) ◇ q11):=by
    intro q11 q12
    exact (((rfl).symm).trans ((((apc1 q12 q11 q12 q11).symm).trans (apc0 q11 q12 q11 q12)).trans (rfl))).symm
  have apc7 : forall (q13 q14 : G), (((q13 ◇ q14) ◇ (q13 ◇ q14)) ◇ q13)=((q13 ◇ q14) ◇ (q14 ◇ q13)):=by
    intro q13 q14
    exact ((rfl).symm).trans ((((apc6 q13 q14).symm).trans ((h q13 q14 (q14 ◇ q13)).symm)).trans (rfl))
  have apc8 : forall (q15 q16 : G), (((q16 ◇ q15) ◇ q16) ◇ q15)=((q15 ◇ q16) ◇ (q16 ◇ q15)):=by
    intro q15 q16
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q15) ((h q16 q15 q16).symm)).symm).trans (apc7 q15 q16)).trans (rfl))
  have apc9 : forall (q17 q18 : G), ((q18 ◇ (q17 ◇ q17)) ◇ (q17 ◇ q17))=((q18 ◇ (q17 ◇ q17)) ◇ q17):=by
    intro q17 q18
    exact ((rfl).symm).trans ((((apc0 q17 q17 q17 q18).symm).trans ((h q18 (q17 ◇ q17) q17).symm)).trans (rfl))
  have apc10 : forall (q19 q20 : G), (((q20 ◇ q20) ◇ q19) ◇ (q20 ◇ q20))=(((q20 ◇ q19) ◇ (q20 ◇ q20)) ◇ q20):=by
    intro q19 q20
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (q20 ◇ q20)) ((h q20 q20 q19).symm)).symm).trans (apc9 q20 (q20 ◇ q19))).trans (rfl))
  have apc11 : forall (q21 q22 : G), (((q22 ◇ (q22 ◇ q21)) ◇ (q22 ◇ q22)) ◇ q22)=(((q21 ◇ q22) ◇ q22) ◇ (q22 ◇ q22)):=by
    intro q21 q22
    exact (((rfl).symm).trans ((((cg (fun t => t ◇ (q22 ◇ q22)) ((h q21 q22 q22).symm)).symm).trans (apc10 (q22 ◇ q21) q22)).trans (rfl))).symm
  have apc12 : forall (q23 q24 : G), (((q24 ◇ q24) ◇ (q24 ◇ q23)) ◇ q24)=(((q23 ◇ q24) ◇ q24) ◇ (q24 ◇ q24)):=by
    intro q23 q24
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q24) ((h q24 q24 (q24 ◇ q23)).symm)).symm).trans (apc11 q23 q24)).trans (rfl))
  have apc13 : forall (q25 q26 : G), (((q25 ◇ q26) ◇ q26) ◇ (q26 ◇ q26))=(((q25 ◇ q26) ◇ q26) ◇ q26):=by
    intro q25 q26
    exact (((rfl).symm).trans ((((cg (fun t => t ◇ q26) ((h q25 q26 q26).symm)).symm).trans (apc12 q25 q26)).trans (rfl))).symm
  have apc15 : forall (q21 q22 q25 q26 : G), (((q22 ◇ (q22 ◇ q21)) ◇ (q22 ◇ q22)) ◇ q22)=(((q21 ◇ q22) ◇ q22) ◇ q22):=by
    intro q21 q22 q25 q26
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc11 q21 q22).trans (apc13 q21 q22))).trans (rfl))
  have apc18 : forall (q27 q28 q29 q30 q31 : G), ((q30 ◇ q31) ◇ (q30 ◇ ((q27 ◇ q28) ◇ q29)))=((((q28 ◇ q29) ◇ (q28 ◇ q27)) ◇ q30) ◇ q31):=by
    intro q27 q28 q29 q30 q31
    exact ((rfl).symm).trans ((((cg (fun t => (q30 ◇ q31) ◇ t) (cg (fun t => q30 ◇ t) ((h q27 q28 q29).symm))).symm).trans ((h ((q28 ◇ q29) ◇ (q28 ◇ q27)) q30 q31).symm)).trans (rfl))
  have apc19 : forall (q32 q33 q34 q35 q36 : G), ((((q33 ◇ q34) ◇ (q33 ◇ q32)) ◇ q35) ◇ q36)=((((q32 ◇ q33) ◇ q34) ◇ q35) ◇ q36):=by
    intro q32 q33 q34 q35 q36
    exact ((rfl).symm).trans ((((apc18 q32 q33 q34 q35 q36).symm).trans ((h ((q32 ◇ q33) ◇ q34) q35 q36).symm)).trans (rfl))
  have apc21 : forall (q37 q38 q39 : G), ((((q37 ◇ q37) ◇ q38) ◇ (q37 ◇ q37)) ◇ q39)=((((q37 ◇ q37) ◇ q38) ◇ q37) ◇ q39):=by
    intro q37 q38 q39
    exact (((apc19 q37 q37 q38 q37 q39).symm).trans ((((cg (fun t => t ◇ q39) (apc9 q37 (q37 ◇ q38))).symm).trans (apc19 q37 q37 q38 (q37 ◇ q37) q39)).trans (rfl))).symm
  have apc22 : forall (q40 q41 : G), ((q41 ◇ (q40 ◇ q40)) ◇ ((q40 ◇ q40) ◇ q41))=((((q40 ◇ q40) ◇ q41) ◇ q40) ◇ q41):=by
    intro q40 q41
    exact (((rfl).symm).trans ((((apc21 q40 q41 q41).symm).trans (apc8 q41 (q40 ◇ q40))).trans (rfl))).symm
  have apc23 : forall (q42 q43 q44 q45 : G), (((q44 ◇ q42) ◇ (q44 ◇ q45)) ◇ (q44 ◇ q43))=(((q43 ◇ q44) ◇ q45) ◇ ((q42 ◇ q44) ◇ q45)):=by
    intro q42 q43 q44 q45
    exact (((rfl).symm).trans ((((cg (fun t => ((q43 ◇ q44) ◇ q45) ◇ t) ((h q42 q44 q45).symm)).symm).trans (apc0 q43 q44 q45 (q44 ◇ q42))).trans (rfl))).symm
  have apc24 : forall (q46 q47 q48 q49 : G), (((q47 ◇ q48) ◇ q49) ◇ ((q46 ◇ q48) ◇ q49))=(((q49 ◇ q48) ◇ q46) ◇ (q48 ◇ q47)):=by
    intro q46 q47 q48 q49
    exact (((rfl).symm).trans ((((cg (fun t => t ◇ (q48 ◇ q47)) ((h q49 q48 q46).symm)).symm).trans (apc23 q46 q47 q48 q49)).trans (rfl))).symm
  have apc25 : forall (q50 q51 q52 : G), (((q52 ◇ q51) ◇ q50) ◇ (q51 ◇ q50))=((q52 ◇ (q50 ◇ q51)) ◇ q52):=by
    intro q50 q51 q52
    exact ((rfl).symm).trans ((((apc24 q50 q50 q51 q52).symm).trans ((h q52 (q50 ◇ q51) q52).symm)).trans (rfl))
  have apc26 : forall (q25 q26 q50 q51 q52 : G), ((q25 ◇ (q26 ◇ q26)) ◇ q25)=(((q25 ◇ q26) ◇ q26) ◇ q26):=by
    intro q25 q26 q50 q51 q52
    exact ((rfl).symm).trans ((((apc25 q26 q26 q25).symm).trans ((apc13 q25 q26).trans (rfl))).trans (rfl))
  have apc27 : forall (q27 q28 q29 q53 q30 : G), ((q30 ◇ ((q27 ◇ q28) ◇ q29)) ◇ (q30 ◇ q53))=((q53 ◇ q30) ◇ ((q28 ◇ q29) ◇ (q28 ◇ q27))):=by
    intro q27 q28 q29 q53 q30
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (q30 ◇ q53)) (cg (fun t => q30 ◇ t) ((h q27 q28 q29).symm))).symm).trans ((h q53 q30 ((q28 ◇ q29) ◇ (q28 ◇ q27))).symm)).trans (rfl))
  have apc28 : forall (q54 q55 : G), ((((q55 ◇ q54) ◇ q55) ◇ q55) ◇ q55)=((q55 ◇ (q54 ◇ q55)) ◇ q55):=by
    intro q54 q55
    exact (((apc25 q54 q55 q55).symm).trans ((((cg (fun t => t ◇ (q55 ◇ q54)) ((h q55 q55 q54).symm)).symm).trans (apc26 (q55 ◇ q54) q55 q54 q54 q54)).trans (rfl))).symm
  have apc29 : forall (q56 q57 q58 : G), (((q56 ◇ q58) ◇ q57) ◇ (q57 ◇ (q58 ◇ q56)))=((q58 ◇ ((q58 ◇ q56) ◇ q57)) ◇ q58):=by
    intro q56 q57 q58
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (q57 ◇ (q58 ◇ q56))) ((h q56 q58 q57).symm)).symm).trans (apc25 (q58 ◇ q56) q57 q58)).trans (rfl))
  have apc32 : forall (q59 q60 : G), (((q60 ◇ (q59 ◇ q59)) ◇ (q60 ◇ q60)) ◇ q60)=((((q60 ◇ q60) ◇ q59) ◇ q59) ◇ q59):=by
    intro q59 q60
    exact (((rfl).symm).trans ((((apc26 (q60 ◇ q60) q59 q59 q59 q59).symm).trans (apc10 (q59 ◇ q59) q60)).trans (rfl))).symm
  have apc33 : forall (q61 q62 : G), ((((q62 ◇ q62) ◇ q61) ◇ q61) ◇ q61)=(((q62 ◇ q62) ◇ (q61 ◇ q61)) ◇ q62):=by
    intro q61 q62
    exact (((rfl).symm).trans ((((cg (fun t => t ◇ q62) ((h q62 q62 (q61 ◇ q61)).symm)).symm).trans (apc32 q61 q62)).trans (rfl))).symm
  have apc34 : forall (q42 q43 q44 q45 q46 q47 q48 q49 : G), (((q44 ◇ q42) ◇ (q44 ◇ q45)) ◇ (q44 ◇ q43))=(((q45 ◇ q44) ◇ q42) ◇ (q44 ◇ q43)):=by
    intro q42 q43 q44 q45 q46 q47 q48 q49
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc23 q42 q43 q44 q45).trans (apc24 q42 q43 q44 q45))).trans (rfl))
  have apc35 : forall (q61 q62 q59 q60 : G), (((q60 ◇ (q59 ◇ q59)) ◇ (q60 ◇ q60)) ◇ q60)=(((q60 ◇ q60) ◇ (q59 ◇ q59)) ◇ q60):=by
    intro q61 q62 q59 q60
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc32 q59 q60).trans (apc33 q59 q60))).trans (rfl))
  have apc36 : forall (q27 q28 q29 q53 q31 : G), ((((q27 ◇ q28) ◇ q29) ◇ q31) ◇ (((q27 ◇ q28) ◇ q29) ◇ q53))=((q53 ◇ ((q28 ◇ q29) ◇ (q28 ◇ q27))) ◇ q31):=by
    intro q27 q28 q29 q53 q31
    exact ((apc19 q27 q28 q29 q31 (((q27 ◇ q28) ◇ q29) ◇ q53)).symm).trans ((((cg (fun t => (((q28 ◇ q29) ◇ (q28 ◇ q27)) ◇ q31) ◇ t) (cg (fun t => t ◇ q53) ((h q27 q28 q29).symm))).symm).trans ((h q53 ((q28 ◇ q29) ◇ (q28 ◇ q27)) q31).symm)).trans (rfl))
  have apc38 : forall (q63 q64 : G), (((q63 ◇ q64) ◇ q64) ◇ (q64 ◇ (q64 ◇ q64)))=((q64 ◇ (q63 ◇ (q64 ◇ q64))) ◇ q64):=by
    intro q63 q64
    exact ((apc24 q64 (q64 ◇ q64) q64 q63).symm).trans ((((cg (fun t => t ◇ ((q64 ◇ q64) ◇ q63)) (apc3 q64 q63)).symm).trans (apc25 q63 (q64 ◇ q64) q64)).trans (rfl))
  have apc40 : forall (q65 q66 : G), ((q65 ◇ ((q65 ◇ q65) ◇ q66)) ◇ q65)=((((q66 ◇ q65) ◇ q65) ◇ q65) ◇ q65):=by
    intro q65 q66
    exact ((((apc25 q65 q65 (q66 ◇ q65)).trans (apc26 (q66 ◇ q65) q65 (((q66 ◇ q65) ◇ (q65 ◇ q65)) ◇ (q66 ◇ q65)) (((q66 ◇ q65) ◇ (q65 ◇ q65)) ◇ (q66 ◇ q65)) (((q66 ◇ q65) ◇ (q65 ◇ q65)) ◇ (q66 ◇ q65)))).symm).trans ((((cg (fun t => t ◇ (q65 ◇ q65)) (apc26 q66 q65 q65 q65 q65)).symm).trans (apc8 (q65 ◇ q65) q66)).trans (apc29 q65 q66 q65))).symm
  have apc41 : forall (q67 q68 : G), ((q68 ◇ ((q67 ◇ q68) ◇ q68)) ◇ q68)=(((q68 ◇ (q67 ◇ q68)) ◇ q68) ◇ q68):=by
    intro q67 q68
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q68) (cg (fun t => q68 ◇ t) ((h q67 q68 q68).symm))).symm).trans (apc40 q68 (q68 ◇ q67))).trans (cg (fun t => t ◇ q68) (apc28 q67 q68)))
  have apc42 : forall (q69 q70 q71 q72 q73 : G), ((q72 ◇ q73) ◇ ((q70 ◇ q71) ◇ (q70 ◇ q69)))=((q72 ◇ q73) ◇ ((q69 ◇ q70) ◇ q71)):=by
    intro q69 q70 q71 q72 q73
    exact ((rfl).symm).trans ((((apc27 q69 q70 q71 q72 q73).symm).trans ((h q72 q73 ((q69 ◇ q70) ◇ q71)).symm)).trans (rfl))
  have apc43 : forall (q74 q75 : G), (((q74 ◇ (q75 ◇ q75)) ◇ q75) ◇ (q75 ◇ q75))=(((q74 ◇ (q75 ◇ q75)) ◇ q75) ◇ q75):=by
    intro q74 q75
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (q75 ◇ q75)) (apc9 q75 q74)).symm).trans (apc9 q75 (q74 ◇ (q75 ◇ q75)))).trans (cg (fun t => t ◇ q75) (apc9 q75 q74)))
  have apc45 : forall (q76 q77 q78 q79 q80 : G), ((q79 ◇ ((q77 ◇ q78) ◇ (q77 ◇ q76))) ◇ q80)=((q79 ◇ ((q76 ◇ q77) ◇ q78)) ◇ q80):=by
    intro q76 q77 q78 q79 q80
    exact ((rfl).symm).trans ((((apc36 q76 q77 q78 q79 q80).symm).trans ((h q79 ((q76 ◇ q77) ◇ q78) q80).symm)).trans (rfl))
  have apc46 : forall (q81 q82 q83 : G), (((q81 ◇ q82) ◇ q83) ◇ ((q82 ◇ q81) ◇ (q83 ◇ q82)))=((q83 ◇ ((q83 ◇ q82) ◇ (q82 ◇ q81))) ◇ q83):=by
    intro q81 q82 q83
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ ((q82 ◇ q81) ◇ (q83 ◇ q82))) ((h q81 q82 q83).symm)).symm).trans (apc29 q82 (q82 ◇ q81) q83)).trans (rfl))
  have apc49 : forall (q84 q85 : G), (((q85 ◇ (q84 ◇ q85)) ◇ q85) ◇ q85)=((q84 ◇ (q85 ◇ q85)) ◇ (q85 ◇ q84)):=by
    intro q84 q85
    exact (((apc0 q84 q85 q85 q84).symm).trans ((((cg (fun t => ((q84 ◇ q85) ◇ q85) ◇ t) ((h q85 q85 q84).symm)).symm).trans (apc46 q84 q85 q85)).trans ((apc45 q84 q85 q85 q85 q85).trans (apc41 q84 q85)))).symm
  have apc56 : forall (q86 q87 q88 : G), (((q86 ◇ q87) ◇ ((q87 ◇ q86) ◇ q87)) ◇ q88)=(((q87 ◇ (q87 ◇ q86)) ◇ q87) ◇ q88):=by
    intro q86 q87 q88
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q88) (cg (fun t => (q86 ◇ q87) ◇ t) ((h q87 q86 q87).symm))).symm).trans (apc3 (q86 ◇ q87) q88)).trans ((cg (fun t => t ◇ q88) (apc34 q87 q87 q86 q87 (((q86 ◇ q87) ◇ (q86 ◇ q87)) ◇ (q86 ◇ q87)) (((q86 ◇ q87) ◇ (q86 ◇ q87)) ◇ (q86 ◇ q87)) (((q86 ◇ q87) ◇ (q86 ◇ q87)) ◇ (q86 ◇ q87)) (((q86 ◇ q87) ◇ (q86 ◇ q87)) ◇ (q86 ◇ q87)))).trans (cg (fun t => t ◇ q88) (apc25 q87 q86 q87))))
  have apc57 : forall (q89 q54 q90 : G), (((q90 ◇ (q89 ◇ q54)) ◇ (q89 ◇ q54)) ◇ (q89 ◇ q54))=((q90 ◇ ((q54 ◇ q89) ◇ q54)) ◇ q90):=by
    intro q89 q54 q90
    exact (((rfl).symm).trans ((((cg (fun t => t ◇ q90) (cg (fun t => q90 ◇ t) ((h q54 q89 q54).symm))).symm).trans (apc26 q90 (q89 ◇ q54) q89 q89 q89)).trans (rfl))).symm
  have apc59 : forall (q91 q92 : G), ((q92 ◇ ((q91 ◇ q91) ◇ q91)) ◇ q92)=(((q92 ◇ (q91 ◇ q91)) ◇ q91) ◇ q91):=by
    intro q91 q92
    exact (((apc43 q92 q91).symm).trans ((((cg (fun t => t ◇ (q91 ◇ q91)) (apc9 q91 q92)).symm).trans (apc57 q91 q91 q92)).trans (rfl))).symm
  have apc63 : forall (q69 q70 q71 q72 q73 q27 q28 q29 q53 q30 : G), ((q30 ◇ ((q27 ◇ q28) ◇ q29)) ◇ (q30 ◇ q53))=((q53 ◇ q30) ◇ ((q27 ◇ q28) ◇ q29)):=by
    intro q69 q70 q71 q72 q73 q27 q28 q29 q53 q30
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc27 q27 q28 q29 q53 q30).trans (apc42 q27 q28 q29 q53 q30))).trans (rfl))
  have apc64 : forall (q93 q94 q95 q96 : G), (((q95 ◇ (q94 ◇ q93)) ◇ q96) ◇ ((q93 ◇ q94) ◇ q95))=(((q95 ◇ q94) ◇ (q95 ◇ (q94 ◇ q93))) ◇ q96):=by
    intro q93 q94 q95 q96
    exact ((rfl).symm).trans ((((cg (fun t => ((q95 ◇ (q94 ◇ q93)) ◇ q96) ◇ t) ((h q93 q94 q95).symm)).symm).trans (apc1 q94 q95 (q94 ◇ q93) q96)).trans (rfl))
  have apc65 : forall (q97 q98 : G), (((q98 ◇ q97) ◇ (q98 ◇ (q97 ◇ q97))) ◇ q98)=((q98 ◇ (q98 ◇ (q97 ◇ q97))) ◇ q98):=by
    intro q97 q98
    exact ((rfl).symm).trans ((((apc64 q97 q97 q98 q98).symm).trans (apc25 q98 (q97 ◇ q97) q98)).trans (rfl))
  have apc66 : forall (q99 q100 : G), ((q100 ◇ (q100 ◇ (q99 ◇ q99))) ◇ q100)=((((q99 ◇ q99) ◇ q100) ◇ q99) ◇ q100):=by
    intro q99 q100
    exact (((rfl).symm).trans ((((cg (fun t => t ◇ q100) ((h (q99 ◇ q99) q100 q99).symm)).symm).trans (apc65 q99 q100)).trans (rfl))).symm
  have apc69 : forall (q101 q9 q102 : G), ((((q101 ◇ q101) ◇ q101) ◇ q102) ◇ (((q101 ◇ q101) ◇ q101) ◇ q9))=((q9 ◇ (q101 ◇ (q101 ◇ q101))) ◇ q102):=by
    intro q101 q9 q102
    exact ((cg (fun t => (((q101 ◇ q101) ◇ q101) ◇ q102) ◇ t) (apc3 q101 q9)).symm).trans ((((cg (fun t => t ◇ ((q101 ◇ (q101 ◇ q101)) ◇ q9)) (apc3 q101 q102)).symm).trans ((h q9 (q101 ◇ (q101 ◇ q101)) q102).symm)).trans (rfl))
  have apc70 : forall (q103 q104 q105 : G), ((q104 ◇ (q103 ◇ (q103 ◇ q103))) ◇ q105)=((q104 ◇ ((q103 ◇ q103) ◇ q103)) ◇ q105):=by
    intro q103 q104 q105
    exact ((rfl).symm).trans ((((apc69 q103 q104 q105).symm).trans ((h q104 ((q103 ◇ q103) ◇ q103) q105).symm)).trans (rfl))
  have apc71 : forall (q106 q107 q108 : G), (((q107 ◇ q106) ◇ ((q107 ◇ q107) ◇ q107)) ◇ q108)=((((q107 ◇ q107) ◇ q107) ◇ q106) ◇ q108):=by
    intro q106 q107 q108
    exact (((rfl).symm).trans ((((cg (fun t => t ◇ q108) ((h (q107 ◇ q107) q107 q106).symm)).symm).trans (apc70 q107 (q107 ◇ q106) q108)).trans (rfl))).symm
  have apc72 : forall (q109 q110 : G), (((q110 ◇ q110) ◇ (q109 ◇ q110)) ◇ (q110 ◇ q110))=((((q110 ◇ q110) ◇ q109) ◇ q110) ◇ q110):=by
    intro q109 q110
    exact ((apc25 q109 q110 (q110 ◇ q110)).symm).trans ((((apc71 q109 q110 (q110 ◇ q109)).symm).trans (apc59 q110 (q110 ◇ q109))).trans (apc19 q110 q110 q109 q110 q110))
  have apc73 : forall (q111 q112 : G), (((q112 ◇ (q111 ◇ q112)) ◇ (q112 ◇ q112)) ◇ q112)=((((q112 ◇ q112) ◇ q111) ◇ q112) ◇ q112):=by
    intro q111 q112
    exact (((rfl).symm).trans ((((apc72 q111 q112).symm).trans (apc10 (q111 ◇ q112) q112)).trans (rfl))).symm
  have apc74 : forall (q113 q114 : G), ((((q114 ◇ q114) ◇ q113) ◇ q114) ◇ q114)=(((q114 ◇ q114) ◇ (q113 ◇ q114)) ◇ q114):=by
    intro q113 q114
    exact (((rfl).symm).trans ((((cg (fun t => t ◇ q114) ((h q114 q114 (q113 ◇ q114)).symm)).symm).trans (apc73 q113 q114)).trans (rfl))).symm
  have apc77 : forall (q113 q114 q111 q112 : G), (((q112 ◇ (q111 ◇ q112)) ◇ (q112 ◇ q112)) ◇ q112)=(((q112 ◇ q112) ◇ (q111 ◇ q112)) ◇ q112):=by
    intro q113 q114 q111 q112
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc73 q111 q112).trans (apc74 q111 q112))).trans (rfl))
  have apc95 : forall (q115 q116 : G), ((((q115 ◇ q115) ◇ q115) ◇ q116) ◇ ((q115 ◇ q115) ◇ q115))=(((q115 ◇ q115) ◇ q115) ◇ q116):=by
    intro q115 q116
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ ((q115 ◇ q115) ◇ q115)) (apc3 q115 q116)).symm).trans (apc64 q115 q115 q115 q116)).trans (((((apc70 q115 (q115 ◇ q115) q116).trans (apc56 q115 q115 q116)).trans (cg (fun t => t ◇ q116) (apc3 q115 q115))).trans (cg (fun t => t ◇ q116) (apc8 q115 q115))).trans (apc5 (((q115 ◇ q115) ◇ (q115 ◇ q115)) ◇ q116) (((q115 ◇ q115) ◇ (q115 ◇ q115)) ◇ q116) q115 q116)))
  have apc98 : forall (q117 q118 : G), (((q117 ◇ q118) ◇ (q118 ◇ q118)) ◇ ((q118 ◇ q118) ◇ q118))=((q117 ◇ q118) ◇ (q118 ◇ q118)):=by
    intro q117 q118
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ ((q118 ◇ q118) ◇ q118)) (apc4 q117 q118)).symm).trans (apc95 q118 (q118 ◇ q117))).trans (apc4 q117 q118))
  have apc100 : forall (q119 q82 q83 : G), (((q82 ◇ q83) ◇ (q83 ◇ q119)) ◇ ((q82 ◇ q83) ◇ q119))=((q83 ◇ ((q119 ◇ q83) ◇ q82)) ◇ q83):=by
    intro q119 q82 q83
    exact ((rfl).symm).trans ((((cg (fun t => ((q82 ◇ q83) ◇ (q83 ◇ q119)) ◇ t) ((h q82 q83 q119).symm)).symm).trans (apc29 q82 (q83 ◇ q119) q83)).trans (apc45 q119 q83 q82 q83 q83))
  have apc101 : forall (q120 q121 q122 : G), ((q121 ◇ ((q122 ◇ q121) ◇ q120)) ◇ q121)=((q122 ◇ (q120 ◇ q121)) ◇ (q121 ◇ q122)):=by
    intro q120 q121 q122
    exact ((rfl).symm).trans ((((apc100 q122 q120 q121).symm).trans ((h q122 (q120 ◇ q121) (q121 ◇ q122)).symm)).trans (rfl))
  have apc103 : forall (q120 q121 q122 q65 q66 : G), ((((q66 ◇ q65) ◇ q65) ◇ q65) ◇ q65)=((q65 ◇ (q66 ◇ q65)) ◇ (q65 ◇ q65)):=by
    intro q120 q121 q122 q65 q66
    exact (((rfl).symm).trans ((((apc101 q66 q65 q65).symm).trans ((apc40 q65 q66).trans (rfl))).trans (rfl))).symm
  have apc105 : forall (q123 q124 : G), ((q124 ◇ q124) ◇ ((q124 ◇ q123) ◇ q124))=((q123 ◇ (q124 ◇ q124)) ◇ (q124 ◇ q123)):=by
    intro q123 q124
    exact (((apc49 q123 q124).symm).trans ((((cg (fun t => t ◇ q124) (apc28 q123 q124)).symm).trans (apc103 q123 q123 q123 q124 (q124 ◇ q123))).trans (apc63 ((q124 ◇ ((q124 ◇ q123) ◇ q124)) ◇ (q124 ◇ q124)) ((q124 ◇ ((q124 ◇ q123) ◇ q124)) ◇ (q124 ◇ q124)) ((q124 ◇ ((q124 ◇ q123) ◇ q124)) ◇ (q124 ◇ q124)) ((q124 ◇ ((q124 ◇ q123) ◇ q124)) ◇ (q124 ◇ q124)) ((q124 ◇ ((q124 ◇ q123) ◇ q124)) ◇ (q124 ◇ q124)) q124 q123 q124 q124 q124))).symm
  have apc107 : forall (q125 q126 : G), ((q126 ◇ q126) ◇ ((q125 ◇ q126) ◇ q126))=(((q126 ◇ q126) ◇ (q125 ◇ q126)) ◇ q126):=by
    intro q125 q126
    exact (((apc77 (((q126 ◇ (q125 ◇ q126)) ◇ (q126 ◇ q126)) ◇ q126) (((q126 ◇ (q125 ◇ q126)) ◇ (q126 ◇ q126)) ◇ q126) q125 q126).symm).trans ((((cg (fun t => t ◇ q126) (apc103 q125 q125 q125 q126 q125)).symm).trans (apc103 q125 q125 q125 q126 (q125 ◇ q126))).trans (apc63 ((q126 ◇ ((q125 ◇ q126) ◇ q126)) ◇ (q126 ◇ q126)) ((q126 ◇ ((q125 ◇ q126) ◇ q126)) ◇ (q126 ◇ q126)) ((q126 ◇ ((q125 ◇ q126) ◇ q126)) ◇ (q126 ◇ q126)) ((q126 ◇ ((q125 ◇ q126) ◇ q126)) ◇ (q126 ◇ q126)) ((q126 ◇ ((q125 ◇ q126) ◇ q126)) ◇ (q126 ◇ q126)) q125 q126 q126 q126 q126))).symm
  have apc111 : forall (q127 q128 q129 : G), (((q128 ◇ (q127 ◇ (q128 ◇ q128))) ◇ q128) ◇ q129)=(((q127 ◇ q128) ◇ (q128 ◇ q128)) ◇ q129):=by
    intro q127 q128 q129
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q129) (apc38 q127 q128)).symm).trans (apc70 q128 ((q127 ◇ q128) ◇ q128) q129)).trans (((cg (fun t => t ◇ q129) (apc0 q127 q128 q128 q128)).trans (cg (fun t => t ◇ q129) (apc3 q128 (q128 ◇ q127)))).trans (cg (fun t => t ◇ q129) (apc4 q127 q128))))
  have apc112 : forall (q130 q131 q132 : G), (((q131 ◇ (q130 ◇ q131)) ◇ (q131 ◇ q131)) ◇ q132)=((((q131 ◇ q130) ◇ q131) ◇ (q131 ◇ q131)) ◇ q132):=by
    intro q130 q131 q132
    exact ((cg (fun t => t ◇ q132) (apc101 q130 q131 q131)).symm).trans ((((cg (fun t => t ◇ q132) (cg (fun t => t ◇ q131) (cg (fun t => q131 ◇ t) ((h q131 q131 q130).symm)))).symm).trans (apc111 (q131 ◇ q130) q131 q132)).trans (rfl))
  have apc113 : forall (q133 q134 q135 : G), ((((q134 ◇ q133) ◇ q134) ◇ (q134 ◇ q134)) ◇ q135)=(((q134 ◇ q134) ◇ (q133 ◇ q134)) ◇ q135):=by
    intro q133 q134 q135
    exact (((rfl).symm).trans ((((cg (fun t => t ◇ q135) ((h q134 q134 (q133 ◇ q134)).symm)).symm).trans (apc112 q133 q134 q135)).trans (rfl))).symm
  have apc117 : forall (q136 q137 : G), (((q137 ◇ q137) ◇ q137) ◇ (q136 ◇ q137))=(((q137 ◇ q136) ◇ q137) ◇ (q137 ◇ q137)):=by
    intro q136 q137
    exact (((apc1 q137 q137 q137 (q136 ◇ q137)).trans (apc5 (((q137 ◇ q137) ◇ (q137 ◇ q137)) ◇ (q136 ◇ q137)) (((q137 ◇ q137) ◇ (q137 ◇ q137)) ◇ (q136 ◇ q137)) q137 (q136 ◇ q137))).symm).trans ((((apc113 q136 q137 ((q137 ◇ q137) ◇ q137)).symm).trans (apc98 (q137 ◇ q136) q137)).trans (rfl))
  have apc118 : forall (q138 q139 : G), (((q139 ◇ (q138 ◇ q139)) ◇ q139) ◇ (q139 ◇ q139))=(((q139 ◇ q138) ◇ (q139 ◇ q139)) ◇ q139):=by
    intro q138 q139
    exact ((rfl).symm).trans ((((apc117 (q138 ◇ q139) q139).symm).trans (apc1 q138 q139 q139 q139)).trans (rfl))
  have apc122 : forall (q140 q141 : G), ((((q140 ◇ q140) ◇ (q141 ◇ q141)) ◇ q140) ◇ q141)=((q141 ◇ q141) ◇ ((q140 ◇ q140) ◇ q141)):=by
    intro q140 q141
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q141) (apc33 q141 q140)).symm).trans (apc103 q140 q140 q140 q141 (q140 ◇ q140))).trans (apc63 ((q141 ◇ ((q140 ◇ q140) ◇ q141)) ◇ (q141 ◇ q141)) ((q141 ◇ ((q140 ◇ q140) ◇ q141)) ◇ (q141 ◇ q141)) ((q141 ◇ ((q140 ◇ q140) ◇ q141)) ◇ (q141 ◇ q141)) ((q141 ◇ ((q140 ◇ q140) ◇ q141)) ◇ (q141 ◇ q141)) ((q141 ◇ ((q140 ◇ q140) ◇ q141)) ◇ (q141 ◇ q141)) q140 q140 q141 q141 q141))
  have apc131 : forall (q142 q143 q144 : G), ((q143 ◇ q144) ◇ (q142 ◇ (q142 ◇ q142)))=((q143 ◇ q144) ◇ ((q142 ◇ q142) ◇ q142)):=by
    intro q142 q143 q144
    exact (((apc63 ((q144 ◇ ((q142 ◇ q142) ◇ q142)) ◇ (q144 ◇ q143)) ((q144 ◇ ((q142 ◇ q142) ◇ q142)) ◇ (q144 ◇ q143)) ((q144 ◇ ((q142 ◇ q142) ◇ q142)) ◇ (q144 ◇ q143)) ((q144 ◇ ((q142 ◇ q142) ◇ q142)) ◇ (q144 ◇ q143)) ((q144 ◇ ((q142 ◇ q142) ◇ q142)) ◇ (q144 ◇ q143)) q142 q142 q142 q143 q144).symm).trans ((((apc70 q142 q144 (q144 ◇ q143)).symm).trans ((h q143 q144 (q142 ◇ (q142 ◇ q142))).symm)).trans (rfl))).symm
  have apc133 : forall (q63 q64 q142 q143 q144 : G), ((q64 ◇ (q63 ◇ (q64 ◇ q64))) ◇ q64)=((q63 ◇ q64) ◇ (q64 ◇ q64)):=by
    intro q63 q64 q142 q143 q144
    exact (((((apc0 q63 q64 q64 q64).trans (apc3 q64 (q64 ◇ q63))).trans (apc4 q63 q64)).symm).trans ((((apc131 q64 (q63 ◇ q64) q64).symm).trans ((apc38 q63 q64).trans (rfl))).trans (rfl))).symm
  have apc134 : forall (q145 q146 : G), ((q146 ◇ (q145 ◇ q146)) ◇ (q146 ◇ q146))=(((q146 ◇ q145) ◇ q146) ◇ (q146 ◇ q146)):=by
    intro q145 q146
    exact ((apc101 q145 q146 q146).symm).trans ((((cg (fun t => t ◇ q146) (cg (fun t => q146 ◇ t) ((h q146 q146 q145).symm))).symm).trans (apc133 (q146 ◇ q145) q146 q145 q145 q145)).trans (rfl))
  have apc135 : forall (q147 q148 : G), (((q148 ◇ q147) ◇ q148) ◇ (q148 ◇ q148))=((q148 ◇ q148) ◇ (q147 ◇ q148)):=by
    intro q147 q148
    exact ((rfl).symm).trans ((((apc134 q147 q148).symm).trans ((h q148 q148 (q147 ◇ q148)).symm)).trans (rfl))
  have apc137 : forall (q145 q146 q120 q121 q122 q65 q66 : G), ((((q66 ◇ q65) ◇ q65) ◇ q65) ◇ q65)=((q65 ◇ q65) ◇ (q66 ◇ q65)):=by
    intro q145 q146 q120 q121 q122 q65 q66
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc103 q65 q65 q65 q65 q66).trans (apc134 q66 q65))).trans (apc135 q66 q65))
  have apc138 : forall (q138 q139 q147 q148 : G), (((q139 ◇ q139) ◇ (q138 ◇ q139)) ◇ q139)=(((q139 ◇ q138) ◇ (q139 ◇ q139)) ◇ q139):=by
    intro q138 q139 q147 q148
    exact ((apc107 q138 q139).symm).trans ((((apc135 (q138 ◇ q139) q139).symm).trans ((apc118 q138 q139).trans (rfl))).trans (rfl))
  have apc140 : forall (q113 q114 q138 q139 q147 q148 : G), ((((q114 ◇ q114) ◇ q113) ◇ q114) ◇ q114)=(((q114 ◇ q113) ◇ (q114 ◇ q114)) ◇ q114):=by
    intro q113 q114 q138 q139 q147 q148
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc74 q113 q114).trans (apc138 q113 q114 (((q114 ◇ q114) ◇ (q113 ◇ q114)) ◇ q114) (((q114 ◇ q114) ◇ (q113 ◇ q114)) ◇ q114)))).trans (rfl))
  have apc143 : forall (q145 q146 q147 q148 : G), ((q146 ◇ (q145 ◇ q146)) ◇ (q146 ◇ q146))=((q146 ◇ q146) ◇ (q145 ◇ q146)):=by
    intro q145 q146 q147 q148
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc134 q145 q146).trans (apc135 q145 q146))).trans (rfl))
  have apc145 : forall (q149 q150 : G), (((q149 ◇ q150) ◇ q150) ◇ q150)=((q150 ◇ q150) ◇ (q149 ◇ q150)):=by
    intro q149 q150
    exact (((apc137 ((((q149 ◇ q150) ◇ q150) ◇ q150) ◇ q150) ((((q149 ◇ q150) ◇ q150) ◇ q150) ◇ q150) ((((q149 ◇ q150) ◇ q150) ◇ q150) ◇ q150) ((((q149 ◇ q150) ◇ q150) ◇ q150) ◇ q150) ((((q149 ◇ q150) ◇ q150) ◇ q150) ◇ q150) q150 q149).symm).trans ((((cg (fun t => t ◇ q150) (cg (fun t => t ◇ q150) ((h q149 q150 q150).symm))).symm).trans (apc140 (q150 ◇ q149) q150 q149 q149 q149 q149)).trans (apc15 q149 q150 (((q150 ◇ (q150 ◇ q149)) ◇ (q150 ◇ q150)) ◇ q150) (((q150 ◇ (q150 ◇ q149)) ◇ (q150 ◇ q150)) ◇ q150)))).symm
  have apc147 : forall (q145 q146 q149 q150 q120 q121 q122 q65 q66 : G), (((q65 ◇ q65) ◇ (q66 ◇ q65)) ◇ q65)=((q65 ◇ q65) ◇ (q66 ◇ q65)):=by
    intro q145 q146 q149 q150 q120 q121 q122 q65 q66
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q65) (apc145 q66 q65)).symm).trans ((apc137 q65 q65 q65 q65 q65 q65 q66).trans (rfl))).trans (rfl))
  have apc148 : forall (q145 q146 q149 q150 q120 q121 q122 q138 q139 q147 q148 q65 q66 : G), (((q139 ◇ q138) ◇ (q139 ◇ q139)) ◇ q139)=((q139 ◇ q139) ◇ (q138 ◇ q139)):=by
    intro q145 q146 q149 q150 q120 q121 q122 q138 q139 q147 q148 q65 q66
    exact (((rfl).symm).trans ((((apc147 (((q139 ◇ q139) ◇ (q138 ◇ q139)) ◇ q139) (((q139 ◇ q139) ◇ (q138 ◇ q139)) ◇ q139) (((q139 ◇ q139) ◇ (q138 ◇ q139)) ◇ q139) (((q139 ◇ q139) ◇ (q138 ◇ q139)) ◇ q139) (((q139 ◇ q139) ◇ (q138 ◇ q139)) ◇ q139) (((q139 ◇ q139) ◇ (q138 ◇ q139)) ◇ q139) (((q139 ◇ q139) ◇ (q138 ◇ q139)) ◇ q139) q139 q138).symm).trans ((apc138 q138 q139 q138 q138).trans (rfl))).trans (rfl))).symm
  have apc149 : forall (q151 q152 : G), (((q152 ◇ q152) ◇ q151) ◇ q152)=((q152 ◇ q152) ◇ (q151 ◇ q152)):=by
    intro q151 q152
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q152) ((h q152 q152 q151).symm)).symm).trans (apc148 q151 q151 q151 q151 q151 q151 q151 q151 q152 q151 q151 q151 q151)).trans (rfl))
  have apc150 : forall (q153 q154 : G), ((q153 ◇ (q154 ◇ q154)) ◇ (q154 ◇ q153))=((q154 ◇ q154) ◇ (q153 ◇ q154)):=by
    intro q153 q154
    exact (((apc145 q153 q154).symm).trans ((((cg (fun t => t ◇ q154) ((h q153 q154 q154).symm)).symm).trans (apc149 (q154 ◇ q153) q154)).trans (apc105 q153 q154))).symm
  have apc151 : forall (q19 q20 q145 q146 q149 q150 q120 q121 q122 q138 q139 q147 q148 q65 q66 : G), (((q20 ◇ q20) ◇ q19) ◇ (q20 ◇ q20))=((q20 ◇ q20) ◇ (q19 ◇ q20)):=by
    intro q19 q20 q145 q146 q149 q150 q120 q121 q122 q138 q139 q147 q148 q65 q66
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc10 q19 q20).trans (apc148 (((q20 ◇ q19) ◇ (q20 ◇ q20)) ◇ q20) (((q20 ◇ q19) ◇ (q20 ◇ q20)) ◇ q20) (((q20 ◇ q19) ◇ (q20 ◇ q20)) ◇ q20) (((q20 ◇ q19) ◇ (q20 ◇ q20)) ◇ q20) (((q20 ◇ q19) ◇ (q20 ◇ q20)) ◇ q20) (((q20 ◇ q19) ◇ (q20 ◇ q20)) ◇ q20) (((q20 ◇ q19) ◇ (q20 ◇ q20)) ◇ q20) q19 q20 (((q20 ◇ q19) ◇ (q20 ◇ q20)) ◇ q20) (((q20 ◇ q19) ◇ (q20 ◇ q20)) ◇ q20) (((q20 ◇ q19) ◇ (q20 ◇ q20)) ◇ q20) (((q20 ◇ q19) ◇ (q20 ◇ q20)) ◇ q20)))).trans (rfl))
  have apc152 : forall (q153 q154 q84 q85 : G), (((q85 ◇ (q84 ◇ q85)) ◇ q85) ◇ q85)=((q85 ◇ q85) ◇ (q84 ◇ q85)):=by
    intro q153 q154 q84 q85
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc49 q84 q85).trans (apc150 q84 q85))).trans (rfl))
  have apc153 : forall (q149 q150 q61 q62 : G), ((q61 ◇ q61) ◇ ((q62 ◇ q62) ◇ q61))=(((q62 ◇ q62) ◇ (q61 ◇ q61)) ◇ q62):=by
    intro q149 q150 q61 q62
    exact ((rfl).symm).trans ((((apc145 (q62 ◇ q62) q61).symm).trans ((apc33 q61 q62).trans (rfl))).trans (rfl))
  have apc154 : forall (q25 q26 q149 q150 q50 q51 q52 : G), ((q25 ◇ (q26 ◇ q26)) ◇ q25)=((q26 ◇ q26) ◇ (q25 ◇ q26)):=by
    intro q25 q26 q149 q150 q50 q51 q52
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc26 q25 q26 q25 q25 q25).trans (apc145 q25 q26))).trans (rfl))
  have apc155 : forall (q155 q156 : G), ((q156 ◇ q156) ◇ ((q156 ◇ q155) ◇ q156))=((q156 ◇ (q155 ◇ q156)) ◇ q156):=by
    intro q155 q156
    exact (((apc25 q155 q156 q156).symm).trans ((((cg (fun t => t ◇ (q156 ◇ q155)) ((h q156 q156 q155).symm)).symm).trans (apc154 (q156 ◇ q155) q156 q155 q155 q155 q155 q155)).trans (rfl))).symm
  have apc156 : forall (q157 q158 : G), ((q158 ◇ (q157 ◇ q158)) ◇ q158)=((q158 ◇ q158) ◇ (q157 ◇ q158)):=by
    intro q157 q158
    exact (((apc152 (((q158 ◇ (q157 ◇ q158)) ◇ q158) ◇ q158) (((q158 ◇ (q157 ◇ q158)) ◇ q158) ◇ q158) q157 q158).symm).trans ((((cg (fun t => t ◇ q158) (apc155 q157 q158)).symm).trans (apc147 q157 q157 q157 q157 q157 q157 q157 q158 (q158 ◇ q157))).trans (apc155 q157 q158))).symm
  have apc157 : forall (q151 q152 q99 q100 : G), ((q100 ◇ (q100 ◇ (q99 ◇ q99))) ◇ q100)=(((q99 ◇ q99) ◇ (q100 ◇ q99)) ◇ q100):=by
    intro q151 q152 q99 q100
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc66 q99 q100).trans (cg (fun t => t ◇ q100) (apc149 q100 q99)))).trans (rfl))
  have apc158 : forall (q145 q146 q149 q150 q61 q62 q120 q121 q122 q138 q139 q147 q148 q59 q60 q65 q66 : G), (((q60 ◇ q60) ◇ (q59 ◇ q59)) ◇ q60)=(((q59 ◇ q59) ◇ (q60 ◇ q60)) ◇ q59):=by
    intro q145 q146 q149 q150 q61 q62 q120 q121 q122 q138 q139 q147 q148 q59 q60 q65 q66
    exact (((apc153 ((q60 ◇ q60) ◇ ((q59 ◇ q59) ◇ q60)) ((q60 ◇ q60) ◇ ((q59 ◇ q59) ◇ q60)) q60 q59).symm).trans ((((apc148 (((q60 ◇ (q59 ◇ q59)) ◇ (q60 ◇ q60)) ◇ q60) (((q60 ◇ (q59 ◇ q59)) ◇ (q60 ◇ q60)) ◇ q60) (((q60 ◇ (q59 ◇ q59)) ◇ (q60 ◇ q60)) ◇ q60) (((q60 ◇ (q59 ◇ q59)) ◇ (q60 ◇ q60)) ◇ q60) (((q60 ◇ (q59 ◇ q59)) ◇ (q60 ◇ q60)) ◇ q60) (((q60 ◇ (q59 ◇ q59)) ◇ (q60 ◇ q60)) ◇ q60) (((q60 ◇ (q59 ◇ q59)) ◇ (q60 ◇ q60)) ◇ q60) (q59 ◇ q59) q60 (((q60 ◇ (q59 ◇ q59)) ◇ (q60 ◇ q60)) ◇ q60) (((q60 ◇ (q59 ◇ q59)) ◇ (q60 ◇ q60)) ◇ q60) (((q60 ◇ (q59 ◇ q59)) ◇ (q60 ◇ q60)) ◇ q60) (((q60 ◇ (q59 ◇ q59)) ◇ (q60 ◇ q60)) ◇ q60)).symm).trans ((apc35 q59 q59 q59 q60).trans (rfl))).trans (rfl))).symm
  have apc165 : forall (q149 q150 q61 q62 q140 q141 : G), ((((q140 ◇ q140) ◇ (q141 ◇ q141)) ◇ q140) ◇ q141)=(((q140 ◇ q140) ◇ (q141 ◇ q141)) ◇ q140):=by
    intro q149 q150 q61 q62 q140 q141
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc122 q140 q141).trans (apc153 ((q141 ◇ q141) ◇ ((q140 ◇ q140) ◇ q141)) ((q141 ◇ q141) ◇ ((q140 ◇ q140) ◇ q141)) q141 q140))).trans (rfl))
  have apc170 : forall (q151 q152 q40 q41 : G), ((q41 ◇ (q40 ◇ q40)) ◇ ((q40 ◇ q40) ◇ q41))=(((q40 ◇ q40) ◇ (q41 ◇ q40)) ◇ q41):=by
    intro q151 q152 q40 q41
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc22 q40 q41).trans (cg (fun t => t ◇ q41) (apc149 q41 q40)))).trans (rfl))
  have apc171 : forall (q159 q160 : G), (((q160 ◇ (q159 ◇ q159)) ◇ q159) ◇ q159)=((q160 ◇ q159) ◇ (q159 ◇ q159)):=by
    intro q159 q160
    exact (((apc98 q160 q159).symm).trans ((((apc131 q159 (q160 ◇ q159) (q159 ◇ q159)).symm).trans (apc25 (q159 ◇ q159) q159 q160)).trans (apc59 q159 q160))).symm
  have apc172 : forall (q74 q75 q159 q160 : G), (((q74 ◇ (q75 ◇ q75)) ◇ q75) ◇ (q75 ◇ q75))=((q74 ◇ q75) ◇ (q75 ◇ q75)):=by
    intro q74 q75 q159 q160
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc43 q74 q75).trans (apc171 q75 q74))).trans (rfl))
  have apc174 : forall (q161 q162 : G), ((q162 ◇ q162) ◇ ((q161 ◇ (q162 ◇ q162)) ◇ q162))=(((q161 ◇ q162) ◇ (q162 ◇ q162)) ◇ q162):=by
    intro q161 q162
    exact (((rfl).symm).trans ((((cg (fun t => t ◇ q162) (apc171 q162 q161)).symm).trans (apc145 (q161 ◇ (q162 ◇ q162)) q162)).trans (rfl))).symm
  have apc177 : forall (q163 q164 : G), (((q163 ◇ q164) ◇ (q164 ◇ q164)) ◇ q164)=((q163 ◇ q164) ◇ (q164 ◇ q164)):=by
    intro q163 q164
    exact (((apc156 (q163 ◇ (q164 ◇ q164)) q164).trans (apc174 q163 q164)).symm).trans ((((cg (fun t => t ◇ q164) (cg (fun t => q164 ◇ t) (apc9 q164 q163))).symm).trans (apc133 (q163 ◇ (q164 ◇ q164)) q164 q163 q163 q163)).trans (apc172 q163 q164 (((q163 ◇ (q164 ◇ q164)) ◇ q164) ◇ (q164 ◇ q164)) (((q163 ◇ (q164 ◇ q164)) ◇ q164) ◇ (q164 ◇ q164))))
  have apc178 : forall (q165 q166 : G), ((q166 ◇ q166) ◇ (q165 ◇ q166))=((q165 ◇ q166) ◇ (q166 ◇ q166)):=by
    intro q165 q166
    exact (((apc177 q165 q166).symm).trans ((((cg (fun t => t ◇ q166) (apc177 q165 q166)).symm).trans (apc171 q166 (q165 ◇ q166))).trans ((apc25 q166 q166 q165).trans (apc154 q165 q166 ((q165 ◇ (q166 ◇ q166)) ◇ q165) ((q165 ◇ (q166 ◇ q166)) ◇ q165) ((q165 ◇ (q166 ◇ q166)) ◇ q165) ((q165 ◇ (q166 ◇ q166)) ◇ q165) ((q165 ◇ (q166 ◇ q166)) ◇ q165))))).symm
  have apc180 : forall (q151 q152 q165 q166 : G), (((q152 ◇ q152) ◇ q151) ◇ q152)=((q151 ◇ q152) ◇ (q152 ◇ q152)):=by
    intro q151 q152 q165 q166
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc149 q151 q152).trans (apc178 q151 q152))).trans (rfl))
  have apc182 : forall (q147 q148 q165 q166 : G), (((q148 ◇ q147) ◇ q148) ◇ (q148 ◇ q148))=((q147 ◇ q148) ◇ (q148 ◇ q148)):=by
    intro q147 q148 q165 q166
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc135 q147 q148).trans (apc178 q147 q148))).trans (rfl))
  have apc185 : forall (q19 q20 q145 q146 q149 q150 q120 q121 q122 q138 q139 q147 q148 q165 q166 q65 q66 : G), (((q20 ◇ q20) ◇ q19) ◇ (q20 ◇ q20))=((q19 ◇ q20) ◇ (q20 ◇ q20)):=by
    intro q19 q20 q145 q146 q149 q150 q120 q121 q122 q138 q139 q147 q148 q165 q166 q65 q66
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc151 q19 q20 q19 q19 q19 q19 q19 q19 q19 q19 q19 q19 q19 q19 q19).trans (apc178 q19 q20))).trans (rfl))
  have apc186 : forall (q25 q26 q149 q150 q165 q166 q50 q51 q52 : G), ((q25 ◇ (q26 ◇ q26)) ◇ q25)=((q25 ◇ q26) ◇ (q26 ◇ q26)):=by
    intro q25 q26 q149 q150 q165 q166 q50 q51 q52
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc154 q25 q26 q25 q25 q25 q25 q25).trans (apc178 q25 q26))).trans (rfl))
  have apc188 : forall (q157 q158 q165 q166 : G), ((q158 ◇ (q157 ◇ q158)) ◇ q158)=((q157 ◇ q158) ◇ (q158 ◇ q158)):=by
    intro q157 q158 q165 q166
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc156 q157 q158).trans (apc178 q157 q158))).trans (rfl))
  have apc189 : forall (q167 q168 : G), ((q168 ◇ (q167 ◇ q167)) ◇ (q167 ◇ q168))=((q168 ◇ q167) ◇ (q167 ◇ q167)):=by
    intro q167 q168
    exact ((((apc25 q167 q167 q168).trans (apc186 q168 q167 ((q168 ◇ (q167 ◇ q167)) ◇ q168) ((q168 ◇ (q167 ◇ q167)) ◇ q168) ((q168 ◇ (q167 ◇ q167)) ◇ q168) ((q168 ◇ (q167 ◇ q167)) ◇ q168) ((q168 ◇ (q167 ◇ q167)) ◇ q168) ((q168 ◇ (q167 ◇ q167)) ◇ q168) ((q168 ◇ (q167 ◇ q167)) ◇ q168))).symm).trans ((((apc188 (q168 ◇ q167) q167 q167 q167).symm).trans (apc101 q167 q167 q168)).trans (rfl))).symm
  have apc191 : forall (q145 q146 q149 q150 q151 q152 q61 q62 q120 q121 q122 q138 q139 q147 q148 q165 q166 q59 q60 q65 q66 : G), (((q59 ◇ q59) ◇ q60) ◇ (q60 ◇ q60))=(((q59 ◇ q59) ◇ (q60 ◇ q60)) ◇ q59):=by
    intro q145 q146 q149 q150 q151 q152 q61 q62 q120 q121 q122 q138 q139 q147 q148 q165 q166 q59 q60 q65 q66
    exact ((rfl).symm).trans ((((apc180 (q59 ◇ q59) q60 (((q60 ◇ q60) ◇ (q59 ◇ q59)) ◇ q60) (((q60 ◇ q60) ◇ (q59 ◇ q59)) ◇ q60)).symm).trans ((apc158 q59 q59 q59 q59 q59 q59 q59 q59 q59 q59 q59 q59 q59 q59 q60 q59 q59).trans (rfl))).trans (rfl))
  have apc193 : forall (q145 q146 q147 q148 q165 q166 : G), ((q146 ◇ (q145 ◇ q146)) ◇ (q146 ◇ q146))=((q145 ◇ q146) ◇ (q146 ◇ q146)):=by
    intro q145 q146 q147 q148 q165 q166
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc143 q145 q146 q145 q145).trans (apc178 q145 q146))).trans (rfl))
  have apc196 : forall (q169 q170 : G), (((q170 ◇ q169) ◇ (q169 ◇ q169)) ◇ q170)=(((q169 ◇ q169) ◇ (q170 ◇ q169)) ◇ q170):=by
    intro q169 q170
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q170) (apc185 q170 q169 q169 q169 q169 q169 q169 q169 q169 q169 q169 q169 q169 q169 q169 q169 q169)).symm).trans (apc8 q170 (q169 ◇ q169))).trans (apc170 ((q170 ◇ (q169 ◇ q169)) ◇ ((q169 ◇ q169) ◇ q170)) ((q170 ◇ (q169 ◇ q169)) ◇ ((q169 ◇ q169) ◇ q170)) q169 q170))
  have apc217 : forall (q171 q172 q173 : G), (((q171 ◇ q172) ◇ (q172 ◇ q172)) ◇ ((q172 ◇ q172) ◇ q173))=((q173 ◇ (q172 ◇ q172)) ◇ (q171 ◇ q172)):=by
    intro q171 q172 q173
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ ((q172 ◇ q172) ◇ q173)) (apc178 q171 q172)).symm).trans ((h q173 (q172 ◇ q172) (q171 ◇ q172)).symm)).trans (rfl))
  have apc218 : forall (q174 q175 : G), (((q175 ◇ q174) ◇ (q175 ◇ q175)) ◇ (q174 ◇ q175))=((q174 ◇ q175) ◇ (q175 ◇ q175)):=by
    intro q174 q175
    exact ((rfl).symm).trans ((((apc217 q174 q175 (q175 ◇ q174)).symm).trans (apc29 q174 (q175 ◇ q175) q175)).trans (((apc45 q175 q175 q174 q175 q175).trans (apc101 q174 q175 q175)).trans (apc193 q174 q175 ((q175 ◇ (q174 ◇ q175)) ◇ (q175 ◇ q175)) ((q175 ◇ (q174 ◇ q175)) ◇ (q175 ◇ q175)) ((q175 ◇ (q174 ◇ q175)) ◇ (q175 ◇ q175)) ((q175 ◇ (q174 ◇ q175)) ◇ (q175 ◇ q175)))))
  have apc219 : forall (q176 q177 : G), (((q177 ◇ q177) ◇ q176) ◇ (q176 ◇ q177))=((q176 ◇ q177) ◇ (q177 ◇ q177)):=by
    intro q176 q177
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (q176 ◇ q177)) ((h q177 q177 q176).symm)).symm).trans (apc218 q176 q177)).trans (rfl))
  have apc220 : forall (q178 q179 : G), (((q178 ◇ q179) ◇ (q178 ◇ q179)) ◇ q179)=((q178 ◇ q179) ◇ (q179 ◇ q179)):=by
    intro q178 q179
    exact ((apc1 q179 q178 q179 q179).symm).trans ((((cg (fun t => t ◇ ((q179 ◇ q178) ◇ q179)) ((h q178 q179 q179).symm)).symm).trans (apc219 (q179 ◇ q178) q179)).trans (apc182 q178 q179 (((q179 ◇ q178) ◇ q179) ◇ (q179 ◇ q179)) (((q179 ◇ q178) ◇ q179) ◇ (q179 ◇ q179))))
  have apc221 : forall (q180 q181 : G), (((q181 ◇ q180) ◇ q181) ◇ q181)=((q180 ◇ q181) ◇ (q181 ◇ q181)):=by
    intro q180 q181
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q181) ((h q181 q180 q181).symm)).symm).trans (apc220 q180 q181)).trans (rfl))
  have apc222 : forall (q182 q183 : G), (((q182 ◇ q182) ◇ (q183 ◇ q183)) ◇ q182)=(((q182 ◇ q182) ◇ (q183 ◇ q182)) ◇ q183):=by
    intro q182 q183
    exact (((apc196 q182 q183).symm).trans ((((cg (fun t => t ◇ q183) (apc186 q183 q182 q182 q182 q182 q182 q182 q182 q182)).symm).trans (apc221 (q182 ◇ q182) q183)).trans (apc191 (((q182 ◇ q182) ◇ q183) ◇ (q183 ◇ q183)) (((q182 ◇ q182) ◇ q183) ◇ (q183 ◇ q183)) (((q182 ◇ q182) ◇ q183) ◇ (q183 ◇ q183)) (((q182 ◇ q182) ◇ q183) ◇ (q183 ◇ q183)) (((q182 ◇ q182) ◇ q183) ◇ (q183 ◇ q183)) (((q182 ◇ q182) ◇ q183) ◇ (q183 ◇ q183)) (((q182 ◇ q182) ◇ q183) ◇ (q183 ◇ q183)) (((q182 ◇ q182) ◇ q183) ◇ (q183 ◇ q183)) (((q182 ◇ q182) ◇ q183) ◇ (q183 ◇ q183)) (((q182 ◇ q182) ◇ q183) ◇ (q183 ◇ q183)) (((q182 ◇ q182) ◇ q183) ◇ (q183 ◇ q183)) (((q182 ◇ q182) ◇ q183) ◇ (q183 ◇ q183)) (((q182 ◇ q182) ◇ q183) ◇ (q183 ◇ q183)) (((q182 ◇ q182) ◇ q183) ◇ (q183 ◇ q183)) (((q182 ◇ q182) ◇ q183) ◇ (q183 ◇ q183)) (((q182 ◇ q182) ◇ q183) ◇ (q183 ◇ q183)) (((q182 ◇ q182) ◇ q183) ◇ (q183 ◇ q183)) q182 q183 (((q182 ◇ q182) ◇ q183) ◇ (q183 ◇ q183)) (((q182 ◇ q182) ◇ q183) ◇ (q183 ◇ q183))))).symm
  have apc224 : forall (q145 q146 q149 q150 q151 q152 q61 q62 q120 q121 q122 q138 q139 q147 q148 q165 q166 q182 q183 q59 q60 q65 q66 : G), (((q59 ◇ q59) ◇ q60) ◇ (q60 ◇ q60))=(((q59 ◇ q59) ◇ (q60 ◇ q59)) ◇ q60):=by
    intro q145 q146 q149 q150 q151 q152 q61 q62 q120 q121 q122 q138 q139 q147 q148 q165 q166 q182 q183 q59 q60 q65 q66
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc191 q59 q59 q59 q59 q59 q59 q59 q59 q59 q59 q59 q59 q59 q59 q59 q59 q59 q59 q60 q59 q59).trans (apc222 q59 q60))).trans (rfl))
  have apc227 : forall (q149 q150 q61 q62 q182 q183 q140 q141 : G), ((((q140 ◇ q140) ◇ (q141 ◇ q140)) ◇ q141) ◇ q141)=(((q140 ◇ q140) ◇ (q141 ◇ q140)) ◇ q141):=by
    intro q149 q150 q61 q62 q182 q183 q140 q141
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q141) (apc222 q140 q141)).symm).trans ((apc165 q140 q140 q140 q140 q140 q141).trans (apc222 q140 q141))).trans (rfl))
  have apc234 : forall (q184 q185 : G), ((q185 ◇ (q184 ◇ q184)) ◇ (q185 ◇ q184))=(((q184 ◇ q184) ◇ (q185 ◇ q184)) ◇ q185):=by
    intro q184 q185
    exact ((apc217 q185 q184 q185).symm).trans ((((cg (fun t => t ◇ ((q184 ◇ q184) ◇ q185)) (apc186 q185 q184 q184 q184 q184 q184 q184 q184 q184)).symm).trans (apc25 q185 (q184 ◇ q184) q185)).trans (apc157 ((q185 ◇ (q185 ◇ (q184 ◇ q184))) ◇ q185) ((q185 ◇ (q185 ◇ (q184 ◇ q184))) ◇ q185) q184 q185))
  have apc235 : forall (q186 q187 : G), (((q186 ◇ q186) ◇ (q187 ◇ q186)) ◇ q187)=((q186 ◇ q187) ◇ (q186 ◇ q186)):=by
    intro q186 q187
    exact ((rfl).symm).trans ((((apc234 q186 q187).symm).trans ((h q186 q187 (q186 ◇ q186)).symm)).trans (rfl))
  have apc236 : forall (q149 q150 q61 q62 q182 q183 q186 q187 q140 q141 : G), (((q140 ◇ q141) ◇ (q140 ◇ q140)) ◇ q141)=((q140 ◇ q141) ◇ (q140 ◇ q140)):=by
    intro q149 q150 q61 q62 q182 q183 q186 q187 q140 q141
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q141) (apc235 q140 q141)).symm).trans ((apc227 q140 q140 q140 q140 q140 q140 q140 q141).trans (apc235 q140 q141))).trans (rfl))
  have apc239 : forall (q93 q188 q189 q190 q96 : G), ((((q188 ◇ q93) ◇ q190) ◇ q96) ◇ (((q93 ◇ q188) ◇ q189) ◇ q190))=(((q190 ◇ (q188 ◇ q93)) ◇ (q188 ◇ q189)) ◇ q96):=by
    intro q93 q188 q189 q190 q96
    exact ((rfl).symm).trans ((((cg (fun t => (((q188 ◇ q93) ◇ q190) ◇ q96) ◇ t) (cg (fun t => t ◇ q190) ((h q93 q188 q189).symm))).symm).trans (apc1 (q188 ◇ q189) (q188 ◇ q93) q190 q96)).trans ((apc19 q189 q188 q93 ((q188 ◇ q93) ◇ q190) q96).trans (cg (fun t => t ◇ q96) (apc0 q189 q188 q93 q190))))
  have apc240 : forall (q182 q183 q186 q187 : G), (((q182 ◇ q182) ◇ (q183 ◇ q183)) ◇ q182)=((q182 ◇ q183) ◇ (q182 ◇ q182)):=by
    intro q182 q183 q186 q187
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc222 q182 q183).trans (apc235 q182 q183))).trans (rfl))
  have apc241 : forall (q191 q192 : G), (((q191 ◇ q191) ◇ q192) ◇ (q192 ◇ q192))=((q192 ◇ q191) ◇ (q192 ◇ q192)):=by
    intro q191 q192
    exact (((rfl).symm).trans ((((apc240 q192 q191 q191 q191).symm).trans (apc180 (q191 ◇ q191) q192 q191 q191)).trans (rfl))).symm
  have apc245 : forall (q145 q146 q149 q150 q151 q152 q61 q62 q120 q121 q122 q138 q139 q147 q148 q165 q166 q182 q183 q186 q187 q59 q60 q65 q66 : G), ((q60 ◇ q59) ◇ (q60 ◇ q60))=((q59 ◇ q60) ◇ (q59 ◇ q59)):=by
    intro q145 q146 q149 q150 q151 q152 q61 q62 q120 q121 q122 q138 q139 q147 q148 q165 q166 q182 q183 q186 q187 q59 q60 q65 q66
    exact ((apc241 q59 q60).symm).trans ((((rfl).symm).trans ((apc224 q59 q59 q59 q59 q59 q59 q59 q59 q59 q59 q59 q59 q59 q59 q59 q59 q59 q59 q59 q59 q60 q59 q59).trans (apc235 q59 q60))).trans (rfl))
  have apc246 : forall (q193 q194 : G), ((q193 ◇ q194) ◇ (q193 ◇ q193))=((q193 ◇ q193) ◇ q194):=by
    intro q193 q194
    exact ((apc245 ((q194 ◇ q193) ◇ (q194 ◇ q194)) ((q194 ◇ q193) ◇ (q194 ◇ q194)) ((q194 ◇ q193) ◇ (q194 ◇ q194)) ((q194 ◇ q193) ◇ (q194 ◇ q194)) ((q194 ◇ q193) ◇ (q194 ◇ q194)) ((q194 ◇ q193) ◇ (q194 ◇ q194)) ((q194 ◇ q193) ◇ (q194 ◇ q194)) ((q194 ◇ q193) ◇ (q194 ◇ q194)) ((q194 ◇ q193) ◇ (q194 ◇ q194)) ((q194 ◇ q193) ◇ (q194 ◇ q194)) ((q194 ◇ q193) ◇ (q194 ◇ q194)) ((q194 ◇ q193) ◇ (q194 ◇ q194)) ((q194 ◇ q193) ◇ (q194 ◇ q194)) ((q194 ◇ q193) ◇ (q194 ◇ q194)) ((q194 ◇ q193) ◇ (q194 ◇ q194)) ((q194 ◇ q193) ◇ (q194 ◇ q194)) ((q194 ◇ q193) ◇ (q194 ◇ q194)) ((q194 ◇ q193) ◇ (q194 ◇ q194)) ((q194 ◇ q193) ◇ (q194 ◇ q194)) ((q194 ◇ q193) ◇ (q194 ◇ q194)) ((q194 ◇ q193) ◇ (q194 ◇ q194)) q193 q194 ((q194 ◇ q193) ◇ (q194 ◇ q194)) ((q194 ◇ q193) ◇ (q194 ◇ q194))).symm).trans ((((apc245 q193 q193 q193 q193 q193 q193 q193 q193 q193 q193 q193 q193 q193 q193 q193 q193 q193 q193 q193 q193 q193 q194 q193 q193 q193).symm).trans ((h q193 q193 q194).symm)).trans (rfl))
  have apc247 : forall (q149 q150 q61 q62 q182 q183 q186 q187 q193 q194 q140 q141 : G), (((q140 ◇ q140) ◇ q141) ◇ q141)=((q140 ◇ q140) ◇ q141):=by
    intro q149 q150 q61 q62 q182 q183 q186 q187 q193 q194 q140 q141
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q141) (apc246 q140 q141)).symm).trans ((apc236 q140 q140 q140 q140 q140 q140 q140 q140 q140 q141).trans (apc246 q140 q141))).trans (rfl))
  have apc248 : forall (q145 q146 q149 q150 q151 q152 q61 q62 q120 q121 q122 q138 q139 q147 q148 q165 q166 q182 q183 q186 q187 q193 q194 q59 q60 q65 q66 : G), ((q60 ◇ q60) ◇ q59)=((q59 ◇ q59) ◇ q60):=by
    intro q145 q146 q149 q150 q151 q152 q61 q62 q120 q121 q122 q138 q139 q147 q148 q165 q166 q182 q183 q186 q187 q193 q194 q59 q60 q65 q66
    exact ((rfl).symm).trans ((((apc246 q60 q59).symm).trans ((apc245 q59 q59 q59 q59 q59 q59 q59 q59 q59 q59 q59 q59 q59 q59 q59 q59 q59 q59 q59 q59 q59 q59 q60 q59 q59).trans (apc246 q59 q60))).trans (rfl))
  have apc249 : forall (q195 q196 : G), ((q196 ◇ q196) ◇ (q196 ◇ q195))=((q195 ◇ q196) ◇ q196):=by
    intro q195 q196
    exact ((apc248 (((q196 ◇ q195) ◇ (q196 ◇ q195)) ◇ q196) (((q196 ◇ q195) ◇ (q196 ◇ q195)) ◇ q196) (((q196 ◇ q195) ◇ (q196 ◇ q195)) ◇ q196) (((q196 ◇ q195) ◇ (q196 ◇ q195)) ◇ q196) (((q196 ◇ q195) ◇ (q196 ◇ q195)) ◇ q196) (((q196 ◇ q195) ◇ (q196 ◇ q195)) ◇ q196) (((q196 ◇ q195) ◇ (q196 ◇ q195)) ◇ q196) (((q196 ◇ q195) ◇ (q196 ◇ q195)) ◇ q196) (((q196 ◇ q195) ◇ (q196 ◇ q195)) ◇ q196) (((q196 ◇ q195) ◇ (q196 ◇ q195)) ◇ q196) (((q196 ◇ q195) ◇ (q196 ◇ q195)) ◇ q196) (((q196 ◇ q195) ◇ (q196 ◇ q195)) ◇ q196) (((q196 ◇ q195) ◇ (q196 ◇ q195)) ◇ q196) (((q196 ◇ q195) ◇ (q196 ◇ q195)) ◇ q196) (((q196 ◇ q195) ◇ (q196 ◇ q195)) ◇ q196) (((q196 ◇ q195) ◇ (q196 ◇ q195)) ◇ q196) (((q196 ◇ q195) ◇ (q196 ◇ q195)) ◇ q196) (((q196 ◇ q195) ◇ (q196 ◇ q195)) ◇ q196) (((q196 ◇ q195) ◇ (q196 ◇ q195)) ◇ q196) (((q196 ◇ q195) ◇ (q196 ◇ q195)) ◇ q196) (((q196 ◇ q195) ◇ (q196 ◇ q195)) ◇ q196) (((q196 ◇ q195) ◇ (q196 ◇ q195)) ◇ q196) (((q196 ◇ q195) ◇ (q196 ◇ q195)) ◇ q196) q196 (q196 ◇ q195) (((q196 ◇ q195) ◇ (q196 ◇ q195)) ◇ q196) (((q196 ◇ q195) ◇ (q196 ◇ q195)) ◇ q196)).symm).trans ((((apc248 q195 q195 q195 q195 q195 q195 q195 q195 q195 q195 q195 q195 q195 q195 q195 q195 q195 q195 q195 q195 q195 q195 q195 (q196 ◇ q195) q196 q195 q195).symm).trans ((h q195 q196 q196).symm)).trans (rfl))
  have apc250 : forall (q197 q198 q199 : G), (((q198 ◇ q197) ◇ q198) ◇ q199)=((q199 ◇ q199) ◇ (q197 ◇ q198)):=by
    intro q197 q198 q199
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q199) ((h q198 q197 q198).symm)).symm).trans (apc248 q197 q197 q197 q197 q197 q197 q197 q197 q197 q197 q197 q197 q197 q197 q197 q197 q197 q197 q197 q197 q197 q197 q197 q199 (q197 ◇ q198) q197 q197)).trans (rfl))
  have apc253 : forall (q182 q183 q186 q187 q193 q194 : G), (((q182 ◇ q182) ◇ (q183 ◇ q183)) ◇ q182)=((q182 ◇ q182) ◇ q183):=by
    intro q182 q183 q186 q187 q193 q194
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc240 q182 q183 q182 q182).trans (apc246 q182 q183))).trans (rfl))
  have apc257 : forall (q145 q146 q149 q150 q151 q152 q61 q62 q120 q121 q122 q138 q139 q147 q148 q165 q166 q182 q183 q186 q187 q193 q194 q59 q60 q65 q66 : G), ((q151 ◇ q152) ◇ (q152 ◇ q152))=((q151 ◇ q151) ◇ q152):=by
    intro q145 q146 q149 q150 q151 q152 q61 q62 q120 q121 q122 q138 q139 q147 q148 q165 q166 q182 q183 q186 q187 q193 q194 q59 q60 q65 q66
    exact (((apc247 (((q151 ◇ q151) ◇ q152) ◇ q152) (((q151 ◇ q151) ◇ q152) ◇ q152) (((q151 ◇ q151) ◇ q152) ◇ q152) (((q151 ◇ q151) ◇ q152) ◇ q152) (((q151 ◇ q151) ◇ q152) ◇ q152) (((q151 ◇ q151) ◇ q152) ◇ q152) (((q151 ◇ q151) ◇ q152) ◇ q152) (((q151 ◇ q151) ◇ q152) ◇ q152) (((q151 ◇ q151) ◇ q152) ◇ q152) (((q151 ◇ q151) ◇ q152) ◇ q152) q151 q152).symm).trans ((((cg (fun t => t ◇ q152) (apc248 ((q152 ◇ q152) ◇ q151) ((q152 ◇ q152) ◇ q151) ((q152 ◇ q152) ◇ q151) ((q152 ◇ q152) ◇ q151) ((q152 ◇ q152) ◇ q151) ((q152 ◇ q152) ◇ q151) ((q152 ◇ q152) ◇ q151) ((q152 ◇ q152) ◇ q151) ((q152 ◇ q152) ◇ q151) ((q152 ◇ q152) ◇ q151) ((q152 ◇ q152) ◇ q151) ((q152 ◇ q152) ◇ q151) ((q152 ◇ q152) ◇ q151) ((q152 ◇ q152) ◇ q151) ((q152 ◇ q152) ◇ q151) ((q152 ◇ q152) ◇ q151) ((q152 ◇ q152) ◇ q151) ((q152 ◇ q152) ◇ q151) ((q152 ◇ q152) ◇ q151) ((q152 ◇ q152) ◇ q151) ((q152 ◇ q152) ◇ q151) ((q152 ◇ q152) ◇ q151) ((q152 ◇ q152) ◇ q151) q151 q152 ((q152 ◇ q152) ◇ q151) ((q152 ◇ q152) ◇ q151))).symm).trans ((apc180 q151 q152 q151 q151).trans (rfl))).trans (rfl))).symm
  have apc259 : forall (q145 q146 q149 q150 q151 q152 q61 q62 q120 q121 q122 q138 q139 q147 q148 q165 q166 q182 q183 q186 q187 q193 q194 q59 q60 q65 q66 : G), ((q147 ◇ q148) ◇ q148)=((q147 ◇ q147) ◇ q148):=by
    intro q145 q146 q149 q150 q151 q152 q61 q62 q120 q121 q122 q138 q139 q147 q148 q165 q166 q182 q183 q186 q187 q193 q194 q59 q60 q65 q66
    exact (((apc248 (((q148 ◇ q147) ◇ (q148 ◇ q147)) ◇ q148) (((q148 ◇ q147) ◇ (q148 ◇ q147)) ◇ q148) (((q148 ◇ q147) ◇ (q148 ◇ q147)) ◇ q148) (((q148 ◇ q147) ◇ (q148 ◇ q147)) ◇ q148) (((q148 ◇ q147) ◇ (q148 ◇ q147)) ◇ q148) (((q148 ◇ q147) ◇ (q148 ◇ q147)) ◇ q148) (((q148 ◇ q147) ◇ (q148 ◇ q147)) ◇ q148) (((q148 ◇ q147) ◇ (q148 ◇ q147)) ◇ q148) (((q148 ◇ q147) ◇ (q148 ◇ q147)) ◇ q148) (((q148 ◇ q147) ◇ (q148 ◇ q147)) ◇ q148) (((q148 ◇ q147) ◇ (q148 ◇ q147)) ◇ q148) (((q148 ◇ q147) ◇ (q148 ◇ q147)) ◇ q148) (((q148 ◇ q147) ◇ (q148 ◇ q147)) ◇ q148) (((q148 ◇ q147) ◇ (q148 ◇ q147)) ◇ q148) (((q148 ◇ q147) ◇ (q148 ◇ q147)) ◇ q148) (((q148 ◇ q147) ◇ (q148 ◇ q147)) ◇ q148) (((q148 ◇ q147) ◇ (q148 ◇ q147)) ◇ q148) (((q148 ◇ q147) ◇ (q148 ◇ q147)) ◇ q148) (((q148 ◇ q147) ◇ (q148 ◇ q147)) ◇ q148) (((q148 ◇ q147) ◇ (q148 ◇ q147)) ◇ q148) (((q148 ◇ q147) ◇ (q148 ◇ q147)) ◇ q148) (((q148 ◇ q147) ◇ (q148 ◇ q147)) ◇ q148) (((q148 ◇ q147) ◇ (q148 ◇ q147)) ◇ q148) q148 (q148 ◇ q147) (((q148 ◇ q147) ◇ (q148 ◇ q147)) ◇ q148) (((q148 ◇ q147) ◇ (q148 ◇ q147)) ◇ q148)).trans (apc249 q147 q148)).symm).trans ((((apc257 (((q148 ◇ q147) ◇ q148) ◇ (q148 ◇ q148)) (((q148 ◇ q147) ◇ q148) ◇ (q148 ◇ q148)) (((q148 ◇ q147) ◇ q148) ◇ (q148 ◇ q148)) (((q148 ◇ q147) ◇ q148) ◇ (q148 ◇ q148)) (q148 ◇ q147) q148 (((q148 ◇ q147) ◇ q148) ◇ (q148 ◇ q148)) (((q148 ◇ q147) ◇ q148) ◇ (q148 ◇ q148)) (((q148 ◇ q147) ◇ q148) ◇ (q148 ◇ q148)) (((q148 ◇ q147) ◇ q148) ◇ (q148 ◇ q148)) (((q148 ◇ q147) ◇ q148) ◇ (q148 ◇ q148)) (((q148 ◇ q147) ◇ q148) ◇ (q148 ◇ q148)) (((q148 ◇ q147) ◇ q148) ◇ (q148 ◇ q148)) (((q148 ◇ q147) ◇ q148) ◇ (q148 ◇ q148)) (((q148 ◇ q147) ◇ q148) ◇ (q148 ◇ q148)) (((q148 ◇ q147) ◇ q148) ◇ (q148 ◇ q148)) (((q148 ◇ q147) ◇ q148) ◇ (q148 ◇ q148)) (((q148 ◇ q147) ◇ q148) ◇ (q148 ◇ q148)) (((q148 ◇ q147) ◇ q148) ◇ (q148 ◇ q148)) (((q148 ◇ q147) ◇ q148) ◇ (q148 ◇ q148)) (((q148 ◇ q147) ◇ q148) ◇ (q148 ◇ q148)) (((q148 ◇ q147) ◇ q148) ◇ (q148 ◇ q148)) (((q148 ◇ q147) ◇ q148) ◇ (q148 ◇ q148)) (((q148 ◇ q147) ◇ q148) ◇ (q148 ◇ q148)) (((q148 ◇ q147) ◇ q148) ◇ (q148 ◇ q148)) (((q148 ◇ q147) ◇ q148) ◇ (q148 ◇ q148)) (((q148 ◇ q147) ◇ q148) ◇ (q148 ◇ q148))).symm).trans ((apc182 q147 q148 q147 q147).trans (apc257 ((q147 ◇ q148) ◇ (q148 ◇ q148)) ((q147 ◇ q148) ◇ (q148 ◇ q148)) ((q147 ◇ q148) ◇ (q148 ◇ q148)) ((q147 ◇ q148) ◇ (q148 ◇ q148)) q147 q148 ((q147 ◇ q148) ◇ (q148 ◇ q148)) ((q147 ◇ q148) ◇ (q148 ◇ q148)) ((q147 ◇ q148) ◇ (q148 ◇ q148)) ((q147 ◇ q148) ◇ (q148 ◇ q148)) ((q147 ◇ q148) ◇ (q148 ◇ q148)) ((q147 ◇ q148) ◇ (q148 ◇ q148)) ((q147 ◇ q148) ◇ (q148 ◇ q148)) ((q147 ◇ q148) ◇ (q148 ◇ q148)) ((q147 ◇ q148) ◇ (q148 ◇ q148)) ((q147 ◇ q148) ◇ (q148 ◇ q148)) ((q147 ◇ q148) ◇ (q148 ◇ q148)) ((q147 ◇ q148) ◇ (q148 ◇ q148)) ((q147 ◇ q148) ◇ (q148 ◇ q148)) ((q147 ◇ q148) ◇ (q148 ◇ q148)) ((q147 ◇ q148) ◇ (q148 ◇ q148)) ((q147 ◇ q148) ◇ (q148 ◇ q148)) ((q147 ◇ q148) ◇ (q148 ◇ q148)) ((q147 ◇ q148) ◇ (q148 ◇ q148)) ((q147 ◇ q148) ◇ (q148 ◇ q148)) ((q147 ◇ q148) ◇ (q148 ◇ q148)) ((q147 ◇ q148) ◇ (q148 ◇ q148))))).trans (rfl))
  have apc265 : forall (q145 q146 q149 q150 q151 q152 q61 q62 q120 q121 q122 q138 q139 q147 q148 q165 q166 q182 q183 q186 q187 q191 q192 q59 q60 q65 q66 : G), ((q192 ◇ q192) ◇ (q191 ◇ q191))=((q191 ◇ q191) ◇ q192):=by
    intro q145 q146 q149 q150 q151 q152 q61 q62 q120 q121 q122 q138 q139 q147 q148 q165 q166 q182 q183 q186 q187 q191 q192 q59 q60 q65 q66
    exact ((((apc257 (((q191 ◇ q191) ◇ q192) ◇ (q192 ◇ q192)) (((q191 ◇ q191) ◇ q192) ◇ (q192 ◇ q192)) (((q191 ◇ q191) ◇ q192) ◇ (q192 ◇ q192)) (((q191 ◇ q191) ◇ q192) ◇ (q192 ◇ q192)) (q191 ◇ q191) q192 (((q191 ◇ q191) ◇ q192) ◇ (q192 ◇ q192)) (((q191 ◇ q191) ◇ q192) ◇ (q192 ◇ q192)) (((q191 ◇ q191) ◇ q192) ◇ (q192 ◇ q192)) (((q191 ◇ q191) ◇ q192) ◇ (q192 ◇ q192)) (((q191 ◇ q191) ◇ q192) ◇ (q192 ◇ q192)) (((q191 ◇ q191) ◇ q192) ◇ (q192 ◇ q192)) (((q191 ◇ q191) ◇ q192) ◇ (q192 ◇ q192)) (((q191 ◇ q191) ◇ q192) ◇ (q192 ◇ q192)) (((q191 ◇ q191) ◇ q192) ◇ (q192 ◇ q192)) (((q191 ◇ q191) ◇ q192) ◇ (q192 ◇ q192)) (((q191 ◇ q191) ◇ q192) ◇ (q192 ◇ q192)) (((q191 ◇ q191) ◇ q192) ◇ (q192 ◇ q192)) (((q191 ◇ q191) ◇ q192) ◇ (q192 ◇ q192)) (((q191 ◇ q191) ◇ q192) ◇ (q192 ◇ q192)) (((q191 ◇ q191) ◇ q192) ◇ (q192 ◇ q192)) (((q191 ◇ q191) ◇ q192) ◇ (q192 ◇ q192)) (((q191 ◇ q191) ◇ q192) ◇ (q192 ◇ q192)) (((q191 ◇ q191) ◇ q192) ◇ (q192 ◇ q192)) (((q191 ◇ q191) ◇ q192) ◇ (q192 ◇ q192)) (((q191 ◇ q191) ◇ q192) ◇ (q192 ◇ q192)) (((q191 ◇ q191) ◇ q192) ◇ (q192 ◇ q192))).trans (cg (fun t => t ◇ q192) (apc246 q191 q191))).trans (apc250 q191 q191 q192)).symm).trans ((((rfl).symm).trans ((apc241 q191 q192).trans (apc245 ((q192 ◇ q191) ◇ (q192 ◇ q192)) ((q192 ◇ q191) ◇ (q192 ◇ q192)) ((q192 ◇ q191) ◇ (q192 ◇ q192)) ((q192 ◇ q191) ◇ (q192 ◇ q192)) ((q192 ◇ q191) ◇ (q192 ◇ q192)) ((q192 ◇ q191) ◇ (q192 ◇ q192)) ((q192 ◇ q191) ◇ (q192 ◇ q192)) ((q192 ◇ q191) ◇ (q192 ◇ q192)) ((q192 ◇ q191) ◇ (q192 ◇ q192)) ((q192 ◇ q191) ◇ (q192 ◇ q192)) ((q192 ◇ q191) ◇ (q192 ◇ q192)) ((q192 ◇ q191) ◇ (q192 ◇ q192)) ((q192 ◇ q191) ◇ (q192 ◇ q192)) ((q192 ◇ q191) ◇ (q192 ◇ q192)) ((q192 ◇ q191) ◇ (q192 ◇ q192)) ((q192 ◇ q191) ◇ (q192 ◇ q192)) ((q192 ◇ q191) ◇ (q192 ◇ q192)) ((q192 ◇ q191) ◇ (q192 ◇ q192)) ((q192 ◇ q191) ◇ (q192 ◇ q192)) ((q192 ◇ q191) ◇ (q192 ◇ q192)) ((q192 ◇ q191) ◇ (q192 ◇ q192)) q191 q192 ((q192 ◇ q191) ◇ (q192 ◇ q192)) ((q192 ◇ q191) ◇ (q192 ◇ q192))))).trans (apc246 q191 q192))
  have apc266 : forall (q145 q146 q149 q150 q151 q152 q61 q62 q120 q121 q122 q138 q139 q147 q148 q165 q166 q182 q183 q186 q187 q191 q192 q193 q194 q59 q60 q65 q66 : G), (((q182 ◇ q182) ◇ q183) ◇ q182)=((q182 ◇ q182) ◇ q183):=by
    intro q145 q146 q149 q150 q151 q152 q61 q62 q120 q121 q122 q138 q139 q147 q148 q165 q166 q182 q183 q186 q187 q191 q192 q193 q194 q59 q60 q65 q66
    exact ((cg (fun t => t ◇ q182) (apc248 ((q183 ◇ q183) ◇ q182) ((q183 ◇ q183) ◇ q182) ((q183 ◇ q183) ◇ q182) ((q183 ◇ q183) ◇ q182) ((q183 ◇ q183) ◇ q182) ((q183 ◇ q183) ◇ q182) ((q183 ◇ q183) ◇ q182) ((q183 ◇ q183) ◇ q182) ((q183 ◇ q183) ◇ q182) ((q183 ◇ q183) ◇ q182) ((q183 ◇ q183) ◇ q182) ((q183 ◇ q183) ◇ q182) ((q183 ◇ q183) ◇ q182) ((q183 ◇ q183) ◇ q182) ((q183 ◇ q183) ◇ q182) ((q183 ◇ q183) ◇ q182) ((q183 ◇ q183) ◇ q182) ((q183 ◇ q183) ◇ q182) ((q183 ◇ q183) ◇ q182) ((q183 ◇ q183) ◇ q182) ((q183 ◇ q183) ◇ q182) ((q183 ◇ q183) ◇ q182) ((q183 ◇ q183) ◇ q182) q182 q183 ((q183 ◇ q183) ◇ q182) ((q183 ◇ q183) ◇ q182))).symm).trans ((((cg (fun t => t ◇ q182) (apc265 ((q182 ◇ q182) ◇ (q183 ◇ q183)) ((q182 ◇ q182) ◇ (q183 ◇ q183)) ((q182 ◇ q182) ◇ (q183 ◇ q183)) ((q182 ◇ q182) ◇ (q183 ◇ q183)) ((q182 ◇ q182) ◇ (q183 ◇ q183)) ((q182 ◇ q182) ◇ (q183 ◇ q183)) ((q182 ◇ q182) ◇ (q183 ◇ q183)) ((q182 ◇ q182) ◇ (q183 ◇ q183)) ((q182 ◇ q182) ◇ (q183 ◇ q183)) ((q182 ◇ q182) ◇ (q183 ◇ q183)) ((q182 ◇ q182) ◇ (q183 ◇ q183)) ((q182 ◇ q182) ◇ (q183 ◇ q183)) ((q182 ◇ q182) ◇ (q183 ◇ q183)) ((q182 ◇ q182) ◇ (q183 ◇ q183)) ((q182 ◇ q182) ◇ (q183 ◇ q183)) ((q182 ◇ q182) ◇ (q183 ◇ q183)) ((q182 ◇ q182) ◇ (q183 ◇ q183)) ((q182 ◇ q182) ◇ (q183 ◇ q183)) ((q182 ◇ q182) ◇ (q183 ◇ q183)) ((q182 ◇ q182) ◇ (q183 ◇ q183)) ((q182 ◇ q182) ◇ (q183 ◇ q183)) q183 q182 ((q182 ◇ q182) ◇ (q183 ◇ q183)) ((q182 ◇ q182) ◇ (q183 ◇ q183)) ((q182 ◇ q182) ◇ (q183 ◇ q183)) ((q182 ◇ q182) ◇ (q183 ◇ q183)))).symm).trans ((apc253 q182 q183 q182 q182 q182 q182).trans (rfl))).trans (rfl))
  have apc267 : forall (q200 q201 : G), ((q201 ◇ q201) ◇ (q201 ◇ q200))=((q200 ◇ q200) ◇ q201):=by
    intro q200 q201
    exact ((((cg (fun t => t ◇ q201) (apc259 ((q200 ◇ q201) ◇ q201) ((q200 ◇ q201) ◇ q201) ((q200 ◇ q201) ◇ q201) ((q200 ◇ q201) ◇ q201) ((q200 ◇ q201) ◇ q201) ((q200 ◇ q201) ◇ q201) ((q200 ◇ q201) ◇ q201) ((q200 ◇ q201) ◇ q201) ((q200 ◇ q201) ◇ q201) ((q200 ◇ q201) ◇ q201) ((q200 ◇ q201) ◇ q201) ((q200 ◇ q201) ◇ q201) ((q200 ◇ q201) ◇ q201) q200 q201 ((q200 ◇ q201) ◇ q201) ((q200 ◇ q201) ◇ q201) ((q200 ◇ q201) ◇ q201) ((q200 ◇ q201) ◇ q201) ((q200 ◇ q201) ◇ q201) ((q200 ◇ q201) ◇ q201) ((q200 ◇ q201) ◇ q201) ((q200 ◇ q201) ◇ q201) ((q200 ◇ q201) ◇ q201) ((q200 ◇ q201) ◇ q201) ((q200 ◇ q201) ◇ q201) ((q200 ◇ q201) ◇ q201))).trans (apc247 (((q200 ◇ q200) ◇ q201) ◇ q201) (((q200 ◇ q200) ◇ q201) ◇ q201) (((q200 ◇ q200) ◇ q201) ◇ q201) (((q200 ◇ q200) ◇ q201) ◇ q201) (((q200 ◇ q200) ◇ q201) ◇ q201) (((q200 ◇ q200) ◇ q201) ◇ q201) (((q200 ◇ q200) ◇ q201) ◇ q201) (((q200 ◇ q200) ◇ q201) ◇ q201) (((q200 ◇ q200) ◇ q201) ◇ q201) (((q200 ◇ q200) ◇ q201) ◇ q201) q200 q201)).symm).trans ((((cg (fun t => t ◇ q201) ((h q200 q201 q201).symm)).symm).trans (apc266 q200 q200 q200 q200 q200 q200 q200 q200 q200 q200 q200 q200 q200 q200 q200 q200 q200 q201 (q201 ◇ q200) q200 q200 q200 q200 q200 q200 q200 q200 q200 q200)).trans (rfl))).symm
  have apc268 : forall (q145 q146 q149 q150 q151 q152 q61 q62 q120 q121 q122 q138 q139 q147 q148 q165 q166 q182 q183 q186 q187 q193 q194 q59 q60 q65 q66 : G), ((q166 ◇ q166) ◇ (q165 ◇ q166))=((q165 ◇ q165) ◇ q166):=by
    intro q145 q146 q149 q150 q151 q152 q61 q62 q120 q121 q122 q138 q139 q147 q148 q165 q166 q182 q183 q186 q187 q193 q194 q59 q60 q65 q66
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc178 q165 q166).trans (apc257 ((q165 ◇ q166) ◇ (q166 ◇ q166)) ((q165 ◇ q166) ◇ (q166 ◇ q166)) ((q165 ◇ q166) ◇ (q166 ◇ q166)) ((q165 ◇ q166) ◇ (q166 ◇ q166)) q165 q166 ((q165 ◇ q166) ◇ (q166 ◇ q166)) ((q165 ◇ q166) ◇ (q166 ◇ q166)) ((q165 ◇ q166) ◇ (q166 ◇ q166)) ((q165 ◇ q166) ◇ (q166 ◇ q166)) ((q165 ◇ q166) ◇ (q166 ◇ q166)) ((q165 ◇ q166) ◇ (q166 ◇ q166)) ((q165 ◇ q166) ◇ (q166 ◇ q166)) ((q165 ◇ q166) ◇ (q166 ◇ q166)) ((q165 ◇ q166) ◇ (q166 ◇ q166)) ((q165 ◇ q166) ◇ (q166 ◇ q166)) ((q165 ◇ q166) ◇ (q166 ◇ q166)) ((q165 ◇ q166) ◇ (q166 ◇ q166)) ((q165 ◇ q166) ◇ (q166 ◇ q166)) ((q165 ◇ q166) ◇ (q166 ◇ q166)) ((q165 ◇ q166) ◇ (q166 ◇ q166)) ((q165 ◇ q166) ◇ (q166 ◇ q166)) ((q165 ◇ q166) ◇ (q166 ◇ q166)) ((q165 ◇ q166) ◇ (q166 ◇ q166)) ((q165 ◇ q166) ◇ (q166 ◇ q166)) ((q165 ◇ q166) ◇ (q166 ◇ q166)) ((q165 ◇ q166) ◇ (q166 ◇ q166))))).trans (rfl))
  have apc272 : forall (q202 q203 : G), (((q202 ◇ q202) ◇ q203) ◇ (q203 ◇ q202))=((q202 ◇ q202) ◇ q203):=by
    intro q202 q203
    exact ((cg (fun t => t ◇ (q203 ◇ q202)) (apc259 ((q202 ◇ q203) ◇ q203) ((q202 ◇ q203) ◇ q203) ((q202 ◇ q203) ◇ q203) ((q202 ◇ q203) ◇ q203) ((q202 ◇ q203) ◇ q203) ((q202 ◇ q203) ◇ q203) ((q202 ◇ q203) ◇ q203) ((q202 ◇ q203) ◇ q203) ((q202 ◇ q203) ◇ q203) ((q202 ◇ q203) ◇ q203) ((q202 ◇ q203) ◇ q203) ((q202 ◇ q203) ◇ q203) ((q202 ◇ q203) ◇ q203) q202 q203 ((q202 ◇ q203) ◇ q203) ((q202 ◇ q203) ◇ q203) ((q202 ◇ q203) ◇ q203) ((q202 ◇ q203) ◇ q203) ((q202 ◇ q203) ◇ q203) ((q202 ◇ q203) ◇ q203) ((q202 ◇ q203) ◇ q203) ((q202 ◇ q203) ◇ q203) ((q202 ◇ q203) ◇ q203) ((q202 ◇ q203) ◇ q203) ((q202 ◇ q203) ◇ q203) ((q202 ◇ q203) ◇ q203))).symm).trans ((((cg (fun t => t ◇ (q203 ◇ q202)) ((h q202 q203 q203).symm)).symm).trans (apc247 q202 q202 q202 q202 q202 q202 q202 q202 q202 q202 q203 (q203 ◇ q202))).trans (apc267 q202 q203))
  have apc278 : forall (q145 q146 q149 q150 q151 q152 q61 q62 q120 q121 q122 q138 q139 q147 q148 q165 q166 q182 q183 q186 q187 q193 q194 q59 q60 q65 q66 q63 q64 q142 q143 q144 : G), ((q64 ◇ (q63 ◇ (q64 ◇ q64))) ◇ q64)=((q63 ◇ q63) ◇ q64):=by
    intro q145 q146 q149 q150 q151 q152 q61 q62 q120 q121 q122 q138 q139 q147 q148 q165 q166 q182 q183 q186 q187 q193 q194 q59 q60 q65 q66 q63 q64 q142 q143 q144
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc133 q63 q64 q63 q63 q63).trans (apc257 ((q63 ◇ q64) ◇ (q64 ◇ q64)) ((q63 ◇ q64) ◇ (q64 ◇ q64)) ((q63 ◇ q64) ◇ (q64 ◇ q64)) ((q63 ◇ q64) ◇ (q64 ◇ q64)) q63 q64 ((q63 ◇ q64) ◇ (q64 ◇ q64)) ((q63 ◇ q64) ◇ (q64 ◇ q64)) ((q63 ◇ q64) ◇ (q64 ◇ q64)) ((q63 ◇ q64) ◇ (q64 ◇ q64)) ((q63 ◇ q64) ◇ (q64 ◇ q64)) ((q63 ◇ q64) ◇ (q64 ◇ q64)) ((q63 ◇ q64) ◇ (q64 ◇ q64)) ((q63 ◇ q64) ◇ (q64 ◇ q64)) ((q63 ◇ q64) ◇ (q64 ◇ q64)) ((q63 ◇ q64) ◇ (q64 ◇ q64)) ((q63 ◇ q64) ◇ (q64 ◇ q64)) ((q63 ◇ q64) ◇ (q64 ◇ q64)) ((q63 ◇ q64) ◇ (q64 ◇ q64)) ((q63 ◇ q64) ◇ (q64 ◇ q64)) ((q63 ◇ q64) ◇ (q64 ◇ q64)) ((q63 ◇ q64) ◇ (q64 ◇ q64)) ((q63 ◇ q64) ◇ (q64 ◇ q64)) ((q63 ◇ q64) ◇ (q64 ◇ q64)) ((q63 ◇ q64) ◇ (q64 ◇ q64)) ((q63 ◇ q64) ◇ (q64 ◇ q64)) ((q63 ◇ q64) ◇ (q64 ◇ q64))))).trans (rfl))
  have apc281 : forall (q204 q205 q206 : G), ((q205 ◇ ((q204 ◇ q204) ◇ q205)) ◇ q206)=(((q204 ◇ q204) ◇ q205) ◇ q206):=by
    intro q204 q205 q206
    exact (((((cg (fun t => t ◇ q206) (apc189 q204 q205)).trans (cg (fun t => t ◇ q206) (apc257 ((q205 ◇ q204) ◇ (q204 ◇ q204)) ((q205 ◇ q204) ◇ (q204 ◇ q204)) ((q205 ◇ q204) ◇ (q204 ◇ q204)) ((q205 ◇ q204) ◇ (q204 ◇ q204)) q205 q204 ((q205 ◇ q204) ◇ (q204 ◇ q204)) ((q205 ◇ q204) ◇ (q204 ◇ q204)) ((q205 ◇ q204) ◇ (q204 ◇ q204)) ((q205 ◇ q204) ◇ (q204 ◇ q204)) ((q205 ◇ q204) ◇ (q204 ◇ q204)) ((q205 ◇ q204) ◇ (q204 ◇ q204)) ((q205 ◇ q204) ◇ (q204 ◇ q204)) ((q205 ◇ q204) ◇ (q204 ◇ q204)) ((q205 ◇ q204) ◇ (q204 ◇ q204)) ((q205 ◇ q204) ◇ (q204 ◇ q204)) ((q205 ◇ q204) ◇ (q204 ◇ q204)) ((q205 ◇ q204) ◇ (q204 ◇ q204)) ((q205 ◇ q204) ◇ (q204 ◇ q204)) ((q205 ◇ q204) ◇ (q204 ◇ q204)) ((q205 ◇ q204) ◇ (q204 ◇ q204)) ((q205 ◇ q204) ◇ (q204 ◇ q204)) ((q205 ◇ q204) ◇ (q204 ◇ q204)) ((q205 ◇ q204) ◇ (q204 ◇ q204)) ((q205 ◇ q204) ◇ (q204 ◇ q204)) ((q205 ◇ q204) ◇ (q204 ◇ q204)) ((q205 ◇ q204) ◇ (q204 ◇ q204))))).trans (cg (fun t => t ◇ q206) (apc248 ((q205 ◇ q205) ◇ q204) ((q205 ◇ q205) ◇ q204) ((q205 ◇ q205) ◇ q204) ((q205 ◇ q205) ◇ q204) ((q205 ◇ q205) ◇ q204) ((q205 ◇ q205) ◇ q204) ((q205 ◇ q205) ◇ q204) ((q205 ◇ q205) ◇ q204) ((q205 ◇ q205) ◇ q204) ((q205 ◇ q205) ◇ q204) ((q205 ◇ q205) ◇ q204) ((q205 ◇ q205) ◇ q204) ((q205 ◇ q205) ◇ q204) ((q205 ◇ q205) ◇ q204) ((q205 ◇ q205) ◇ q204) ((q205 ◇ q205) ◇ q204) ((q205 ◇ q205) ◇ q204) ((q205 ◇ q205) ◇ q204) ((q205 ◇ q205) ◇ q204) ((q205 ◇ q205) ◇ q204) ((q205 ◇ q205) ◇ q204) ((q205 ◇ q205) ◇ q204) ((q205 ◇ q205) ◇ q204) q204 q205 ((q205 ◇ q205) ◇ q204) ((q205 ◇ q205) ◇ q204)))).symm).trans ((((apc239 q204 q204 q205 q205 q206).symm).trans ((h q205 ((q204 ◇ q204) ◇ q205) q206).symm)).trans (rfl))).symm
  have apc282 : forall (q207 q208 q209 : G), ((q208 ◇ q209) ◇ ((q207 ◇ q207) ◇ q209))=(((q207 ◇ q207) ◇ q209) ◇ (q209 ◇ q208)):=by
    intro q207 q208 q209
    exact (((rfl).symm).trans ((((apc281 q207 q209 (q209 ◇ q208)).symm).trans ((h q208 q209 ((q207 ◇ q207) ◇ q209)).symm)).trans (rfl))).symm
  have apc286 : forall (q210 q211 q212 : G), (((q211 ◇ q211) ◇ q212) ◇ (q212 ◇ (q210 ◇ q211)))=(((q212 ◇ q211) ◇ q211) ◇ (q211 ◇ q210)):=by
    intro q210 q211 q212
    exact ((rfl).symm).trans ((((apc282 q211 (q210 ◇ q211) q212).symm).trans (apc24 q211 q210 q211 q212)).trans (rfl))
  have apc288 : forall (q213 q214 q215 : G), ((q214 ◇ (q213 ◇ q214)) ◇ q215)=(((q213 ◇ q213) ◇ q214) ◇ q215):=by
    intro q213 q214 q215
    exact (((((apc1 q213 q213 q214 q215).trans (cg (fun t => t ◇ q215) (apc267 q214 q213))).trans (cg (fun t => t ◇ q215) (apc248 ((q214 ◇ q214) ◇ q213) ((q214 ◇ q214) ◇ q213) ((q214 ◇ q214) ◇ q213) ((q214 ◇ q214) ◇ q213) ((q214 ◇ q214) ◇ q213) ((q214 ◇ q214) ◇ q213) ((q214 ◇ q214) ◇ q213) ((q214 ◇ q214) ◇ q213) ((q214 ◇ q214) ◇ q213) ((q214 ◇ q214) ◇ q213) ((q214 ◇ q214) ◇ q213) ((q214 ◇ q214) ◇ q213) ((q214 ◇ q214) ◇ q213) ((q214 ◇ q214) ◇ q213) ((q214 ◇ q214) ◇ q213) ((q214 ◇ q214) ◇ q213) ((q214 ◇ q214) ◇ q213) ((q214 ◇ q214) ◇ q213) ((q214 ◇ q214) ◇ q213) ((q214 ◇ q214) ◇ q213) ((q214 ◇ q214) ◇ q213) ((q214 ◇ q214) ◇ q213) ((q214 ◇ q214) ◇ q213) q213 q214 ((q214 ◇ q214) ◇ q213) ((q214 ◇ q214) ◇ q213)))).symm).trans ((((cg (fun t => ((q213 ◇ q214) ◇ q215) ◇ t) (apc259 q213 q213 q213 q213 q213 q213 q213 q213 q213 q213 q213 q213 q213 q213 q214 q213 q213 q213 q213 q213 q213 q213 q213 q213 q213 q213 q213)).symm).trans ((h q214 (q213 ◇ q214) q215).symm)).trans (rfl))).symm
  have apc289 : forall (q216 q217 q218 : G), (((q216 ◇ q216) ◇ q218) ◇ (q218 ◇ q217))=((q217 ◇ q218) ◇ (q216 ◇ q218)):=by
    intro q216 q217 q218
    exact ((rfl).symm).trans ((((apc288 q216 q218 (q218 ◇ q217)).symm).trans ((h q217 q218 (q216 ◇ q218)).symm)).trans (rfl))
  have apc290 : forall (q202 q203 q216 q217 q218 : G), ((q202 ◇ q203) ◇ (q202 ◇ q203))=((q202 ◇ q202) ◇ q203):=by
    intro q202 q203 q216 q217 q218
    exact ((rfl).symm).trans ((((apc289 q202 q202 q203).symm).trans ((apc272 q202 q203).trans (rfl))).trans (rfl))
  have apc291 : forall (q219 q220 : G), ((q219 ◇ q220) ◇ q219)=((q219 ◇ q219) ◇ q220):=by
    intro q219 q220
    exact (((apc248 ((q220 ◇ q220) ◇ q219) ((q220 ◇ q220) ◇ q219) ((q220 ◇ q220) ◇ q219) ((q220 ◇ q220) ◇ q219) ((q220 ◇ q220) ◇ q219) ((q220 ◇ q220) ◇ q219) ((q220 ◇ q220) ◇ q219) ((q220 ◇ q220) ◇ q219) ((q220 ◇ q220) ◇ q219) ((q220 ◇ q220) ◇ q219) ((q220 ◇ q220) ◇ q219) ((q220 ◇ q220) ◇ q219) ((q220 ◇ q220) ◇ q219) ((q220 ◇ q220) ◇ q219) ((q220 ◇ q220) ◇ q219) ((q220 ◇ q220) ◇ q219) ((q220 ◇ q220) ◇ q219) ((q220 ◇ q220) ◇ q219) ((q220 ◇ q220) ◇ q219) ((q220 ◇ q220) ◇ q219) ((q220 ◇ q220) ◇ q219) ((q220 ◇ q220) ◇ q219) ((q220 ◇ q220) ◇ q219) q219 q220 ((q220 ◇ q220) ◇ q219) ((q220 ◇ q220) ◇ q219)).symm).trans ((((apc290 q220 q219 q219 q219 q219).symm).trans ((h q219 q220 q219).symm)).trans (rfl))).symm
  have apc292 : forall (q221 q222 q223 : G), (((q221 ◇ q221) ◇ q222) ◇ q223)=((q223 ◇ q223) ◇ (q221 ◇ q222)):=by
    intro q221 q222 q223
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q223) (apc290 q221 q222 q221 q221 q221)).symm).trans (apc248 q221 q221 q221 q221 q221 q221 q221 q221 q221 q221 q221 q221 q221 q221 q221 q221 q221 q221 q221 q221 q221 q221 q221 q223 (q221 ◇ q222) q221 q221)).trans (rfl))
  have apc297 : forall (q50 q51 q52 q219 q220 : G), (((q52 ◇ q51) ◇ q50) ◇ (q51 ◇ q50))=((q52 ◇ q52) ◇ (q50 ◇ q51)):=by
    intro q50 q51 q52 q219 q220
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc25 q50 q51 q52).trans (apc291 q52 (q50 ◇ q51)))).trans (rfl))
  have apc304 : forall (q145 q146 q149 q150 q151 q152 q61 q62 q120 q121 q122 q138 q139 q147 q148 q165 q166 q182 q183 q186 q187 q193 q194 q59 q60 q65 q66 q219 q220 q63 q64 q142 q143 q144 : G), ((q64 ◇ q64) ◇ (q63 ◇ (q64 ◇ q64)))=((q63 ◇ q63) ◇ q64):=by
    intro q145 q146 q149 q150 q151 q152 q61 q62 q120 q121 q122 q138 q139 q147 q148 q165 q166 q182 q183 q186 q187 q193 q194 q59 q60 q65 q66 q219 q220 q63 q64 q142 q143 q144
    exact ((rfl).symm).trans ((((apc291 q64 (q63 ◇ (q64 ◇ q64))).symm).trans ((apc278 q63 q63 q63 q63 q63 q63 q63 q63 q63 q63 q63 q63 q63 q63 q63 q63 q63 q63 q63 q63 q63 q63 q63 q63 q63 q63 q63 q63 q64 q63 q63 q63).trans (rfl))).trans (rfl))
  have apc316 : forall (q224 q225 q226 : G), (((q226 ◇ q226) ◇ (q224 ◇ q225)) ◇ q226)=((q226 ◇ q226) ◇ (q224 ◇ q225)):=by
    intro q224 q225 q226
    exact ((cg (fun t => t ◇ q226) (apc250 q224 q225 q226)).symm).trans ((((cg (fun t => t ◇ q226) (cg (fun t => t ◇ q226) ((h q225 q224 q225).symm))).symm).trans (apc247 q224 q224 q224 q224 q224 q224 q224 q224 q224 q224 (q224 ◇ q225) q226)).trans ((cg (fun t => t ◇ q226) (apc290 q224 q225 ((q224 ◇ q225) ◇ (q224 ◇ q225)) ((q224 ◇ q225) ◇ (q224 ◇ q225)) ((q224 ◇ q225) ◇ (q224 ◇ q225)))).trans (apc292 q224 q225 q226)))
  have apc324 : forall (q227 q228 q229 : G), (((q227 ◇ q227) ◇ q228) ◇ (q229 ◇ (q227 ◇ q228)))=((q229 ◇ q229) ◇ (q227 ◇ q228)):=by
    intro q227 q228 q229
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (q229 ◇ (q227 ◇ q228))) (apc290 q227 q228 q227 q227 q227)).symm).trans (apc268 q227 q227 q227 q227 q227 q227 q227 q227 q227 q227 q227 q227 q227 q227 q227 q229 (q227 ◇ q228) q227 q227 q227 q227 q227 q227 q227 q227 q227 q227)).trans (rfl))
  have apc328 : forall (q213 q214 q215 q221 q222 q223 : G), ((q214 ◇ (q213 ◇ q214)) ◇ q215)=((q215 ◇ q215) ◇ (q213 ◇ q214)):=by
    intro q213 q214 q215 q221 q222 q223
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc288 q213 q214 q215).trans (apc292 q213 q214 q215))).trans (rfl))
  have apc329 : forall (q230 q231 q232 : G), ((q232 ◇ q232) ◇ (q231 ◇ (q230 ◇ q230)))=((q232 ◇ q232) ◇ (q230 ◇ q231)):=by
    intro q230 q231 q232
    exact ((((cg (fun t => t ◇ q232) (apc248 ((q231 ◇ q231) ◇ q230) ((q231 ◇ q231) ◇ q230) ((q231 ◇ q231) ◇ q230) ((q231 ◇ q231) ◇ q230) ((q231 ◇ q231) ◇ q230) ((q231 ◇ q231) ◇ q230) ((q231 ◇ q231) ◇ q230) ((q231 ◇ q231) ◇ q230) ((q231 ◇ q231) ◇ q230) ((q231 ◇ q231) ◇ q230) ((q231 ◇ q231) ◇ q230) ((q231 ◇ q231) ◇ q230) ((q231 ◇ q231) ◇ q230) ((q231 ◇ q231) ◇ q230) ((q231 ◇ q231) ◇ q230) ((q231 ◇ q231) ◇ q230) ((q231 ◇ q231) ◇ q230) ((q231 ◇ q231) ◇ q230) ((q231 ◇ q231) ◇ q230) ((q231 ◇ q231) ◇ q230) ((q231 ◇ q231) ◇ q230) ((q231 ◇ q231) ◇ q230) ((q231 ◇ q231) ◇ q230) q230 q231 ((q231 ◇ q231) ◇ q230) ((q231 ◇ q231) ◇ q230))).trans (apc292 q230 q231 q232)).symm).trans ((((cg (fun t => t ◇ q232) (apc304 q230 q230 q230 q230 q230 q230 q230 q230 q230 q230 q230 q230 q230 q230 q230 q230 q230 q230 q230 q230 q230 q230 q230 q230 q230 q230 q230 q230 q230 q231 q230 q230 q230 q230)).symm).trans (apc328 q231 (q230 ◇ q230) q232 q230 q230 q230)).trans (rfl))).symm
  have apc330 : forall (q233 q234 q235 : G), (((q235 ◇ q233) ◇ q233) ◇ (q233 ◇ q234))=(((q233 ◇ q233) ◇ q235) ◇ (q233 ◇ q234)):=by
    intro q233 q234 q235
    exact (((cg (fun t => t ◇ (q233 ◇ q234)) (apc248 ((q235 ◇ q235) ◇ q233) ((q235 ◇ q235) ◇ q233) ((q235 ◇ q235) ◇ q233) ((q235 ◇ q235) ◇ q233) ((q235 ◇ q235) ◇ q233) ((q235 ◇ q235) ◇ q233) ((q235 ◇ q235) ◇ q233) ((q235 ◇ q235) ◇ q233) ((q235 ◇ q235) ◇ q233) ((q235 ◇ q235) ◇ q233) ((q235 ◇ q235) ◇ q233) ((q235 ◇ q235) ◇ q233) ((q235 ◇ q235) ◇ q233) ((q235 ◇ q235) ◇ q233) ((q235 ◇ q235) ◇ q233) ((q235 ◇ q235) ◇ q233) ((q235 ◇ q235) ◇ q233) ((q235 ◇ q235) ◇ q233) ((q235 ◇ q235) ◇ q233) ((q235 ◇ q235) ◇ q233) ((q235 ◇ q235) ◇ q233) ((q235 ◇ q235) ◇ q233) ((q235 ◇ q235) ◇ q233) q233 q235 ((q235 ◇ q235) ◇ q233) ((q235 ◇ q235) ◇ q233))).symm).trans ((((cg (fun t => t ◇ (q233 ◇ q234)) (apc267 q235 q233)).symm).trans (apc34 q233 q234 q233 q235 q233 q233 q233 q233)).trans (rfl))).symm
  have apc333 : forall (q236 q237 q238 q239 : G), ((q239 ◇ q239) ◇ ((q236 ◇ q237) ◇ q238))=(((q238 ◇ q238) ◇ (q236 ◇ q237)) ◇ q239):=by
    intro q236 q237 q238 q239
    exact (((cg (fun t => t ◇ q239) (apc292 q236 q237 q238)).symm).trans ((((cg (fun t => t ◇ q239) (cg (fun t => t ◇ q238) (apc290 q236 q237 q236 q236 q236))).symm).trans (apc292 (q236 ◇ q237) q238 q239)).trans (rfl))).symm
  have apc341 : forall (q240 q241 q242 q243 : G), (((q242 ◇ q242) ◇ (q241 ◇ q240)) ◇ q243)=(((q242 ◇ q242) ◇ (q240 ◇ q241)) ◇ q243):=by
    intro q240 q241 q242 q243
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q243) (apc248 q240 q240 q240 q240 q240 q240 q240 q240 q240 q240 q240 q240 q240 q240 q240 q240 q240 q240 q240 q240 q240 q240 q240 q242 (q241 ◇ q240) q240 q240)).symm).trans (apc19 q240 q241 q240 q242 q243)).trans ((cg (fun t => t ◇ q243) (cg (fun t => t ◇ q242) (apc291 q240 q241))).trans (cg (fun t => t ◇ q243) (apc292 q240 q241 q242))))
  have apc343 : forall (q244 q245 q246 : G), ((q246 ◇ q246) ◇ (q245 ◇ q244))=((q246 ◇ q246) ◇ (q244 ◇ q245)):=by
    intro q244 q245 q246
    exact ((apc316 q245 q244 q246).symm).trans ((((apc341 q245 q244 q246 q246).symm).trans (apc316 q244 q245 q246)).trans (rfl))
  have apc347 : forall (q210 q211 q212 q216 q217 q218 : G), (((q211 ◇ q211) ◇ q212) ◇ (q211 ◇ q210))=((q210 ◇ q210) ◇ (q211 ◇ q212)):=by
    intro q210 q211 q212 q216 q217 q218
    exact ((((apc297 q212 q211 q210 (((q210 ◇ q211) ◇ q212) ◇ (q211 ◇ q212)) (((q210 ◇ q211) ◇ q212) ◇ (q211 ◇ q212))).trans (apc343 q211 q212 q210)).symm).trans ((((apc289 q211 (q210 ◇ q211) q212).symm).trans ((apc286 q210 q211 q212).trans (rfl))).trans (apc330 q211 q210 q212))).symm
  have apc349 : forall (q247 q248 q249 : G), ((q248 ◇ q249) ◇ (q247 ◇ q249))=((q248 ◇ q248) ◇ (q247 ◇ q249)):=by
    intro q247 q248 q249
    exact (((cg (fun t => t ◇ (q249 ◇ q248)) (apc259 ((q247 ◇ q249) ◇ q249) ((q247 ◇ q249) ◇ q249) ((q247 ◇ q249) ◇ q249) ((q247 ◇ q249) ◇ q249) ((q247 ◇ q249) ◇ q249) ((q247 ◇ q249) ◇ q249) ((q247 ◇ q249) ◇ q249) ((q247 ◇ q249) ◇ q249) ((q247 ◇ q249) ◇ q249) ((q247 ◇ q249) ◇ q249) ((q247 ◇ q249) ◇ q249) ((q247 ◇ q249) ◇ q249) ((q247 ◇ q249) ◇ q249) q247 q249 ((q247 ◇ q249) ◇ q249) ((q247 ◇ q249) ◇ q249) ((q247 ◇ q249) ◇ q249) ((q247 ◇ q249) ◇ q249) ((q247 ◇ q249) ◇ q249) ((q247 ◇ q249) ◇ q249) ((q247 ◇ q249) ◇ q249) ((q247 ◇ q249) ◇ q249) ((q247 ◇ q249) ◇ q249) ((q247 ◇ q249) ◇ q249) ((q247 ◇ q249) ◇ q249) ((q247 ◇ q249) ◇ q249))).trans (apc289 q247 q248 q249)).symm).trans ((((cg (fun t => t ◇ (q249 ◇ q248)) ((h q247 q249 q249).symm)).symm).trans (apc347 q248 q249 (q249 ◇ q247) q247 q247 q247)).trans (((((apc343 (q249 ◇ q247) q249 q248).trans (apc333 q249 q247 q249 q248)).trans (cg (fun t => t ◇ q248) (apc343 q247 q249 q249))).trans (cg (fun t => t ◇ q248) (apc268 ((q249 ◇ q249) ◇ (q247 ◇ q249)) ((q249 ◇ q249) ◇ (q247 ◇ q249)) ((q249 ◇ q249) ◇ (q247 ◇ q249)) ((q249 ◇ q249) ◇ (q247 ◇ q249)) ((q249 ◇ q249) ◇ (q247 ◇ q249)) ((q249 ◇ q249) ◇ (q247 ◇ q249)) ((q249 ◇ q249) ◇ (q247 ◇ q249)) ((q249 ◇ q249) ◇ (q247 ◇ q249)) ((q249 ◇ q249) ◇ (q247 ◇ q249)) ((q249 ◇ q249) ◇ (q247 ◇ q249)) ((q249 ◇ q249) ◇ (q247 ◇ q249)) ((q249 ◇ q249) ◇ (q247 ◇ q249)) ((q249 ◇ q249) ◇ (q247 ◇ q249)) ((q249 ◇ q249) ◇ (q247 ◇ q249)) ((q249 ◇ q249) ◇ (q247 ◇ q249)) q247 q249 ((q249 ◇ q249) ◇ (q247 ◇ q249)) ((q249 ◇ q249) ◇ (q247 ◇ q249)) ((q249 ◇ q249) ◇ (q247 ◇ q249)) ((q249 ◇ q249) ◇ (q247 ◇ q249)) ((q249 ◇ q249) ◇ (q247 ◇ q249)) ((q249 ◇ q249) ◇ (q247 ◇ q249)) ((q249 ◇ q249) ◇ (q247 ◇ q249)) ((q249 ◇ q249) ◇ (q247 ◇ q249)) ((q249 ◇ q249) ◇ (q247 ◇ q249)) ((q249 ◇ q249) ◇ (q247 ◇ q249))))).trans (apc292 q247 q249 q248)))
  have apc350 : forall (q247 q248 q249 q216 q217 q218 : G), (((q216 ◇ q216) ◇ q218) ◇ (q218 ◇ q217))=((q217 ◇ q217) ◇ (q216 ◇ q218)):=by
    intro q247 q248 q249 q216 q217 q218
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc289 q216 q217 q218).trans (apc349 q216 q217 q218))).trans (rfl))
  have apc352 : forall (q250 q251 q252 : G), ((q252 ◇ q252) ◇ (q250 ◇ q251))=((q250 ◇ q250) ◇ (q251 ◇ q252)):=by
    intro q250 q251 q252
    exact (((rfl).symm).trans ((((apc347 q250 q251 q252 q250 q250 q250).symm).trans (apc292 q251 q252 (q251 ◇ q250))).trans (((apc34 q250 q252 q251 q250 (((q251 ◇ q250) ◇ (q251 ◇ q250)) ◇ (q251 ◇ q252)) (((q251 ◇ q250) ◇ (q251 ◇ q250)) ◇ (q251 ◇ q252)) (((q251 ◇ q250) ◇ (q251 ◇ q250)) ◇ (q251 ◇ q252)) (((q251 ◇ q250) ◇ (q251 ◇ q250)) ◇ (q251 ◇ q252))).trans (cg (fun t => t ◇ (q251 ◇ q252)) (apc291 q250 q251))).trans (apc350 (((q250 ◇ q250) ◇ q251) ◇ (q251 ◇ q252)) (((q250 ◇ q250) ◇ q251) ◇ (q251 ◇ q252)) (((q250 ◇ q250) ◇ q251) ◇ (q251 ◇ q252)) q250 q252 q251)))).symm
  have apc354 : forall (q197 q198 q199 q250 q251 q252 : G), (((q198 ◇ q197) ◇ q198) ◇ q199)=((q197 ◇ q197) ◇ (q198 ◇ q199)):=by
    intro q197 q198 q199 q250 q251 q252
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc250 q197 q198 q199).trans (apc352 q197 q198 q199))).trans (rfl))
  have apc355 : forall (q221 q222 q223 q250 q251 q252 : G), (((q221 ◇ q221) ◇ q222) ◇ q223)=((q221 ◇ q221) ◇ (q222 ◇ q223)):=by
    intro q221 q222 q223 q250 q251 q252
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc292 q221 q222 q223).trans (apc352 q221 q222 q223))).trans (rfl))
  have apc356 : forall (q253 q254 q255 : G), (((q253 ◇ q253) ◇ (q254 ◇ q255)) ◇ q254)=((q253 ◇ q253) ◇ (q254 ◇ q255)):=by
    intro q253 q254 q255
    exact ((((cg (fun t => t ◇ q255) (apc259 ((q253 ◇ q254) ◇ q254) ((q253 ◇ q254) ◇ q254) ((q253 ◇ q254) ◇ q254) ((q253 ◇ q254) ◇ q254) ((q253 ◇ q254) ◇ q254) ((q253 ◇ q254) ◇ q254) ((q253 ◇ q254) ◇ q254) ((q253 ◇ q254) ◇ q254) ((q253 ◇ q254) ◇ q254) ((q253 ◇ q254) ◇ q254) ((q253 ◇ q254) ◇ q254) ((q253 ◇ q254) ◇ q254) ((q253 ◇ q254) ◇ q254) q253 q254 ((q253 ◇ q254) ◇ q254) ((q253 ◇ q254) ◇ q254) ((q253 ◇ q254) ◇ q254) ((q253 ◇ q254) ◇ q254) ((q253 ◇ q254) ◇ q254) ((q253 ◇ q254) ◇ q254) ((q253 ◇ q254) ◇ q254) ((q253 ◇ q254) ◇ q254) ((q253 ◇ q254) ◇ q254) ((q253 ◇ q254) ◇ q254) ((q253 ◇ q254) ◇ q254) ((q253 ◇ q254) ◇ q254))).trans (apc355 q253 q254 q255 (((q253 ◇ q253) ◇ q254) ◇ q255) (((q253 ◇ q253) ◇ q254) ◇ q255) (((q253 ◇ q253) ◇ q254) ◇ q255))).symm).trans ((((cg (fun t => t ◇ q255) ((h q253 q254 q254).symm)).symm).trans (apc355 q254 (q254 ◇ q253) q255 q253 q253 q253)).trans (((apc333 q254 q253 q255 q254).trans (cg (fun t => t ◇ q254) (apc343 q253 q254 q255))).trans (cg (fun t => t ◇ q254) (apc352 q253 q254 q255))))).symm
  have apc361 : forall (q224 q225 q226 q250 q251 q252 : G), (((q224 ◇ q224) ◇ (q225 ◇ q226)) ◇ q226)=((q224 ◇ q224) ◇ (q225 ◇ q226)):=by
    intro q224 q225 q226 q250 q251 q252
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q226) (apc352 q224 q225 q226)).symm).trans ((apc316 q224 q225 q226).trans (apc352 q224 q225 q226))).trans (rfl))
  have apc367 : forall (q227 q228 q229 q250 q251 q252 : G), (((q227 ◇ q227) ◇ q228) ◇ (q229 ◇ (q227 ◇ q228)))=((q227 ◇ q227) ◇ (q228 ◇ q229)):=by
    intro q227 q228 q229 q250 q251 q252
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc324 q227 q228 q229).trans (apc352 q227 q228 q229))).trans (rfl))
  have apc369 : forall (q213 q214 q215 q221 q222 q223 q250 q251 q252 : G), ((q214 ◇ (q213 ◇ q214)) ◇ q215)=((q213 ◇ q213) ◇ (q214 ◇ q215)):=by
    intro q213 q214 q215 q221 q222 q223 q250 q251 q252
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc328 q213 q214 q215 q213 q213 q213).trans (apc352 q213 q214 q215))).trans (rfl))
  have apc375 : forall (q256 q257 q258 q259 : G), (((q257 ◇ q256) ◇ q257) ◇ (q258 ◇ q259))=(((q256 ◇ q256) ◇ (q257 ◇ q259)) ◇ q258):=by
    intro q256 q257 q258 q259
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (q258 ◇ q259)) ((h q257 q256 q257).symm)).symm).trans (apc352 q258 q259 (q256 ◇ q257))).trans (((apc343 (q256 ◇ q257) q259 q258).trans (apc333 q256 q257 q259 q258)).trans (cg (fun t => t ◇ q258) (apc352 q256 q257 q259))))
  have apc376 : forall (q260 q261 q262 q263 : G), (((q261 ◇ q261) ◇ (q262 ◇ q263)) ◇ q260)=(((q260 ◇ q260) ◇ (q261 ◇ q263)) ◇ q262):=by
    intro q260 q261 q262 q263
    exact ((((cg (fun t => t ◇ q260) (apc343 q261 q263 q262)).trans (cg (fun t => t ◇ q260) (apc352 q261 q263 q262))).trans (cg (fun t => t ◇ q260) (apc343 q262 q263 q261))).symm).trans ((((apc375 q262 q263 q260 q261).symm).trans (apc354 q262 q263 (q260 ◇ q261) q260 q260 q260)).trans (((apc343 (q260 ◇ q261) q263 q262).trans (apc333 q260 q261 q263 q262)).trans (cg (fun t => t ◇ q262) (apc352 q260 q261 q263))))
  have apc377 : forall (q264 q265 q266 : G), (((q266 ◇ q265) ◇ q265) ◇ q264)=((q264 ◇ q264) ◇ (q265 ◇ q266)):=by
    intro q264 q265 q266
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q264) ((h q266 q265 q265).symm)).symm).trans (apc376 q264 q265 q265 q266)).trans (apc356 q264 q265 q266))
  exact ((((((((((((((((h x y z).trans (h y z (y ◇ x))).trans (h z (y ◇ x) (z ◇ y))).trans (cg (fun t => t ◇ ((y ◇ x) ◇ z)) (h y x (z ◇ y)))).trans ((apc1 (z ◇ y) x y ((y ◇ x) ◇ z)).symm)).trans ((apc45 y x z (x ◇ y) (((z ◇ y) ◇ x) ◇ y)).symm)).trans (apc369 (x ◇ z) (x ◇ y) (((z ◇ y) ◇ x) ◇ y) x x x x x x)).trans (cg (fun t => t ◇ ((x ◇ y) ◇ (((z ◇ y) ◇ x) ◇ y))) (apc290 x z x x x))).trans (cg (fun t => t ◇ ((x ◇ y) ◇ (((z ◇ y) ◇ x) ◇ y))) ((apc259 x x x x x x x x x x x x x x z x x x x x x x x x x x x).symm))).trans (cg (fun t => ((x ◇ z) ◇ z) ◇ t) (apc349 ((z ◇ y) ◇ x) x y))).trans (cg (fun t => ((x ◇ z) ◇ z) ◇ t) (apc333 (z ◇ y) x y x))).trans (cg (fun t => ((x ◇ z) ◇ z) ◇ t) (apc361 y (z ◇ y) x x x x))).trans (cg (fun t => ((x ◇ z) ◇ z) ◇ t) (apc333 z y x y))).trans (cg (fun t => ((x ◇ z) ◇ z) ◇ t) (apc361 x z y x x x))).trans (cg (fun t => ((x ◇ z) ◇ z) ◇ t) ((apc352 x z y).symm))).trans (cg (fun t => t ◇ ((y ◇ y) ◇ (x ◇ z))) (apc259 x x x x x x x x x x x x x x z x x x x x x x x x x x x))).trans (((((apc377 y z x).trans ((apc352 y z x).symm)).trans ((apc329 y z x).symm)).trans ((apc367 x z (y ◇ y) x x x).symm)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_60566_to_62248 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_60566_to_62248
