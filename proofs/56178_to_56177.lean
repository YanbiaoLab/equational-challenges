-- Equation56178 → Equation56177
-- Recorded verdict: true
-- Premise: x ◇ (y ◇ z) = (y ◇ z) ◇ (x ◇ y)
-- Conclusion: x ◇ (y ◇ z) = (y ◇ z) ◇ (x ◇ x)
-- Original submission SHA-256: f1ee3591344215317571734c459ed884932648704653505ad5950aa4828a29fd
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ z) = (y ◇ z) ◇ (x ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ z) = (y ◇ z) ◇ (x ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f : G → G) {a b : G}, a=b → f a=f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1 q2 q3 : G), (((q0 ◇ q1) ◇ q3) ◇ (q0 ◇ (q1 ◇ q2)))=((q1 ◇ q2) ◇ ((q0 ◇ q1) ◇ q3)):=by
    intro q0 q1 q2 q3
    exact ((rfl).symm).trans ((((cg (fun t => ((q0 ◇ q1) ◇ q3) ◇ t) ((h q0 q1 q2).symm)).symm).trans ((h (q1 ◇ q2) (q0 ◇ q1) q3).symm)).trans (rfl))
  have apc1 : forall (q4 q5 : G), ((q4 ◇ q4) ◇ ((q4 ◇ q4) ◇ q5))=(q4 ◇ ((q4 ◇ q4) ◇ q5)):=by
    intro q4 q5
    exact ((rfl).symm).trans ((((apc0 q4 q4 q4 q5).symm).trans ((h q4 (q4 ◇ q4) q5).symm)).trans (rfl))
  have apc8 : forall (q6 q7 q8 q9 q10 : G), (q9 ◇ (q10 ◇ ((q7 ◇ q8) ◇ (q6 ◇ q7))))=((q10 ◇ (q6 ◇ (q7 ◇ q8))) ◇ (q9 ◇ q10)):=by
    intro q6 q7 q8 q9 q10
    exact (((rfl).symm).trans ((((cg (fun t => t ◇ (q9 ◇ q10)) (cg (fun t => q10 ◇ t) ((h q6 q7 q8).symm))).symm).trans ((h q9 q10 ((q7 ◇ q8) ◇ (q6 ◇ q7))).symm)).trans (rfl))).symm
  have apc9 : forall (q11 q12 q13 q14 q15 : G), ((q15 ◇ (q11 ◇ (q12 ◇ q13))) ◇ (q14 ◇ q15))=(q14 ◇ (q15 ◇ (q11 ◇ (q12 ◇ q13)))):=by
    intro q11 q12 q13 q14 q15
    exact (((rfl).symm).trans ((((cg (fun t => q14 ◇ t) (cg (fun t => q15 ◇ t) ((h q11 q12 q13).symm))).symm).trans (apc8 q11 q12 q13 q14 q15)).trans (rfl))).symm
  have apc11 : forall (q0 q1 q2 q16 : G), ((q0 ◇ (q1 ◇ q2)) ◇ (q16 ◇ (q1 ◇ q2)))=(q16 ◇ ((q1 ◇ q2) ◇ (q0 ◇ q1))):=by
    intro q0 q1 q2 q16
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (q16 ◇ (q1 ◇ q2))) ((h q0 q1 q2).symm)).symm).trans ((h q16 (q1 ◇ q2) (q0 ◇ q1)).symm)).trans (rfl))
  have apc12 : forall (q6 q7 q8 q10 q17 : G), ((q10 ◇ q17) ◇ ((q6 ◇ (q7 ◇ q8)) ◇ q10))=(((q7 ◇ q8) ◇ (q6 ◇ q7)) ◇ (q10 ◇ q17)):=by
    intro q6 q7 q8 q10 q17
    exact ((rfl).symm).trans ((((cg (fun t => (q10 ◇ q17) ◇ t) (cg (fun t => t ◇ q10) ((h q6 q7 q8).symm))).symm).trans ((h ((q7 ◇ q8) ◇ (q6 ◇ q7)) q10 q17).symm)).trans (rfl))
  have apc13 : forall (q18 q19 q20 q21 q22 : G), (((q19 ◇ q20) ◇ (q18 ◇ q19)) ◇ (q21 ◇ q22))=((q18 ◇ (q19 ◇ q20)) ◇ (q21 ◇ q22)):=by
    intro q18 q19 q20 q21 q22
    exact ((rfl).symm).trans ((((apc12 q18 q19 q20 q21 q22).symm).trans ((h (q18 ◇ (q19 ◇ q20)) q21 q22).symm)).trans (rfl))
  have apc21 : forall (q23 q24 q25 q26 : G), ((q25 ◇ q26) ◇ ((q24 ◇ q25) ◇ (q23 ◇ q24)))=((q23 ◇ (q24 ◇ q25)) ◇ (q24 ◇ (q25 ◇ q26))):=by
    intro q23 q24 q25 q26
    exact (((rfl).symm).trans ((((cg (fun t => t ◇ (q24 ◇ (q25 ◇ q26))) ((h q23 q24 q25).symm)).symm).trans (apc0 q24 q25 q26 (q23 ◇ q24))).trans (rfl))).symm
  have apc22 : forall (q27 q28 q29 q30 : G), ((q27 ◇ (q28 ◇ q29)) ◇ (q28 ◇ (q29 ◇ q30)))=((q29 ◇ q30) ◇ (q27 ◇ (q28 ◇ q29))):=by
    intro q27 q28 q29 q30
    exact (((rfl).symm).trans ((((cg (fun t => (q29 ◇ q30) ◇ t) ((h q27 q28 q29).symm)).symm).trans (apc21 q27 q28 q29 q30)).trans (rfl))).symm
  have apc23 : forall (q23 q24 q25 q26 q27 q28 q29 q30 : G), ((q25 ◇ q26) ◇ ((q24 ◇ q25) ◇ (q23 ◇ q24)))=((q25 ◇ q26) ◇ (q23 ◇ (q24 ◇ q25))):=by
    intro q23 q24 q25 q26 q27 q28 q29 q30
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc21 q23 q24 q25 q26).trans (apc22 q23 q24 q25 q26))).trans (rfl))
  have apc24 : forall (q31 q32 q33 : G), ((q31 ◇ q32) ◇ ((q31 ◇ q32) ◇ (q33 ◇ q31)))=(q33 ◇ ((q31 ◇ q32) ◇ (q33 ◇ q31))):=by
    intro q31 q32 q33
    exact ((rfl).symm).trans ((((apc22 (q31 ◇ q32) q33 q31 q32).symm).trans ((h q33 (q31 ◇ q32) (q33 ◇ q31)).symm)).trans (rfl))
  have apc25 : forall (q34 q35 q36 : G), (q36 ◇ ((q34 ◇ q35) ◇ (q36 ◇ q34)))=((q34 ◇ q35) ◇ (q36 ◇ (q34 ◇ q35))):=by
    intro q34 q35 q36
    exact (((rfl).symm).trans ((((cg (fun t => (q34 ◇ q35) ◇ t) ((h q36 q34 q35).symm)).symm).trans (apc24 q34 q35 q36)).trans (rfl))).symm
  have apc26 : forall (q37 q38 q39 : G), ((q37 ◇ q38) ◇ (q39 ◇ (q37 ◇ q38)))=(q39 ◇ (q39 ◇ (q37 ◇ q38))):=by
    intro q37 q38 q39
    exact (((rfl).symm).trans ((((cg (fun t => q39 ◇ t) ((h q39 q37 q38).symm)).symm).trans (apc25 q37 q38 q39)).trans (rfl))).symm
  have apc32 : forall (q34 q35 q36 q37 q38 q39 : G), (q36 ◇ ((q34 ◇ q35) ◇ (q36 ◇ q34)))=(q36 ◇ (q36 ◇ (q34 ◇ q35))):=by
    intro q34 q35 q36 q37 q38 q39
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc25 q34 q35 q36).trans (apc26 q34 q35 q36))).trans (rfl))
  have apc35 : forall (q34 q35 q36 q31 q32 q33 : G), ((q31 ◇ q32) ◇ ((q31 ◇ q32) ◇ (q33 ◇ q31)))=(q33 ◇ (q33 ◇ (q31 ◇ q32))):=by
    intro q34 q35 q36 q31 q32 q33
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc24 q31 q32 q33).trans (apc25 q31 q32 q33))).trans (apc26 q31 q32 q33))
  have apc36 : forall (q40 q41 q42 : G), ((q41 ◇ q42) ◇ (q41 ◇ (q42 ◇ q40)))=(q41 ◇ (q41 ◇ (q42 ◇ q40))):=by
    intro q40 q41 q42
    exact ((rfl).symm).trans ((((cg (fun t => (q41 ◇ q42) ◇ t) ((h q41 q42 q40).symm)).symm).trans (apc26 q41 q42 (q42 ◇ q40))).trans (apc35 ((q42 ◇ q40) ◇ ((q42 ◇ q40) ◇ (q41 ◇ q42))) ((q42 ◇ q40) ◇ ((q42 ◇ q40) ◇ (q41 ◇ q42))) ((q42 ◇ q40) ◇ ((q42 ◇ q40) ◇ (q41 ◇ q42))) q42 q40 q41))
  have apc58 : forall (q43 q44 q45 q46 : G), (q46 ◇ ((q44 ◇ q45) ◇ ((q45 ◇ q43) ◇ q44)))=((q44 ◇ (q45 ◇ q43)) ◇ (q46 ◇ (q44 ◇ q45))):=by
    intro q43 q44 q45 q46
    exact (((rfl).symm).trans ((((cg (fun t => t ◇ (q46 ◇ (q44 ◇ q45))) ((h q44 q45 q43).symm)).symm).trans (apc11 (q45 ◇ q43) q44 q45 q46)).trans (rfl))).symm
  have apc59 : forall (q47 q48 q49 q50 : G), ((q48 ◇ (q49 ◇ q47)) ◇ (q50 ◇ (q48 ◇ q49)))=(q50 ◇ ((q49 ◇ q47) ◇ (q48 ◇ q49))):=by
    intro q47 q48 q49 q50
    exact (((rfl).symm).trans ((((cg (fun t => q50 ◇ t) ((h (q49 ◇ q47) q48 q49).symm)).symm).trans (apc58 q47 q48 q49 q50)).trans (rfl))).symm
  have apc60 : forall (q11 q12 q13 q14 q15 q6 q7 q8 q9 q10 : G), (q9 ◇ (q10 ◇ ((q7 ◇ q8) ◇ (q6 ◇ q7))))=(q9 ◇ (q10 ◇ (q6 ◇ (q7 ◇ q8)))):=by
    intro q11 q12 q13 q14 q15 q6 q7 q8 q9 q10
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc8 q6 q7 q8 q9 q10).trans (apc9 q6 q7 q8 q9 q10))).trans (rfl))
  have apc62 : forall (q51 q52 q53 q54 : G), ((q53 ◇ q54) ◇ ((q53 ◇ q51) ◇ (q52 ◇ q53)))=((q52 ◇ (q53 ◇ q51)) ◇ (q52 ◇ (q53 ◇ q54))):=by
    intro q51 q52 q53 q54
    exact (((rfl).symm).trans ((((cg (fun t => t ◇ (q52 ◇ (q53 ◇ q54))) ((h q52 q53 q51).symm)).symm).trans (apc22 (q53 ◇ q51) q52 q53 q54)).trans (rfl))).symm
  have apc63 : forall (q55 q56 q57 q58 : G), ((q56 ◇ (q57 ◇ q55)) ◇ (q56 ◇ (q57 ◇ q58)))=((q57 ◇ q58) ◇ (q56 ◇ (q57 ◇ q55))):=by
    intro q55 q56 q57 q58
    exact (((rfl).symm).trans ((((cg (fun t => (q57 ◇ q58) ◇ t) ((h q56 q57 q55).symm)).symm).trans (apc62 q55 q56 q57 q58)).trans (rfl))).symm
  have apc65 : forall (q51 q52 q53 q54 q55 q56 q57 q58 : G), ((q53 ◇ q54) ◇ ((q53 ◇ q51) ◇ (q52 ◇ q53)))=((q53 ◇ q54) ◇ (q52 ◇ (q53 ◇ q51))):=by
    intro q51 q52 q53 q54 q55 q56 q57 q58
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc62 q51 q52 q53 q54).trans (apc63 q51 q52 q53 q54))).trans (rfl))
  have apc71 : forall (q59 q60 q61 : G), (((q60 ◇ q59) ◇ q61) ◇ (q61 ◇ (q60 ◇ q59)))=(q61 ◇ (q61 ◇ (q60 ◇ q59))):=by
    intro q59 q60 q61
    exact ((rfl).symm).trans ((((cg (fun t => ((q60 ◇ q59) ◇ q61) ◇ t) ((h q61 q60 q59).symm)).symm).trans (apc36 q60 (q60 ◇ q59) q61)).trans ((apc65 q59 q61 q60 q59 ((q60 ◇ q59) ◇ ((q60 ◇ q59) ◇ (q61 ◇ q60))) ((q60 ◇ q59) ◇ ((q60 ◇ q59) ◇ (q61 ◇ q60))) ((q60 ◇ q59) ◇ ((q60 ◇ q59) ◇ (q61 ◇ q60))) ((q60 ◇ q59) ◇ ((q60 ◇ q59) ◇ (q61 ◇ q60)))).trans (apc26 q60 q59 q61)))
  have apc72 : forall (q62 q63 q64 : G), (q64 ◇ (q64 ◇ (q63 ◇ q62)))=(q64 ◇ ((q63 ◇ q62) ◇ q64)):=by
    intro q62 q63 q64
    exact ((rfl).symm).trans ((((apc71 q62 q63 q64).symm).trans ((h q64 (q63 ◇ q62) q64).symm)).trans (rfl))
  have apc73 : forall (q37 q38 q39 q62 q63 q64 : G), ((q37 ◇ q38) ◇ (q39 ◇ (q37 ◇ q38)))=(q39 ◇ ((q37 ◇ q38) ◇ q39)):=by
    intro q37 q38 q39 q62 q63 q64
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc26 q37 q38 q39).trans (apc72 q38 q37 q39))).trans (rfl))
  have apc74 : forall (q40 q41 q42 q62 q63 q64 : G), ((q41 ◇ q42) ◇ (q41 ◇ (q42 ◇ q40)))=(q41 ◇ ((q42 ◇ q40) ◇ q41)):=by
    intro q40 q41 q42 q62 q63 q64
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc36 q40 q41 q42).trans (apc72 q40 q42 q41))).trans (rfl))
  have apc94 : forall (q65 q66 q67 : G), ((q66 ◇ q65) ◇ ((q67 ◇ q66) ◇ (q66 ◇ q65)))=(q67 ◇ ((q66 ◇ q65) ◇ q67)):=by
    intro q65 q66 q67
    exact (((apc73 q66 q65 q67 ((q66 ◇ q65) ◇ (q67 ◇ (q66 ◇ q65))) ((q66 ◇ q65) ◇ (q67 ◇ (q66 ◇ q65))) ((q66 ◇ q65) ◇ (q67 ◇ (q66 ◇ q65)))).symm).trans ((((cg (fun t => (q66 ◇ q65) ◇ t) ((h q67 q66 q65).symm)).symm).trans (apc72 q66 q67 (q66 ◇ q65))).trans (rfl))).symm
  have apc95 : forall (q68 q69 : G), (q69 ◇ ((q68 ◇ q69) ◇ q69))=(q68 ◇ ((q69 ◇ q68) ◇ q68)):=by
    intro q68 q69
    exact ((apc74 q69 q69 q68 ((q69 ◇ q68) ◇ (q69 ◇ (q68 ◇ q69))) ((q69 ◇ q68) ◇ (q69 ◇ (q68 ◇ q69))) ((q69 ◇ q68) ◇ (q69 ◇ (q68 ◇ q69)))).symm).trans ((((cg (fun t => (q69 ◇ q68) ◇ t) ((h q69 q68 q69).symm)).symm).trans (apc94 q68 q69 q68)).trans (rfl))
  have apc96 : forall (q70 q71 q72 : G), ((q70 ◇ q71) ◇ ((q71 ◇ q72) ◇ (q70 ◇ q71)))=(q70 ◇ ((q71 ◇ q72) ◇ q70)):=by
    intro q70 q71 q72
    exact (((rfl).symm).trans ((((apc94 q72 q71 q70).symm).trans (apc73 q71 q72 (q70 ◇ q71) q70 q70 q70)).trans (rfl))).symm
  have apc104 : forall (q73 q74 q75 : G), ((q74 ◇ q73) ◇ ((q75 ◇ q75) ◇ (q74 ◇ q73)))=(q75 ◇ ((q75 ◇ q75) ◇ (q74 ◇ q73))):=by
    intro q73 q74 q75
    exact ((apc73 q75 q75 (q74 ◇ q73) ((q75 ◇ q75) ◇ ((q74 ◇ q73) ◇ (q75 ◇ q75))) ((q75 ◇ q75) ◇ ((q74 ◇ q73) ◇ (q75 ◇ q75))) ((q75 ◇ q75) ◇ ((q74 ◇ q73) ◇ (q75 ◇ q75)))).symm).trans ((((apc72 q73 q74 (q75 ◇ q75)).symm).trans (apc1 q75 (q74 ◇ q73))).trans (rfl))
  have apc106 : forall (q76 q77 q78 : G), ((q76 ◇ q76) ◇ ((q77 ◇ q78) ◇ (q76 ◇ q76)))=(q76 ◇ ((q76 ◇ q76) ◇ (q77 ◇ q78))):=by
    intro q76 q77 q78
    exact (((rfl).symm).trans ((((apc104 q78 q77 q76).symm).trans (apc73 q77 q78 (q76 ◇ q76) q76 q76 q76)).trans (rfl))).symm
  have apc107 : forall (q79 q80 q81 : G), (q81 ◇ ((q81 ◇ (q80 ◇ q79)) ◇ q81))=(q81 ◇ (((q80 ◇ q79) ◇ q81) ◇ q81)):=by
    intro q79 q80 q81
    exact (((apc72 q81 (q80 ◇ q79) q81).symm).trans ((((cg (fun t => q81 ◇ t) (apc72 q79 q80 q81)).symm).trans (apc72 (q80 ◇ q79) q81 q81)).trans (rfl))).symm
  have apc112 : forall (q23 q82 q83 q24 q84 : G), (((q24 ◇ (q82 ◇ q83)) ◇ q84) ◇ (q24 ◇ (q23 ◇ (q82 ◇ q83))))=((q23 ◇ (q82 ◇ q83)) ◇ ((q24 ◇ (q82 ◇ q83)) ◇ q84)):=by
    intro q23 q82 q83 q24 q84
    exact ((rfl).symm).trans ((((cg (fun t => ((q24 ◇ (q82 ◇ q83)) ◇ q84) ◇ t) (cg (fun t => q24 ◇ t) ((h q23 q82 q83).symm))).symm).trans (apc0 q24 (q82 ◇ q83) (q23 ◇ q82) q84)).trans (apc13 q23 q82 q83 (q24 ◇ (q82 ◇ q83)) q84))
  have apc113 : forall (q85 q86 q87 q88 : G), ((q87 ◇ (q85 ◇ q86)) ◇ ((q87 ◇ (q85 ◇ q86)) ◇ q88))=(q87 ◇ ((q87 ◇ (q85 ◇ q86)) ◇ q88)):=by
    intro q85 q86 q87 q88
    exact ((rfl).symm).trans ((((apc112 q87 q85 q86 q87 q88).symm).trans ((h q87 (q87 ◇ (q85 ◇ q86)) q88).symm)).trans (rfl))
  have apc114 : forall (q89 q90 q91 : G), (q91 ◇ (((q89 ◇ q90) ◇ q91) ◇ q91))=(q91 ◇ ((q89 ◇ q90) ◇ q91)):=by
    intro q89 q90 q91
    exact ((apc107 q90 q89 q91).symm).trans ((((apc113 q89 q90 q91 q91).symm).trans ((h (q91 ◇ (q89 ◇ q90)) q91 (q89 ◇ q90)).symm)).trans (((apc11 q91 q89 q90 q91).trans (apc32 q89 q90 q91 (q91 ◇ ((q89 ◇ q90) ◇ (q91 ◇ q89))) (q91 ◇ ((q89 ◇ q90) ◇ (q91 ◇ q89))) (q91 ◇ ((q89 ◇ q90) ◇ (q91 ◇ q89))))).trans (apc72 q90 q89 q91)))
  have apc136 : forall (q92 q93 q65 q94 : G), (q94 ◇ (((q93 ◇ q65) ◇ (q92 ◇ q93)) ◇ q94))=(q94 ◇ ((q92 ◇ (q93 ◇ q65)) ◇ q94)):=by
    intro q92 q93 q65 q94
    exact (((apc72 (q93 ◇ q65) q92 q94).symm).trans ((((cg (fun t => q94 ◇ t) (cg (fun t => q94 ◇ t) ((h q92 q93 q65).symm))).symm).trans (apc72 (q92 ◇ q93) (q93 ◇ q65) q94)).trans (rfl))).symm
  have apc167 : forall (q95 q96 q59 q97 : G), ((q97 ◇ (q96 ◇ q59)) ◇ (q97 ◇ (q95 ◇ (q96 ◇ q59))))=(q97 ◇ ((q95 ◇ (q96 ◇ q59)) ◇ q97)):=by
    intro q95 q96 q59 q97
    exact ((rfl).symm).trans ((((cg (fun t => (q97 ◇ (q96 ◇ q59)) ◇ t) (cg (fun t => q97 ◇ t) ((h q95 q96 q59).symm))).symm).trans (apc36 (q95 ◇ q96) q97 (q96 ◇ q59))).trans ((apc60 (q97 ◇ (q97 ◇ ((q96 ◇ q59) ◇ (q95 ◇ q96)))) (q97 ◇ (q97 ◇ ((q96 ◇ q59) ◇ (q95 ◇ q96)))) (q97 ◇ (q97 ◇ ((q96 ◇ q59) ◇ (q95 ◇ q96)))) (q97 ◇ (q97 ◇ ((q96 ◇ q59) ◇ (q95 ◇ q96)))) (q97 ◇ (q97 ◇ ((q96 ◇ q59) ◇ (q95 ◇ q96)))) q95 q96 q59 q97 q97).trans (apc72 (q96 ◇ q59) q95 q97)))
  have apc267 : forall (q98 q99 q100 q101 : G), (q101 ◇ ((q99 ◇ (q100 ◇ q98)) ◇ q101))=(q101 ◇ ((q100 ◇ q98) ◇ (q99 ◇ q100))):=by
    intro q98 q99 q100 q101
    exact ((((apc63 q100 q101 q99 (q100 ◇ q98)).trans (apc59 q98 q99 q100 q101)).symm).trans ((((cg (fun t => (q101 ◇ (q99 ◇ q100)) ◇ t) (cg (fun t => q101 ◇ t) ((h q99 q100 q98).symm))).symm).trans (apc167 (q100 ◇ q98) q99 q100 q101)).trans (apc136 q99 q100 q98 q101))).symm
  have apc268 : forall (q102 q103 q104 q105 : G), ((q104 ◇ q105) ◇ ((q103 ◇ q102) ◇ (q105 ◇ q103)))=(q104 ◇ ((q103 ◇ q102) ◇ (q105 ◇ q103))):=by
    intro q102 q103 q104 q105
    exact ((rfl).symm).trans ((((apc267 q102 q105 q103 (q104 ◇ q105)).symm).trans (apc96 q104 q105 (q103 ◇ q102))).trans (apc267 q102 q105 q103 q104))
  have apc269 : forall (q106 q107 q108 q109 : G), (q108 ◇ ((q107 ◇ q106) ◇ (q109 ◇ q107)))=((q108 ◇ q109) ◇ (q109 ◇ (q107 ◇ q106))):=by
    intro q106 q107 q108 q109
    exact (((rfl).symm).trans ((((cg (fun t => (q108 ◇ q109) ◇ t) ((h q109 q107 q106).symm)).symm).trans (apc268 q106 q107 q108 q109)).trans (rfl))).symm
  have apc270 : forall (q110 q111 q112 q113 : G), ((q112 ◇ q113) ◇ (q113 ◇ (q111 ◇ q110)))=(q112 ◇ (q113 ◇ (q111 ◇ q110))):=by
    intro q110 q111 q112 q113
    exact (((rfl).symm).trans ((((cg (fun t => q112 ◇ t) ((h q113 q111 q110).symm)).symm).trans (apc269 q110 q111 q112 q113)).trans (rfl))).symm
  have apc274 : forall (q98 q99 q100 q101 q106 q107 q108 q109 : G), (q101 ◇ ((q99 ◇ (q100 ◇ q98)) ◇ q101))=(q101 ◇ (q99 ◇ (q100 ◇ q98))):=by
    intro q98 q99 q100 q101 q106 q107 q108 q109
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc267 q98 q99 q100 q101).trans (apc269 q98 q100 q101 q99))).trans (apc270 q98 q100 q101 q99))
  have apc275 : forall (q114 q115 q116 : G), (q116 ◇ ((q115 ◇ q116) ◇ (q114 ◇ q115)))=(q116 ◇ (q114 ◇ (q115 ◇ q116))):=by
    intro q114 q115 q116
    exact ((rfl).symm).trans ((((apc268 q116 q115 q116 q114).symm).trans (apc23 q114 q115 q116 q114 q114 q114 q114 q114)).trans (apc270 q116 q115 q116 q114))
  have apc276 : forall (q117 q118 : G), (q117 ◇ (q118 ◇ (q117 ◇ q118)))=(q117 ◇ ((q118 ◇ q117) ◇ q117)):=by
    intro q117 q118
    exact (((apc74 (q117 ◇ q118) q117 q118 ((q117 ◇ q118) ◇ (q117 ◇ (q118 ◇ (q117 ◇ q118)))) ((q117 ◇ q118) ◇ (q117 ◇ (q118 ◇ (q117 ◇ q118)))) ((q117 ◇ q118) ◇ (q117 ◇ (q118 ◇ (q117 ◇ q118))))).trans (apc274 q118 q118 q117 q117 (q117 ◇ ((q118 ◇ (q117 ◇ q118)) ◇ q117)) (q117 ◇ ((q118 ◇ (q117 ◇ q118)) ◇ q117)) (q117 ◇ ((q118 ◇ (q117 ◇ q118)) ◇ q117)) (q117 ◇ ((q118 ◇ (q117 ◇ q118)) ◇ q117)))).symm).trans ((((apc275 q117 q118 (q117 ◇ q118)).symm).trans (apc95 q118 (q117 ◇ q118))).trans ((apc114 q117 q118 q118).trans (apc95 q117 q118)))
  have apc278 : forall (q106 q107 q108 q109 q110 q111 q112 q113 : G), (q108 ◇ ((q107 ◇ q106) ◇ (q109 ◇ q107)))=(q108 ◇ (q109 ◇ (q107 ◇ q106))):=by
    intro q106 q107 q108 q109 q110 q111 q112 q113
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc269 q106 q107 q108 q109).trans (apc270 q106 q107 q108 q109))).trans (rfl))
  have apc279 : forall (q0 q1 q2 q16 q106 q107 q108 q109 : G), ((q0 ◇ (q1 ◇ q2)) ◇ (q16 ◇ (q1 ◇ q2)))=(q16 ◇ (q0 ◇ (q1 ◇ q2))):=by
    intro q0 q1 q2 q16 q106 q107 q108 q109
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc11 q0 q1 q2 q16).trans (apc269 q2 q1 q16 q0))).trans (apc270 q2 q1 q16 q0))
  have apc285 : forall (q119 q120 q121 q122 : G), (((q120 ◇ q119) ◇ q121) ◇ (q122 ◇ (q120 ◇ q119)))=(q122 ◇ (((q120 ◇ q119) ◇ q121) ◇ q122)):=by
    intro q119 q120 q121 q122
    exact ((rfl).symm).trans ((((apc274 q119 q122 q120 ((q120 ◇ q119) ◇ q121) q119 q119 q119 q119).symm).trans (apc94 q121 (q120 ◇ q119) q122)).trans (rfl))
  have apc286 : forall (q123 q124 q125 q126 : G), (q125 ◇ (((q124 ◇ q123) ◇ q126) ◇ q125))=(q125 ◇ ((q124 ◇ q123) ◇ q126)):=by
    intro q123 q124 q125 q126
    exact ((rfl).symm).trans ((((apc285 q123 q124 q126 q125).symm).trans ((h q125 (q124 ◇ q123) q126).symm)).trans (rfl))
  have apc288 : forall (q127 q128 q129 q130 : G), (q129 ◇ ((q129 ◇ q129) ◇ ((q128 ◇ q127) ◇ q130)))=((q129 ◇ q129) ◇ ((q128 ◇ q127) ◇ q130)):=by
    intro q127 q128 q129 q130
    exact (((rfl).symm).trans ((((apc286 q127 q128 (q129 ◇ q129) q130).symm).trans (apc106 q129 (q128 ◇ q127) q130)).trans (rfl))).symm
  have apc289 : forall (q131 q132 q133 : G), (q133 ◇ ((q132 ◇ q131) ◇ (q133 ◇ q133)))=((q133 ◇ q133) ◇ ((q132 ◇ q131) ◇ q133)):=by
    intro q131 q132 q133
    exact ((rfl).symm).trans ((((cg (fun t => q133 ◇ t) ((h (q132 ◇ q131) q133 q133).symm)).symm).trans (apc288 q131 q132 q133 q133)).trans (rfl))
  have apc292 : forall (q134 q135 q136 q137 : G), (q137 ◇ (q136 ◇ (q135 ◇ q134)))=(q136 ◇ (q137 ◇ (q135 ◇ q134))):=by
    intro q134 q135 q136 q137
    exact (((apc279 q137 q135 q134 q136 ((q137 ◇ (q135 ◇ q134)) ◇ (q136 ◇ (q135 ◇ q134))) ((q137 ◇ (q135 ◇ q134)) ◇ (q136 ◇ (q135 ◇ q134))) ((q137 ◇ (q135 ◇ q134)) ◇ (q136 ◇ (q135 ◇ q134))) ((q137 ◇ (q135 ◇ q134)) ◇ (q136 ◇ (q135 ◇ q134)))).symm).trans ((((cg (fun t => (q137 ◇ (q135 ◇ q134)) ◇ t) ((h q136 q135 q134).symm)).symm).trans (apc270 q135 q136 q137 (q135 ◇ q134))).trans (apc278 q134 q135 q137 q136 (q137 ◇ ((q135 ◇ q134) ◇ (q136 ◇ q135))) (q137 ◇ ((q135 ◇ q134) ◇ (q136 ◇ q135))) (q137 ◇ ((q135 ◇ q134) ◇ (q136 ◇ q135))) (q137 ◇ ((q135 ◇ q134) ◇ (q136 ◇ q135)))))).symm
  have apc293 : forall (q106 q107 q108 q109 q110 q111 q112 q113 q134 q135 q136 q137 : G), ((q107 ◇ q106) ◇ (q108 ◇ (q109 ◇ q107)))=(q108 ◇ (q109 ◇ (q107 ◇ q106))):=by
    intro q106 q107 q108 q109 q110 q111 q112 q113 q134 q135 q136 q137
    exact ((rfl).symm).trans ((((apc292 q107 q109 (q107 ◇ q106) q108).symm).trans ((apc278 q106 q107 q108 q109 q106 q106 q106 q106).trans (rfl))).trans (rfl))
  have apc295 : forall (q138 q139 q140 : G), (q139 ◇ (q140 ◇ (q138 ◇ q140)))=(q138 ◇ (q140 ◇ (q139 ◇ q138))):=by
    intro q138 q139 q140
    exact ((apc292 q140 q138 q139 q140).symm).trans ((((apc293 q140 q138 q140 q139 q138 q138 q138 q138 q138 q138 q138 q138).symm).trans (apc270 q138 q139 q138 q140)).trans (rfl))
  have apc296 : forall (q141 q142 : G), (q141 ◇ (q142 ◇ (q141 ◇ q141)))=(q141 ◇ ((q142 ◇ q141) ◇ q141)):=by
    intro q141 q142
    exact (((apc292 q142 q141 q141 q142).trans (apc295 q141 q141 q142)).symm).trans ((((apc292 q142 q141 q142 q141).symm).trans (apc276 q141 q142)).trans (rfl))
  exact (((((h x y z).trans (h (y ◇ z) x y)).trans ((apc286 z y (x ◇ y) x).symm)).trans (apc94 y x (y ◇ z))).trans (apc94 z y x)).trans (((((h (y ◇ z) x x).trans ((apc289 z y x).symm)).trans (apc296 x (y ◇ z))).trans (apc114 y z x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_56178_to_56177 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_56178_to_56177
