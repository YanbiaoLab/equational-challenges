-- Equation58434 → Equation61729
-- Recorded verdict: true
-- Premise: (x ◇ y) ◇ x = y ◇ (x ◇ (x ◇ z))
-- Conclusion: (x ◇ x) ◇ x = ((y ◇ y) ◇ y) ◇ y
-- Original submission SHA-256: 8f17827ec842431ff097001b755ffa57e0f0de14ad2c0fafc2c72ca44f6501ae
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ x = y ◇ (x ◇ (x ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), (x ◇ x) ◇ x = ((y ◇ y) ◇ y) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   

def submission : Goal := by
  intro G _ h
  intro x y
  have cg : ∀ (f : G → G) {a b : G}, a = b → f a = f b := by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1 : G), (q1 ◇ ((q0 ◇ q0) ◇ q0)) = ((q0 ◇ q1) ◇ q0) := by
    intro q0 q1
    exact ((rfl).symm).trans ((((cg (fun t => q1 ◇ t) ((h q0 q0 q0).symm)).symm).trans ((h q0 q1 (q0 ◇ q0)).symm)).trans (rfl))
  have apc1 : forall (q2 q0 q1 : G), (q1 ◇ (q0 ◇ ((q2 ◇ q0) ◇ q2))) = ((q0 ◇ q1) ◇ q0) := by
    intro q2 q0 q1
    exact ((rfl).symm).trans ((((cg (fun t => q1 ◇ t) (cg (fun t => q0 ◇ t) ((h q2 q0 q2).symm))).symm).trans ((h q0 q1 (q2 ◇ (q2 ◇ q2))).symm)).trans (rfl))
  have apc2 : forall (q3 q4 : G), (q3 ◇ ((q4 ◇ (q4 ◇ q4)) ◇ q4)) = (((q4 ◇ q4) ◇ q3) ◇ (q4 ◇ q4)) := by
    intro q3 q4
    exact ((rfl).symm).trans ((((cg (fun t => q3 ◇ t) (apc0 q4 (q4 ◇ q4))).symm).trans ((h (q4 ◇ q4) q3 q4).symm)).trans (rfl))
  have apc3 : forall (x y z : G), (y ◇ (x ◇ (x ◇ z))) = (y ◇ (x ◇ (x ◇ x))) := by
    intro x y z
    exact ((rfl).symm).trans (((h x y z).symm.trans (h x y x)).trans (rfl))
  have apc5 : forall (q5 q6 : G), (q6 ◇ (q5 ◇ (q5 ◇ q5))) = ((q5 ◇ q6) ◇ q5) := by
    intro q5 q6
    exact ((rfl).symm).trans ((((apc3 q5 q6 q5).symm).trans ((h q5 q6 q5).symm)).trans (rfl))
  have apc8 : forall (q7 q8 q9 : G), (q9 ◇ (q8 ◇ ((q7 ◇ (((q7 ◇ q7) ◇ q7) ◇ q8)) ◇ q7))) = ((q8 ◇ q9) ◇ q8) := by
    intro q7 q8 q9
    exact ((rfl).symm).trans ((((cg (fun t => q9 ◇ t) (cg (fun t => q8 ◇ t) (apc0 q7 (((q7 ◇ q7) ◇ q7) ◇ q8)))).symm).trans (apc1 ((q7 ◇ q7) ◇ q7) q8 q9)).trans (rfl))
  have apc10 : forall (q10 q11 : G), (q11 ◇ ((q10 ◇ (((q10 ◇ q10) ◇ q10) ◇ q10)) ◇ q10)) = ((q10 ◇ (((q10 ◇ q10) ◇ q10) ◇ q11)) ◇ q10) := by
    intro q10 q11
    exact (((cg (fun t => q11 ◇ t) (cg (fun t => t ◇ q10) (cg (fun t => q10 ◇ t) (apc0 q10 ((q10 ◇ q10) ◇ q10))))).trans (cg (fun t => q11 ◇ t) (cg (fun t => t ◇ q10) (cg (fun t => q10 ◇ t) (cg (fun t => t ◇ q10) (apc0 q10 q10)))))).symm).trans ((((cg (fun t => q11 ◇ t) (apc0 q10 (((q10 ◇ q10) ◇ q10) ◇ ((q10 ◇ q10) ◇ q10)))).symm).trans (apc0 ((q10 ◇ q10) ◇ q10) q11)).trans (apc0 q10 (((q10 ◇ q10) ◇ q10) ◇ q11)))
  have apc11 : forall (q12 q13 : G), ((q12 ◇ (((q12 ◇ q12) ◇ q12) ◇ q13)) ◇ q12) = ((q12 ◇ q13) ◇ q12) := by
    intro q12 q13
    exact ((apc10 q12 q13).symm).trans ((((cg (fun t => q13 ◇ t) (apc10 q12 q12)).symm).trans (apc8 q12 q12 q13)).trans (rfl))
  have apc12 : forall (q14 q15 q16 : G), ((q16 ◇ (((q16 ◇ q14) ◇ q16) ◇ q14)) ◇ q16) = ((q16 ◇ (q14 ◇ (q14 ◇ q15))) ◇ q16) := by
    intro q14 q15 q16
    exact ((cg (fun t => t ◇ q16) (cg (fun t => q16 ◇ t) (cg (fun t => t ◇ q14) (apc0 q16 q14)))).symm).trans ((((cg (fun t => t ◇ q16) (cg (fun t => q16 ◇ t) ((h q14 ((q16 ◇ q16) ◇ q16) q15).symm))).symm).trans (apc11 q16 (q14 ◇ (q14 ◇ q15)))).trans (rfl))
  have apc13 : forall (q17 q18 : G), ((q18 ◇ (q18 ◇ (q18 ◇ q17))) ◇ q18) = ((q18 ◇ q18) ◇ q18) := by
    intro q17 q18
    exact ((rfl).symm).trans ((((apc12 q18 q17 q18).symm).trans (apc11 q18 q18)).trans (rfl))
  have apc14 : forall (q19 : G), (((q19 ◇ q19) ◇ q19) ◇ q19) = ((q19 ◇ q19) ◇ q19) := by
    intro q19
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q19) ((h q19 q19 q19).symm)).symm).trans (apc13 q19 q19)).trans (rfl))
  have apc15 : forall (q20 q21 : G), ((q21 ◇ (((q21 ◇ q20) ◇ q21) ◇ q20)) ◇ q21) = (((q20 ◇ q21) ◇ q20) ◇ q21) := by
    intro q20 q21
    exact (((rfl).symm).trans ((((cg (fun t => t ◇ q21) ((h q20 q21 q20).symm)).symm).trans ((apc12 q20 q20 q21).symm)).trans (rfl))).symm
  have apc16 : forall (q14 q15 q16 q20 q21 : G), ((q16 ◇ (q14 ◇ (q14 ◇ q15))) ◇ q16) = (((q14 ◇ q16) ◇ q14) ◇ q16) := by
    intro q14 q15 q16 q20 q21
    exact (((rfl).symm).trans ((((apc15 q14 q16).symm).trans ((apc12 q14 q15 q16).trans (rfl))).trans (rfl))).symm
  have apc18 : forall (q22 q23 q24 : G), ((q23 ◇ ((q23 ◇ ((q22 ◇ q23) ◇ q22)) ◇ q24)) ◇ q23) = ((q23 ◇ q24) ◇ q23) := by
    intro q22 q23 q24
    exact ((((((((cg (fun t => q24 ◇ t) (cg (fun t => t ◇ q23) (cg (fun t => q23 ◇ t) (apc1 q22 q23 (q23 ◇ ((q22 ◇ q23) ◇ q22)))))).trans (cg (fun t => q24 ◇ t) (cg (fun t => t ◇ q23) (cg (fun t => q23 ◇ t) (cg (fun t => t ◇ q23) (apc1 q22 q23 q23)))))).trans (cg (fun t => q24 ◇ t) (cg (fun t => t ◇ q23) (cg (fun t => q23 ◇ t) (apc14 q23))))).trans (cg (fun t => q24 ◇ t) (cg (fun t => t ◇ q23) (apc0 q23 q23)))).trans (cg (fun t => q24 ◇ t) (apc14 q23))).trans (apc0 q23 q24)).symm).trans ((((cg (fun t => q24 ◇ t) (apc1 q22 q23 ((q23 ◇ ((q22 ◇ q23) ◇ q22)) ◇ (q23 ◇ ((q22 ◇ q23) ◇ q22))))).symm).trans (apc0 (q23 ◇ ((q22 ◇ q23) ◇ q22)) q24)).trans (apc1 q22 q23 ((q23 ◇ ((q22 ◇ q23) ◇ q22)) ◇ q24)))).symm
  have apc20 : forall (q7 q25 q9 : G), (q9 ◇ (((q7 ◇ q7) ◇ q7) ◇ (((q7 ◇ q25) ◇ q7) ◇ q25))) = ((q7 ◇ q9) ◇ q7) := by
    intro q7 q25 q9
    exact ((rfl).symm).trans ((((cg (fun t => q9 ◇ t) (cg (fun t => ((q7 ◇ q7) ◇ q7) ◇ t) (cg (fun t => t ◇ q25) (apc0 q7 q25)))).symm).trans (apc1 q25 ((q7 ◇ q7) ◇ q7) q9)).trans ((apc0 q7 (((q7 ◇ q7) ◇ q7) ◇ q9)).trans (apc11 q7 q9)))
  have apc21 : forall (q26 q27 : G), (((q26 ◇ q27) ◇ q26) ◇ q27) = ((q27 ◇ q27) ◇ q27) := by
    intro q26 q27
    exact (((apc14 q27).symm).trans ((((cg (fun t => t ◇ q27) (apc20 q27 q26 q27)).symm).trans (apc11 q27 (((q27 ◇ q26) ◇ q27) ◇ q26))).trans (apc15 q26 q27))).symm
  have apc23 : forall (q14 q15 q16 q20 q21 q26 q27 : G), ((q16 ◇ (q14 ◇ (q14 ◇ q15))) ◇ q16) = ((q16 ◇ q16) ◇ q16) := by
    intro q14 q15 q16 q20 q21 q26 q27
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc16 q14 q15 q16 q20 q21).trans (apc21 q14 q16))).trans (rfl))
  have apc24 : forall (q28 q29 q30 q31 : G), ((q30 ◇ q31) ◇ q30) = ((q29 ◇ q31) ◇ q29) := by
    intro q28 q29 q30 q31
    exact ((((((cg (fun t => q31 ◇ t) (cg (fun t => (q29 ◇ ((q28 ◇ q29) ◇ q28)) ◇ t) (apc21 q29 q30))).trans (cg (fun t => q31 ◇ t) (apc0 q30 (q29 ◇ ((q28 ◇ q29) ◇ q28))))).trans (cg (fun t => q31 ◇ t) (cg (fun t => t ◇ q30) (apc1 q28 q29 q30)))).trans (cg (fun t => q31 ◇ t) (apc21 q29 q30))).trans (apc0 q30 q31)).symm).trans ((((cg (fun t => q31 ◇ t) (cg (fun t => (q29 ◇ ((q28 ◇ q29) ◇ q28)) ◇ t) (cg (fun t => t ◇ q30) (apc1 q28 q29 q30)))).symm).trans (apc1 q30 (q29 ◇ ((q28 ◇ q29) ◇ q28)) q31)).trans ((apc1 q28 q29 ((q29 ◇ ((q28 ◇ q29) ◇ q28)) ◇ q31)).trans (apc18 q28 q29 q31)))
  have apc25 : forall (q32 q33 q34 q35 : G), (((q32 ◇ q33) ◇ q32) ◇ (q35 ◇ q33)) = ((q34 ◇ q35) ◇ q34) := by
    intro q32 q33 q34 q35
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (q35 ◇ q33)) (apc24 q32 q32 q35 q33)).symm).trans (apc24 q32 q34 (q35 ◇ q33) q35)).trans (rfl))
  have apc26 : forall (q36 q37 q38 q39 : G), ((q39 ◇ q39) ◇ q39) = ((q38 ◇ q38) ◇ q38) := by
    intro q36 q37 q38 q39
    exact ((apc21 q36 q39).symm).trans ((((cg (fun t => t ◇ q39) ((h q36 q39 q37).symm)).symm).trans (apc24 q36 q38 q39 (q36 ◇ (q36 ◇ q37)))).trans (apc23 q36 q37 q38 ((q38 ◇ (q36 ◇ (q36 ◇ q37))) ◇ q38) ((q38 ◇ (q36 ◇ (q36 ◇ q37))) ◇ q38) ((q38 ◇ (q36 ◇ (q36 ◇ q37))) ◇ q38) ((q38 ◇ (q36 ◇ (q36 ◇ q37))) ◇ q38)))
  have apc27 : forall (q40 q41 : G), (((q40 ◇ q40) ◇ q40) ◇ q41) = ((q41 ◇ q41) ◇ q41) := by
    intro q40 q41
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q41) (apc26 q40 q40 q40 q41)).symm).trans (apc21 q41 q41)).trans (rfl))
  have apc28 : forall (q42 q43 q44 : G), (((q42 ◇ q43) ◇ q42) ◇ q44) = ((q44 ◇ q44) ◇ q44) := by
    intro q42 q43 q44
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q44) (apc24 q42 q42 q43 q43)).symm).trans (apc27 q43 q44)).trans (rfl))
  have apc29 : forall (q45 q46 q47 : G), ((q46 ◇ q47) ◇ q46) = ((q45 ◇ q45) ◇ q45) := by
    intro q45 q46 q47
    exact (((rfl).symm).trans ((((apc26 q45 q45 q45 q47).symm).trans (apc24 q45 q46 q47 q47)).trans (rfl))).symm
  have apc30 : forall (q48 q49 : G), ((q49 ◇ ((q49 ◇ (q49 ◇ q49)) ◇ q48)) ◇ q49) = (((q49 ◇ q49) ◇ q48) ◇ (q49 ◇ q49)) := by
    intro q48 q49
    exact (((((cg (fun t => q48 ◇ t) (cg (fun t => t ◇ (q49 ◇ q49)) (apc5 q49 (q49 ◇ q49)))).trans (cg (fun t => q48 ◇ t) (apc28 q49 (q49 ◇ q49) (q49 ◇ q49)))).trans (apc0 (q49 ◇ q49) q48)).symm).trans ((((cg (fun t => q48 ◇ t) (apc2 (q49 ◇ (q49 ◇ q49)) q49)).symm).trans ((h (q49 ◇ (q49 ◇ q49)) q48 q49).symm)).trans (apc5 q49 ((q49 ◇ (q49 ◇ q49)) ◇ q48)))).symm
  have apc32 : forall (q50 q51 q52 : G), (((q50 ◇ q50) ◇ q50) ◇ (q52 ◇ q52)) = ((q51 ◇ q51) ◇ q51) := by
    intro q50 q51 q52
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (q52 ◇ q52)) (apc26 q50 q50 q50 q52)).symm).trans (apc29 q51 (q52 ◇ q52) q52)).trans (rfl))
  have apc47 : forall (q53 q54 q55 q56 q57 : G), (((q53 ◇ q54) ◇ q53) ◇ (q57 ◇ q55)) = ((q56 ◇ q57) ◇ q56) := by
    intro q53 q54 q55 q56 q57
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (q57 ◇ q55)) ((apc29 q55 q53 q54).symm)).symm).trans (apc25 q55 q55 q56 q57)).trans (rfl))
  have apc54 : forall (q58 q59 : G), ((q58 ◇ q59) ◇ q58) = ((q58 ◇ q58) ◇ q58) := by
    intro q58 q59
    exact ((((((((((cg (fun t => q59 ◇ t) (cg (fun t => t ◇ q58) (cg (fun t => q58 ◇ t) (cg (fun t => ((q58 ◇ q58) ◇ q58) ◇ t) (apc0 q58 ((q58 ◇ q58) ◇ q58)))))).trans (cg (fun t => q59 ◇ t) (cg (fun t => t ◇ q58) (cg (fun t => q58 ◇ t) (cg (fun t => ((q58 ◇ q58) ◇ q58) ◇ t) (cg (fun t => t ◇ q58) (apc0 q58 q58))))))).trans (cg (fun t => q59 ◇ t) (cg (fun t => t ◇ q58) (cg (fun t => q58 ◇ t) (cg (fun t => ((q58 ◇ q58) ◇ q58) ◇ t) (apc28 q58 q58 q58)))))).trans (cg (fun t => q59 ◇ t) (cg (fun t => t ◇ q58) (cg (fun t => q58 ◇ t) (apc0 q58 ((q58 ◇ q58) ◇ q58)))))).trans (cg (fun t => q59 ◇ t) (cg (fun t => t ◇ q58) (cg (fun t => q58 ◇ t) (cg (fun t => t ◇ q58) (apc0 q58 q58)))))).trans (cg (fun t => q59 ◇ t) (cg (fun t => t ◇ q58) (cg (fun t => q58 ◇ t) (apc28 q58 q58 q58))))).trans (cg (fun t => q59 ◇ t) (cg (fun t => t ◇ q58) (apc0 q58 q58)))).trans (cg (fun t => q59 ◇ t) (apc28 q58 q58 q58))).trans (apc0 q58 q59)).symm).trans ((((cg (fun t => q59 ◇ t) (apc0 q58 (((q58 ◇ q58) ◇ q58) ◇ (((q58 ◇ q58) ◇ q58) ◇ ((q58 ◇ q58) ◇ q58))))).symm).trans (apc2 q59 ((q58 ◇ q58) ◇ q58))).trans ((((((((((cg (fun t => t ◇ (((q58 ◇ q58) ◇ q58) ◇ ((q58 ◇ q58) ◇ q58))) (cg (fun t => t ◇ q59) (apc0 q58 ((q58 ◇ q58) ◇ q58)))).trans (cg (fun t => t ◇ (((q58 ◇ q58) ◇ q58) ◇ ((q58 ◇ q58) ◇ q58))) (cg (fun t => t ◇ q59) (cg (fun t => t ◇ q58) (apc0 q58 q58))))).trans (cg (fun t => t ◇ (((q58 ◇ q58) ◇ q58) ◇ ((q58 ◇ q58) ◇ q58))) (cg (fun t => t ◇ q59) (apc28 q58 q58 q58)))).trans (cg (fun t => t ◇ (((q58 ◇ q58) ◇ q58) ◇ ((q58 ◇ q58) ◇ q58))) (apc28 q58 q58 q59))).trans (cg (fun t => ((q59 ◇ q59) ◇ q59) ◇ t) (apc0 q58 ((q58 ◇ q58) ◇ q58)))).trans (cg (fun t => ((q59 ◇ q59) ◇ q59) ◇ t) (cg (fun t => t ◇ q58) (apc0 q58 q58)))).trans (cg (fun t => ((q59 ◇ q59) ◇ q59) ◇ t) (apc28 q58 q58 q58))).trans (apc0 q58 ((q59 ◇ q59) ◇ q59))).trans (cg (fun t => t ◇ q58) (apc0 q59 q58))).trans (apc28 q59 q58 q58)))
  have apc55 : forall (q60 q61 : G), (((q61 ◇ q61) ◇ q60) ◇ (q61 ◇ q61)) = ((q61 ◇ q61) ◇ q61) := by
    intro q60 q61
    exact (((rfl).symm).trans ((((apc54 q61 ((q61 ◇ (q61 ◇ q61)) ◇ q60)).symm).trans (apc30 q60 q61)).trans (rfl))).symm
  have apc56 : forall (q62 q63 : G), ((q63 ◇ q62) ◇ q63) = ((q62 ◇ q62) ◇ q62) := by
    intro q62 q63
    exact (((rfl).symm).trans ((((apc55 q62 q62).symm).trans (apc47 q62 q62 q62 q63 q62)).trans (rfl))).symm
  have apc62 : forall (q64 q65 q66 : G), (((q64 ◇ q64) ◇ q64) ◇ q64) = ((q66 ◇ q66) ◇ q66) := by
    intro q64 q65 q66
    exact ((((apc0 q64 ((q65 ◇ q65) ◇ q65)).trans (cg (fun t => t ◇ q64) (apc0 q65 q64))).trans (cg (fun t => t ◇ q64) (apc56 q64 q65))).symm).trans ((((cg (fun t => t ◇ ((q64 ◇ q64) ◇ q64)) (apc32 q64 q65 q64)).symm).trans (apc29 q66 ((q64 ◇ q64) ◇ q64) (q64 ◇ q64))).trans (rfl))
  exact (apc62 y ((x ◇ x) ◇ x) x).symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_58434_to_61729 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_58434_to_61729
