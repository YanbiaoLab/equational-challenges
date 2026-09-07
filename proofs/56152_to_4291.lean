-- Equation56152 → Equation4291
-- Recorded verdict: true
-- Premise: x ◇ (y ◇ z) = (y ◇ x) ◇ (z ◇ y)
-- Conclusion: x ◇ (x ◇ y) = y ◇ (x ◇ y)
-- Original submission SHA-256: 790c7f950cd13066abb385327d82dbf721d7f8b87702d9bf94cbb875053b5d25
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ z) = (y ◇ x) ◇ (z ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ (x ◇ y) = y ◇ (x ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have p0 : forall (q0 q1 q2 q3:G), (((q2 ◇ q1) ◇ q3) ◇ (q0 ◇ (q1 ◇ q2))) = (q3 ◇ ((q2 ◇ q1) ◇ (q1 ◇ q0))):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => ((q2 ◇ q1) ◇ q3) ◇ t) ((h q0 q1 q2).symm)).symm).trans ((h q3 (q2 ◇ q1) (q1 ◇ q0)).symm)
  have p1 : forall (q4 q5 q6:G), (q5 ◇ ((q4 ◇ q4) ◇ (q4 ◇ q6))) = (q5 ◇ ((q4 ◇ q4) ◇ q6)):=by
    intro q4 q5 q6
    exact ((p0 q6 q4 q4 q5).symm).trans ((h q5 (q4 ◇ q4) q6).symm)
  have p2 : forall (q7 q8:G), (q7 ◇ (q8 ◇ (q8 ◇ q8))) = (q7 ◇ ((q8 ◇ q8) ◇ q8)):=by
    intro q7 q8
    exact ((cg (fun t => q7 ◇ t) ((h q8 q8 q8).symm)).symm).trans (p1 q8 q7 q8)
  have p3 : forall (q9 q10 q11:G), ((q10 ◇ ((q9 ◇ q9) ◇ q9)) ◇ (q11 ◇ q10)) = ((q9 ◇ (q9 ◇ q9)) ◇ (q10 ◇ q11)):=by
    intro q9 q10 q11
    exact ((cg (fun t => t ◇ (q11 ◇ q10)) (p2 q10 q9)).symm).trans ((h (q9 ◇ (q9 ◇ q9)) q10 q11).symm)
  have p4 : forall (q0 q1 q2 q12:G), ((q0 ◇ (q1 ◇ q2)) ◇ (q12 ◇ (q1 ◇ q0))) = ((q2 ◇ q1) ◇ ((q1 ◇ q0) ◇ q12)):=by
    intro q0 q1 q2 q12
    exact ((cg (fun t => t ◇ (q12 ◇ (q1 ◇ q0))) ((h q0 q1 q2).symm)).symm).trans ((h (q2 ◇ q1) (q1 ◇ q0) q12).symm)
  have p5 : forall (q13 q14 q15:G), ((q13 ◇ (q13 ◇ q13)) ◇ (q14 ◇ q15)) = (((q13 ◇ q13) ◇ q13) ◇ (q14 ◇ q15)):=by
    intro q13 q14 q15
    exact ((p3 q13 q14 q15).symm).trans ((h ((q13 ◇ q13) ◇ q13) q14 q15).symm)
  have p6 : forall (q16 q17 q18:G), (((q16 ◇ q17) ◇ q18) ◇ ((q16 ◇ q16) ◇ q17)) = (q18 ◇ ((q16 ◇ q17) ◇ (q16 ◇ q16))):=by
    intro q16 q17 q18
    exact ((p1 q16 ((q16 ◇ q17) ◇ q18) q17).symm).trans ((h q18 (q16 ◇ q17) (q16 ◇ q16)).symm)
  have p7 : forall (q19 q20:G), ((q19 ◇ q19) ◇ ((q19 ◇ q19) ◇ q20)) = (q19 ◇ ((q19 ◇ q19) ◇ q20)):=by
    intro q19 q20
    exact ((((p0 q20 q19 q19 q19).trans (p1 q19 q19 q20)).symm).trans (((p5 q19 q20 (q19 ◇ q19)).symm).trans (p4 q19 q19 q19 q20))).symm
  have p8 : forall (q21 q22:G), (q22 ◇ ((q22 ◇ q22) ◇ (q21 ◇ q22))) = ((q22 ◇ q22) ◇ (q22 ◇ (q22 ◇ q21))):=by
    intro q21 q22
    exact (((cg (fun t => (q22 ◇ q22) ◇ t) ((h q22 q22 q21).symm)).symm).trans (p7 q22 (q21 ◇ q22))).symm
  have p9 : forall (q23 q24:G), ((q24 ◇ q24) ◇ (q24 ◇ (q24 ◇ q23))) = (q24 ◇ (q24 ◇ (q24 ◇ q23))):=by
    intro q23 q24
    exact (((cg (fun t => q24 ◇ t) ((h q24 q24 q23).symm)).symm).trans (p8 q23 q24)).symm
  have pa : forall (q21 q22 q23 q24:G), (q22 ◇ ((q22 ◇ q22) ◇ (q21 ◇ q22))) = (q22 ◇ (q22 ◇ (q22 ◇ q21))):=by
    intro q21 q22 q23 q24
    exact (p8 q21 q22).trans (p9 q21 q22)
  have pb : forall (q25 q26 q27 q28:G), (q28 ◇ ((q27 ◇ q26) ◇ (q26 ◇ (q27 ◇ q25)))) = (((q27 ◇ q26) ◇ q28) ◇ (q25 ◇ (q27 ◇ q26))):=by
    intro q25 q26 q27 q28
    exact (((cg (fun t => ((q27 ◇ q26) ◇ q28) ◇ t) ((h q25 q27 q26).symm)).symm).trans (p0 (q27 ◇ q25) q26 q27 q28)).symm
  have pc : forall (q29 q30 q31:G), (q31 ◇ (q30 ◇ (q30 ◇ (q30 ◇ q29)))) = (q31 ◇ ((q30 ◇ q30) ◇ q29)):=by
    intro q29 q30 q31
    exact (((cg (fun t => q31 ◇ t) (p9 q29 q30)).symm).trans (p1 q30 q31 (q30 ◇ q29))).trans (p1 q30 q31 q29)
  have pd : forall (q32 q33 q34:G), (q34 ◇ (q33 ◇ ((q33 ◇ q33) ◇ q32))) = (q34 ◇ ((q33 ◇ q33) ◇ q32)):=by
    intro q32 q33 q34
    exact (((cg (fun t => q34 ◇ t) (pc q32 q33 q33)).symm).trans (pc (q33 ◇ q32) q33 q34)).trans (p1 q33 q34 q32)
  have pe : forall (q35 q36 q37:G), (q37 ◇ ((q36 ◇ q36) ◇ (q35 ◇ q36))) = (q37 ◇ ((q36 ◇ q36) ◇ q35)):=by
    intro q35 q36 q37
    exact (((pc q35 q36 q37).symm).trans (((cg (fun t => q37 ◇ t) (cg (fun t => q36 ◇ t) ((h q36 q36 q35).symm))).symm).trans (pd (q35 ◇ q36) q36 q37))).symm
  have pf : forall (q21 q22 q23 q24 q35 q36 q37:G), (q22 ◇ (q22 ◇ (q22 ◇ q21))) = (q22 ◇ ((q22 ◇ q22) ◇ q21)):=by
    intro q21 q22 q23 q24 q35 q36 q37
    exact (((pe q21 q22 q22).symm).trans (pa q21 q22 q23 q24)).symm
  have pg : forall (q38 q39 q40:G), (q40 ◇ (q39 ◇ (q39 ◇ q38))) = (q40 ◇ ((q39 ◇ q39) ◇ q38)):=by
    intro q38 q39 q40
    exact ((cg (fun t => q40 ◇ t) ((h q39 q39 q38).symm)).symm).trans (pe q38 q39 q40)
  have ph : forall (q41 q42 q43:G), (q42 ◇ ((q43 ◇ q41) ◇ (q43 ◇ q43))) = (q42 ◇ ((q43 ◇ q41) ◇ q43)):=by
    intro q41 q42 q43
    exact ((p6 q43 q41 q42).symm).trans (((pg q41 q43 ((q43 ◇ q41) ◇ q42)).symm).trans ((h q42 (q43 ◇ q41) q43).symm))
  have pi : forall (q44 q45 q46:G), (q45 ◇ (q44 ◇ (q46 ◇ q46))) = (q45 ◇ ((q46 ◇ q44) ◇ q46)):=by
    intro q44 q45 q46
    exact ((cg (fun t => q45 ◇ t) ((h q44 q46 q46).symm)).symm).trans (ph q44 q45 q46)
  have pj : forall (q47 q48 q49:G), (q48 ◇ ((q49 ◇ (q49 ◇ q47)) ◇ q49)) = (q48 ◇ ((q49 ◇ q47) ◇ q49)):=by
    intro q47 q48 q49
    exact (((pi q47 q48 q49).symm).trans (((cg (fun t => q48 ◇ t) ((h q47 q49 q49).symm)).symm).trans (pi (q49 ◇ q47) q48 q49))).symm
  have pk : forall (q16 q17 q18 q41 q42 q43:G), (((q16 ◇ q17) ◇ q18) ◇ ((q16 ◇ q16) ◇ q17)) = (q18 ◇ ((q16 ◇ q17) ◇ q16)):=by
    intro q16 q17 q18 q41 q42 q43
    exact (p6 q16 q17 q18).trans (ph q17 q18 q16)
  have pl : forall (q50 q51 q52:G), ((q52 ◇ q51) ◇ ((q52 ◇ q50) ◇ q52)) = (q51 ◇ ((q52 ◇ q52) ◇ q50)):=by
    intro q50 q51 q52
    exact (((pj q50 (q52 ◇ q51) q52).symm).trans ((h q51 q52 (q52 ◇ (q52 ◇ q50))).symm)).trans ((cg (fun t => q51 ◇ t) (pg q50 q52 q52)).trans (pd q50 q52 q51))
  have pm : forall (q16 q17 q53 q54:G), ((q53 ◇ ((q16 ◇ q16) ◇ q17)) ◇ (q54 ◇ q53)) = (((q16 ◇ q16) ◇ (q16 ◇ q17)) ◇ (q53 ◇ q54)):=by
    intro q16 q17 q53 q54
    exact ((cg (fun t => t ◇ (q54 ◇ q53)) (p1 q16 q53 q17)).symm).trans ((h ((q16 ◇ q16) ◇ (q16 ◇ q17)) q53 q54).symm)
  have pn : forall (q55 q56 q57 q58:G), (((q55 ◇ q55) ◇ (q55 ◇ q56)) ◇ (q57 ◇ q58)) = (((q55 ◇ q55) ◇ q56) ◇ (q57 ◇ q58)):=by
    intro q55 q56 q57 q58
    exact ((pm q55 q56 q57 q58).symm).trans ((h ((q55 ◇ q55) ◇ q56) q57 q58).symm)
  have po : forall (q16 q17 q53 q54 q55 q56 q57 q58:G), ((q53 ◇ ((q16 ◇ q16) ◇ q17)) ◇ (q54 ◇ q53)) = (((q16 ◇ q16) ◇ q17) ◇ (q53 ◇ q54)):=by
    intro q16 q17 q53 q54 q55 q56 q57 q58
    exact (pm q16 q17 q53 q54).trans (pn q16 q17 q53 q54)
  have pp : forall (q59 q60 q61:G), (q61 ◇ (((q60 ◇ q59) ◇ (q60 ◇ q59)) ◇ q60)) = (q61 ◇ (q59 ◇ ((q60 ◇ q60) ◇ q59))):=by
    intro q59 q60 q61
    exact (((cg (fun t => q61 ◇ t) (pg q59 q60 q59)).symm).trans (((cg (fun t => q61 ◇ t) ((h q59 q60 (q60 ◇ q59)).symm)).symm).trans (pg q60 (q60 ◇ q59) q61))).symm
  have pq : forall (q62 q63 q64:G), ((q63 ◇ (q63 ◇ q62)) ◇ (q63 ◇ q64)) = (((q63 ◇ q63) ◇ q62) ◇ (q63 ◇ q64)):=by
    intro q62 q63 q64
    exact (((po q63 q62 q63 q64 ((q63 ◇ ((q63 ◇ q63) ◇ q62)) ◇ (q64 ◇ q63)) ((q63 ◇ ((q63 ◇ q63) ◇ q62)) ◇ (q64 ◇ q63)) ((q63 ◇ ((q63 ◇ q63) ◇ q62)) ◇ (q64 ◇ q63)) ((q63 ◇ ((q63 ◇ q63) ◇ q62)) ◇ (q64 ◇ q63))).symm).trans (((cg (fun t => t ◇ (q64 ◇ q63)) (pf q62 q63 q62 q62 q62 q62 q62)).symm).trans ((h (q63 ◇ (q63 ◇ q62)) q63 q64).symm))).symm
  have pr : forall (q65 q66:G), (((q66 ◇ q66) ◇ q65) ◇ (q66 ◇ q66)) = ((q66 ◇ q65) ◇ (q66 ◇ q66)):=by
    intro q65 q66
    exact ((pq q65 q66 q66).symm).trans ((h (q66 ◇ q65) q66 q66).symm)
  have ps : forall (q67 q68:G), ((q68 ◇ (q67 ◇ q68)) ◇ (q68 ◇ q68)) = ((q68 ◇ q67) ◇ (q68 ◇ q68)):=by
    intro q67 q68
    exact ((((pq q67 q68 q68).trans (pr q67 q68)).symm).trans (((cg (fun t => t ◇ (q68 ◇ q68)) ((h q68 q68 q67).symm)).symm).trans (pr (q67 ◇ q68) q68))).symm
  have pt : forall (q69 q70:G), ((q70 ◇ q69) ◇ (q70 ◇ q70)) = ((q69 ◇ q70) ◇ (q70 ◇ q70)):=by
    intro q69 q70
    exact ((ps q69 q70).symm).trans ((h (q69 ◇ q70) q70 q70).symm)
  have pu : forall (q71 q72:G), ((q71 ◇ q72) ◇ (q72 ◇ q72)) = (q71 ◇ (q72 ◇ q72)):=by
    intro q71 q72
    exact ((pt q71 q72).symm).trans ((h q71 q72 q72).symm)
  have pv : forall (q69 q70 q71 q72:G), ((q70 ◇ q69) ◇ (q70 ◇ q70)) = (q69 ◇ (q70 ◇ q70)):=by
    intro q69 q70 q71 q72
    exact (pt q69 q70).trans (pu q69 q70)
  have pw : forall (q73 q74 q75:G), (q75 ◇ ((q73 ◇ (q73 ◇ q73)) ◇ q74)) = (q75 ◇ ((q73 ◇ q73) ◇ q74)):=by
    intro q73 q74 q75
    exact (((pd q74 q73 q75).symm).trans ((((cg (fun t => q75 ◇ t) (p7 q73 q74)).symm).trans (pg q74 (q73 ◇ q73) q75)).trans (cg (fun t => q75 ◇ t) (cg (fun t => t ◇ q74) (pu q73 q73))))).symm
  have px : forall (q76 q77 q78:G), (q77 ◇ (q78 ◇ ((q76 ◇ q76) ◇ q76))) = ((q78 ◇ q77) ◇ ((q76 ◇ q76) ◇ q78)):=by
    intro q76 q77 q78
    exact ((((pw q76 q78 (q78 ◇ q77)).symm).trans ((h q77 q78 (q76 ◇ (q76 ◇ q76))).symm)).trans (cg (fun t => q77 ◇ t) (pg q76 q76 q78))).symm
  have py : forall (q79 q80 q81:G), ((q79 ◇ q80) ◇ ((q79 ◇ q79) ◇ q81)) = (q80 ◇ ((q79 ◇ q79) ◇ q81)):=by
    intro q79 q80 q81
    exact ((((p0 q81 q79 q79 q80).trans (p1 q79 q80 q81)).symm).trans (((pn q79 q80 q81 (q79 ◇ q79)).symm).trans ((h (q79 ◇ q80) (q79 ◇ q79) q81).symm))).symm
  have pz : forall (q82 q83 q84:G), (q84 ◇ (((q83 ◇ q82) ◇ (q83 ◇ q82)) ◇ (q82 ◇ q83))) = (q84 ◇ (((q83 ◇ q82) ◇ (q83 ◇ q82)) ◇ q82)):=by
    intro q82 q83 q84
    exact ((((cg (fun t => q84 ◇ t) (pb q82 q82 q83 (q83 ◇ q82))).trans (pe q82 (q83 ◇ q82) q84)).symm).trans (((cg (fun t => q84 ◇ t) (p0 (q83 ◇ q82) q82 q83 (q83 ◇ q82))).symm).trans (p1 (q83 ◇ q82) q84 (q82 ◇ q83)))).symm
  have p10 : forall (q41 q85 q86 q43:G), ((q85 ◇ (q85 ◇ q41)) ◇ (q86 ◇ q43)) = (((q85 ◇ q85) ◇ q41) ◇ (q86 ◇ q43)):=by
    intro q41 q85 q86 q43
    exact (((po q85 q41 q86 q43 ((q86 ◇ ((q85 ◇ q85) ◇ q41)) ◇ (q43 ◇ q86)) ((q86 ◇ ((q85 ◇ q85) ◇ q41)) ◇ (q43 ◇ q86)) ((q86 ◇ ((q85 ◇ q85) ◇ q41)) ◇ (q43 ◇ q86)) ((q86 ◇ ((q85 ◇ q85) ◇ q41)) ◇ (q43 ◇ q86))).symm).trans (((cg (fun t => t ◇ (q43 ◇ q86)) (pg q41 q85 q86)).symm).trans ((h (q85 ◇ (q85 ◇ q41)) q86 q43).symm))).symm
  have p11 : forall (q87 q88 q89:G), (((q88 ◇ q88) ◇ q87) ◇ (q89 ◇ q88)) = ((q88 ◇ q87) ◇ (q88 ◇ q89)):=by
    intro q87 q88 q89
    exact ((p10 q87 q88 q89 q88).symm).trans ((h (q88 ◇ q87) q88 q89).symm)
  have p12 : forall (q90 q91 q92:G), ((q91 ◇ q92) ◇ ((q90 ◇ q90) ◇ q91)) = (q92 ◇ ((q90 ◇ q91) ◇ q90)):=by
    intro q90 q91 q92
    exact (((cg (fun t => q92 ◇ t) (pi q90 q91 q90)).trans (px q90 q92 q91)).symm).trans ((((cg (fun t => q92 ◇ t) (cg (fun t => q91 ◇ t) ((h q90 q90 q90).symm))).symm).trans (pi q91 q92 (q90 ◇ q90))).trans (((cg (fun t => q92 ◇ t) (p11 q91 q90 q90)).trans (cg (fun t => q92 ◇ t) (pv q91 q90 ((q90 ◇ q91) ◇ (q90 ◇ q90)) ((q90 ◇ q91) ◇ (q90 ◇ q90))))).trans (pi q91 q92 q90)))
  have p13 : forall (q93 q94 q95:G), ((q94 ◇ q93) ◇ ((q93 ◇ q93) ◇ q95)) = (q94 ◇ ((q93 ◇ q93) ◇ q95)):=by
    intro q93 q94 q95
    exact ((((((pi q95 ((q93 ◇ q93) ◇ q94) q93).trans (p11 q94 q93 (q93 ◇ q95))).trans (pg q95 q93 (q93 ◇ q94))).trans (py q93 q94 q95)).symm).trans (((p10 q94 q93 q95 (q93 ◇ q93)).symm).trans (p4 q93 q93 q94 q95))).symm
  have p14 : forall (q96 q97:G), (q97 ◇ ((q96 ◇ q96) ◇ q97)) = (q96 ◇ ((q96 ◇ q97) ◇ q96)):=by
    intro q96 q97
    exact (((p13 q96 q97 q97).symm).trans ((h q96 q97 (q96 ◇ q96)).symm)).trans (pi q97 q96 q96)
  have p15 : forall (q98 q99 q10 q11:G), ((q10 ◇ ((q99 ◇ q98) ◇ q99)) ◇ (q11 ◇ q10)) = ((q98 ◇ (q99 ◇ q99)) ◇ (q10 ◇ q11)):=by
    intro q98 q99 q10 q11
    exact ((cg (fun t => t ◇ (q11 ◇ q10)) (pi q98 q10 q99)).symm).trans ((h (q98 ◇ (q99 ◇ q99)) q10 q11).symm)
  have p16 : forall (q100 q101 q102 q103:G), ((q100 ◇ (q101 ◇ q101)) ◇ (q102 ◇ q103)) = (((q101 ◇ q100) ◇ q101) ◇ (q102 ◇ q103)):=by
    intro q100 q101 q102 q103
    exact ((p15 q100 q101 q102 q103).symm).trans ((h ((q101 ◇ q100) ◇ q101) q102 q103).symm)
  have p17 : forall (q104 q105 q106:G), (((q104 ◇ q105) ◇ q104) ◇ (q106 ◇ q105)) = ((q104 ◇ q104) ◇ (q105 ◇ q106)):=by
    intro q104 q105 q106
    exact ((p16 q105 q104 q106 q105).symm).trans ((h (q104 ◇ q104) q105 q106).symm)
  have p18 : forall (q107 q108:G), (q108 ◇ ((q108 ◇ q108) ◇ q107)) = (q108 ◇ ((q108 ◇ q107) ◇ q108)):=by
    intro q107 q108
    exact (((pi q107 (q108 ◇ q108) q108).trans (pl q107 q108 q108)).symm).trans (((p17 q108 q107 (q108 ◇ q108)).symm).trans (pk q108 q107 q108 q107 q107 q107))
  have p19 : forall (q109 q110 q111:G), (q109 ◇ (q111 ◇ ((q111 ◇ q110) ◇ q111))) = (q109 ◇ ((q111 ◇ q111) ◇ q110)):=by
    intro q109 q110 q111
    exact (((cg (fun t => q109 ◇ t) (pg q110 q111 q111)).trans (cg (fun t => q109 ◇ t) (p18 q110 q111))).symm).trans (((h q109 q111 (q111 ◇ (q111 ◇ q110))).trans (pj q110 (q111 ◇ q109) q111)).trans (pl q110 q109 q111))
  have p1a : forall (q112 q113 q114 q115:G), (q115 ◇ (((q113 ◇ q112) ◇ (q113 ◇ q112)) ◇ (q114 ◇ q113))) = (((q113 ◇ q112) ◇ q115) ◇ (q114 ◇ (q113 ◇ q112))):=by
    intro q112 q113 q114 q115
    exact (((pb q114 q112 q113 q115).symm).trans (((cg (fun t => q115 ◇ t) (cg (fun t => (q113 ◇ q112) ◇ t) ((h q112 q113 q114).symm))).symm).trans (pg (q114 ◇ q113) (q113 ◇ q112) q115))).symm
  have p1b : forall (q116 q117 q118:G), (q118 ◇ ((q116 ◇ q117) ◇ q116)) = (q118 ◇ ((q116 ◇ q116) ◇ q117)):=by
    intro q116 q117 q118
    exact (((((cg (fun t => q118 ◇ t) (pl q117 q117 q116)).trans (cg (fun t => q118 ◇ t) (p14 q116 q117))).trans (p19 q118 q117 q116)).symm).trans ((((cg (fun t => q118 ◇ t) (pi q117 (q116 ◇ q117) q116)).symm).trans (pb q116 q117 q116 q118)).trans ((pg q117 q116 ((q116 ◇ q117) ◇ q118)).trans (pk q116 q117 q118 (((q116 ◇ q117) ◇ q118) ◇ ((q116 ◇ q116) ◇ q117)) (((q116 ◇ q117) ◇ q118) ◇ ((q116 ◇ q116) ◇ q117)) (((q116 ◇ q117) ◇ q118) ◇ ((q116 ◇ q116) ◇ q117)))))).symm
  have p1c : forall (q90 q91 q92:G), ((q91 ◇ q92) ◇ ((q90 ◇ q90) ◇ q91)) = (q92 ◇ ((q90 ◇ q90) ◇ q91)):=by
    intro q90 q91 q92
    exact (p12 q90 q91 q92).trans (p1b q90 q91 q92)
  have p1d : forall (q109 q110 q119:G), (q119 ◇ ((q110 ◇ q109) ◇ (q110 ◇ q109))) = (q119 ◇ ((q110 ◇ q110) ◇ q109)):=by
    intro q109 q110 q119
    exact ((((cg (fun t => q119 ◇ t) (cg (fun t => t ◇ (q110 ◇ q109)) (pg q109 q110 q109))).trans (cg (fun t => q119 ◇ t) (po q110 q109 q109 q110 ((q109 ◇ ((q110 ◇ q110) ◇ q109)) ◇ (q110 ◇ q109)) ((q109 ◇ ((q110 ◇ q110) ◇ q109)) ◇ (q110 ◇ q109)) ((q109 ◇ ((q110 ◇ q110) ◇ q109)) ◇ (q110 ◇ q109)) ((q109 ◇ ((q110 ◇ q110) ◇ q109)) ◇ (q110 ◇ q109))))).trans (cg (fun t => q119 ◇ t) (p11 q109 q110 q109))).symm).trans ((((cg (fun t => q119 ◇ t) (cg (fun t => t ◇ (q110 ◇ q109)) ((h q109 q110 (q110 ◇ q109)).symm))).symm).trans (pj q110 q119 (q110 ◇ q109))).trans ((cg (fun t => q119 ◇ t) (p17 q110 q109 q110)).trans (pe q109 q110 q119)))
  have p1e : forall (q120 q121 q122 q123:G), (q123 ◇ (((q121 ◇ q120) ◇ (q121 ◇ q120)) ◇ q122)) = (q123 ◇ (q122 ◇ ((q121 ◇ q121) ◇ q120))):=by
    intro q120 q121 q122 q123
    exact ((((cg (fun t => q123 ◇ t) (p1d q120 q121 q122)).symm).trans (pi q122 q123 (q121 ◇ q120))).trans (p1b (q121 ◇ q120) q122 q123)).symm
  have p1f : forall (q124 q125 q126:G), (q125 ◇ (q124 ◇ ((q126 ◇ q126) ◇ q124))) = (q125 ◇ ((q126 ◇ q126) ◇ q124)):=by
    intro q124 q125 q126
    exact ((((pv q125 (q126 ◇ q124) (((q126 ◇ q124) ◇ q125) ◇ ((q126 ◇ q124) ◇ (q126 ◇ q124))) (((q126 ◇ q124) ◇ q125) ◇ ((q126 ◇ q124) ◇ (q126 ◇ q124)))).trans (p1d q124 q126 q125)).symm).trans ((((p1a q124 q126 (q126 ◇ q124) q125).symm).trans (p1 (q126 ◇ q124) q125 q126)).trans (pp q124 q126 q125))).symm
  have p1g : forall (q127 q128 q129:G), (((q128 ◇ q127) ◇ q129) ◇ (q127 ◇ (q128 ◇ q127))) = (q129 ◇ ((q128 ◇ q128) ◇ q127)):=by
    intro q127 q128 q129
    exact (((p1a q127 q128 q127 q129).symm).trans (pz q127 q128 q129)).trans ((p1e q127 q128 q127 q129).trans (p1f q127 q129 q128))
  have p1h : forall (q130 q131 q132:G), (q131 ◇ ((q130 ◇ q132) ◇ q132)) = (q131 ◇ ((q130 ◇ q130) ◇ q132)):=by
    intro q130 q131 q132
    exact (((p1g q132 q130 q131).symm).trans ((h q131 (q130 ◇ q132) q132).symm)).symm
  have p1i : forall (q133 q134 q135:G), (q134 ◇ (q135 ◇ (q133 ◇ q135))) = (q134 ◇ ((q133 ◇ q133) ◇ q135)):=by
    intro q133 q134 q135
    exact (((p1c q133 q135 q134).symm).trans (((p1h q133 (q135 ◇ q134) q135).symm).trans ((h q134 q135 (q133 ◇ q135)).symm))).symm
  exact (calc
    (x ◇ (x ◇ y)) = ((x ◇ x) ◇ (y ◇ x)):=h x x y
    _ = ((y ◇ (x ◇ x)) ◇ (x ◇ y)):=h (x ◇ x) y x
    _ = ((x ◇ (y ◇ (x ◇ x))) ◇ (y ◇ x)):=h (y ◇ (x ◇ x)) x y
    _ = ((x ◇ ((x ◇ y) ◇ x)) ◇ (y ◇ x)):=cg (fun t => t ◇ (y ◇ x)) (pi y x x)
    _ = ((x ◇ ((x ◇ x) ◇ y)) ◇ (y ◇ x)):=(cg (fun t => t ◇ (y ◇ x)) ((p1b x y x).symm)).symm
    _ = ((x ◇ (y ◇ (x ◇ y))) ◇ (y ◇ x)):=(cg (fun t => t ◇ (y ◇ x)) (p1i x x y)).symm
    _ = ((y ◇ (x ◇ y)) ◇ (x ◇ y)):=(h (y ◇ (x ◇ y)) x y).symm
    _ = ((x ◇ y) ◇ (y ◇ x)):=(h (x ◇ y) y x).symm
    _ = (y ◇ (x ◇ y)):=(h y x y).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_56152_to_4291 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_56152_to_4291
