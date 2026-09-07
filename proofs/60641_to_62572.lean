-- Equation60641 → Equation62572
-- Recorded verdict: true
-- Premise: (x ◇ y) ◇ z = (z ◇ z) ◇ (x ◇ z)
-- Conclusion: (x ◇ y) ◇ z = ((w ◇ u) ◇ v) ◇ z
-- Original submission SHA-256: 2aca401ea5988555f84835afacb62b820ec858e32a46ae1dc09ee5fb225af919
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ z = (z ◇ z) ◇ (x ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G), (x ◇ y) ◇ z = ((w ◇ u) ◇ v) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u v
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have p0 : forall (x y z:G), ((x ◇ y) ◇ z) = ((x ◇ x) ◇ z):=by
    intro x y z
    exact (h x y z).trans ((h x x z).symm)
  have p1 : forall (q5 q6:G), ((q6 ◇ q6) ◇ (q5 ◇ q6)) = ((q5 ◇ q5) ◇ q6):=by
    intro q5 q6
    exact (((p0 q5 q5 q6).symm).trans (h q5 q5 q6)).symm
  have p2 : forall (q7 q8 q9 q10:G), (((q7 ◇ q7) ◇ q9) ◇ q10) = (((q7 ◇ q7) ◇ q7) ◇ q10):=by
    intro q7 q8 q9 q10
    exact (((cg (fun t => t ◇ q10) (p0 q7 q8 q9)).symm).trans (p0 (q7 ◇ q8) q9 q10)).trans (((cg (fun t => t ◇ q10) (p0 q7 q8 (q7 ◇ q8))).trans (p0 (q7 ◇ q7) (q7 ◇ q8) q10)).trans (cg (fun t => t ◇ q10) (p1 q7 q7)))
  have p3 : forall (q11 q12 q13:G), (((q12 ◇ q12) ◇ q12) ◇ q13) = (((q11 ◇ q11) ◇ q11) ◇ q13):=by
    intro q11 q12 q13
    exact (((p2 q11 (((q11 ◇ q11) ◇ q12) ◇ q13) q12 q13).symm).trans (((cg (fun t => t ◇ q13) (p1 q11 q12)).symm).trans (p2 q12 q11 (q11 ◇ q12) q13))).symm
  have p4 : forall (q14 q15 q16:G), (((q14 ◇ q14) ◇ q14) ◇ (q16 ◇ (q14 ◇ q16))) = ((q14 ◇ q14) ◇ q16):=by
    intro q14 q15 q16
    exact (((p0 q14 q15 q16).symm).trans (((h q14 q15 q16).trans (h q16 q16 (q14 ◇ q16))).trans (((cg (fun t => t ◇ (q16 ◇ (q14 ◇ q16))) (p0 q14 q16 (q14 ◇ q16))).trans (p0 (q14 ◇ q14) (q14 ◇ q16) (q16 ◇ (q14 ◇ q16)))).trans (cg (fun t => t ◇ (q16 ◇ (q14 ◇ q16))) (p1 q14 q14))))).symm
  have p5 : forall (q17 q18 q19:G), (((q18 ◇ q18) ◇ q18) ◇ (q17 ◇ (q19 ◇ q17))) = ((q19 ◇ q19) ◇ q17):=by
    intro q17 q18 q19
    exact (((p4 q19 q17 q17).symm).trans (p3 q18 q19 (q17 ◇ (q19 ◇ q17)))).symm
  have p6 : forall (q20 q21 q5 q22:G), (((q20 ◇ q20) ◇ q20) ◇ (q5 ◇ (q20 ◇ q21))) = ((q5 ◇ q5) ◇ (q20 ◇ q21)):=by
    intro q20 q21 q5 q22
    exact (((p0 (q20 ◇ q20) (q20 ◇ q21) (q5 ◇ (q20 ◇ q21))).trans (cg (fun t => t ◇ (q5 ◇ (q20 ◇ q21))) (p1 q20 q20))).symm).trans ((((cg (fun t => t ◇ (q5 ◇ (q20 ◇ q21))) (p0 q20 q21 (q20 ◇ q21))).symm).trans ((h q5 q22 (q20 ◇ q21)).symm)).trans (p0 q5 q22 (q20 ◇ q21)))
  have p7 : forall (q23 q24 q25:G), ((q25 ◇ q25) ◇ (((q23 ◇ q23) ◇ q23) ◇ q25)) = (((q23 ◇ q23) ◇ q23) ◇ q25):=by
    intro q23 q24 q25
    exact (((p2 q23 (((q23 ◇ q23) ◇ q24) ◇ q25) q24 q25).symm).trans (((cg (fun t => t ◇ q25) (p4 q23 q23 q24)).symm).trans (h ((q23 ◇ q23) ◇ q23) (q24 ◇ (q23 ◇ q24)) q25))).symm
  have p8 : forall (q26 q27 q28:G), ((((q26 ◇ q26) ◇ q26) ◇ q27) ◇ q28) = (((q26 ◇ q26) ◇ q26) ◇ q28):=by
    intro q26 q27 q28
    exact (((p7 q26 q26 q28).symm).trans ((h ((q26 ◇ q26) ◇ q26) q27 q28).symm)).symm
  have p9 : forall (q29 q30 q31 q32:G), (((q31 ◇ q31) ◇ q31) ◇ q32) = (((q30 ◇ q30) ◇ q29) ◇ q32):=by
    intro q29 q30 q31 q32
    exact (((cg (fun t => t ◇ q32) (p5 q29 q31 q30)).symm).trans (p8 q31 (q29 ◇ (q30 ◇ q29)) q32)).symm
  have pa : forall (q33 q34 q35 q36:G), (((q34 ◇ q34) ◇ q33) ◇ (q35 ◇ (q36 ◇ q35))) = ((q36 ◇ q36) ◇ q35):=by
    intro q33 q34 q35 q36
    exact ((p9 q33 q34 q33 (q35 ◇ (q36 ◇ q35))).symm).trans (p5 q35 q33 q36)
  have pb : forall (q37 q38 q39 q40:G), (((q39 ◇ q39) ◇ q39) ◇ (q38 ◇ (q40 ◇ q37))) = ((q38 ◇ q38) ◇ (q40 ◇ q37)):=by
    intro q37 q38 q39 q40
    exact (((p6 q40 q37 q38 q37).symm).trans (p3 q39 q40 (q38 ◇ (q40 ◇ q37)))).symm
  have pc : forall (q41 q42 q43 q44 q45:G), ((q45 ◇ q45) ◇ (((q42 ◇ q42) ◇ q41) ◇ q45)) = (((q44 ◇ q44) ◇ q43) ◇ q45):=by
    intro q41 q42 q43 q44 q45
    exact (((cg (fun t => t ◇ q45) (pa q41 q42 q43 q44)).symm).trans (h ((q42 ◇ q42) ◇ q41) (q43 ◇ (q44 ◇ q43)) q45)).symm
  have pd : forall (q46 q47 q48 q49:G), ((((q47 ◇ q47) ◇ q46) ◇ q48) ◇ q49) = (((q48 ◇ q48) ◇ q48) ◇ q49):=by
    intro q46 q47 q48 q49
    exact ((cg (fun t => t ◇ q49) (pc q46 q46 q46 q47 q48)).symm).trans (p2 q48 q46 (((q46 ◇ q46) ◇ q46) ◇ q48) q49)
  have pe : forall (q50 q51 q52 q53:G), ((((q50 ◇ q50) ◇ q50) ◇ (q50 ◇ q51)) ◇ q53) = (((q52 ◇ q52) ◇ q52) ◇ q53):=by
    intro q50 q51 q52 q53
    exact (((((((((cg (fun t => t ◇ q53) (cg (fun t => t ◇ q52) (cg (fun t => t ◇ (q50 ◇ (q50 ◇ q51))) (p0 q50 q51 (q50 ◇ q51))))).trans (cg (fun t => t ◇ q53) (cg (fun t => t ◇ q52) (p0 (q50 ◇ q50) (q50 ◇ q51) (q50 ◇ (q50 ◇ q51)))))).trans (cg (fun t => t ◇ q53) (cg (fun t => t ◇ q52) (cg (fun t => t ◇ (q50 ◇ (q50 ◇ q51))) (p1 q50 q50))))).trans (cg (fun t => t ◇ q53) (cg (fun t => t ◇ q52) (pb q51 q50 q50 q50)))).trans (cg (fun t => t ◇ q53) (p0 (q50 ◇ q50) (q50 ◇ q51) q52))).trans (cg (fun t => t ◇ q53) (cg (fun t => t ◇ q52) (p1 q50 q50)))).trans (pd q50 q50 q52 q53)).symm).trans ((((cg (fun t => t ◇ q53) (cg (fun t => t ◇ q52) (h q50 q51 (q50 ◇ q51)))).symm).trans (p2 (q50 ◇ q51) q50 q52 q53)).trans (((cg (fun t => t ◇ q53) (cg (fun t => t ◇ (q50 ◇ q51)) (p0 q50 q51 (q50 ◇ q51)))).trans (cg (fun t => t ◇ q53) (p0 (q50 ◇ q50) (q50 ◇ q51) (q50 ◇ q51)))).trans (cg (fun t => t ◇ q53) (cg (fun t => t ◇ (q50 ◇ q51)) (p1 q50 q50)))))).symm
  have pf : forall (q54 q55 q56 q57 q58:G), ((((q54 ◇ q54) ◇ q54) ◇ (q54 ◇ q55)) ◇ q58) = (((q57 ◇ q57) ◇ q56) ◇ q58):=by
    intro q54 q55 q56 q57 q58
    exact (pe q54 q55 q54 q58).trans (p9 q56 q57 q54 q58)
  have pg : forall (q59 q60 q61 q62 q63 q64 q65:G), ((((q60 ◇ q60) ◇ q59) ◇ (q61 ◇ q62)) ◇ q65) = (((q64 ◇ q64) ◇ q63) ◇ q65):=by
    intro q59 q60 q61 q62 q63 q64 q65
    exact ((cg (fun t => t ◇ q65) (p9 q59 q60 q61 (q61 ◇ q62))).symm).trans (pf q61 q62 q63 q64 q65)
  have ph : forall (q66 q67 q68 q69 q70 q71:G), (((q68 ◇ q66) ◇ (q67 ◇ q67)) ◇ q71) = (((q70 ◇ q70) ◇ q69) ◇ q71):=by
    intro q66 q67 q68 q69 q70 q71
    exact ((cg (fun t => t ◇ q71) ((h q68 q66 (q67 ◇ q67)).symm)).symm).trans (pg (q67 ◇ q67) q67 q68 (q67 ◇ q67) q69 q70 q71)
  have pi : forall (q72 q73 q74 q75 q76:G), (((q75 ◇ q75) ◇ q74) ◇ q76) = (((q73 ◇ q72) ◇ q73) ◇ q76):=by
    intro q72 q73 q74 q75 q76
    exact (((cg (fun t => t ◇ q76) ((h q73 q72 q73).symm)).symm).trans (ph q73 q73 q73 q74 q75 q76)).symm
  have pj : forall (q77 q78 q79 q80:G), (((q78 ◇ q77) ◇ q78) ◇ (q79 ◇ (q80 ◇ q79))) = ((q80 ◇ q80) ◇ q79):=by
    intro q77 q78 q79 q80
    exact ((pi q77 q78 q77 q77 (q79 ◇ (q80 ◇ q79))).symm).trans (pa q77 q77 q79 q80)
  have pk : forall (q81 q82 q83 q84:G), (((q84 ◇ q81) ◇ (q84 ◇ q81)) ◇ (q82 ◇ (q83 ◇ q82))) = ((q83 ◇ q83) ◇ q82):=by
    intro q81 q82 q83 q84
    exact (((pj q81 q84 q82 q83).symm).trans (p0 (q84 ◇ q81) q84 (q82 ◇ (q83 ◇ q82)))).symm
  have pl : forall (q85 q86 q87 q88 q89:G), (((q86 ◇ q86) ◇ q85) ◇ (q89 ◇ (q87 ◇ q88))) = ((q89 ◇ q89) ◇ (q87 ◇ q88)):=by
    intro q85 q86 q87 q88 q89
    exact ((p9 q85 q86 q87 (q89 ◇ (q87 ◇ q88))).symm).trans (p6 q87 q88 q89 q85)
  have pm : forall (q90 q91 q92:G), ((q91 ◇ q90) ◇ (q92 ◇ q91)) = ((q92 ◇ q92) ◇ q91):=by
    intro q90 q91 q92
    exact (h q91 q90 (q92 ◇ q91)).trans (pk q91 q91 q92 q92)
  have pn : forall (q93 q94 q95:G), ((q95 ◇ q95) ◇ (q94 ◇ q94)) = ((q95 ◇ q93) ◇ (q94 ◇ q94)):=by
    intro q93 q94 q95
    exact ((h q95 q93 (q94 ◇ q94)).trans (pl (q94 ◇ q94) q94 q94 q94 q95)).symm
  have po : forall (q96 q97:G), ((q97 ◇ q97) ◇ q97) = ((q97 ◇ q96) ◇ q97):=by
    intro q96 q97
    exact ((p1 q97 q97).symm).trans ((pn q97 q97 q97).trans ((h q97 q96 q97).symm))
  have pp : forall (q98 q99 q100 q101:G), (((q99 ◇ q98) ◇ (q99 ◇ q98)) ◇ q101) = (((q100 ◇ q100) ◇ q99) ◇ q101):=by
    intro q98 q99 q100 q101
    exact (((cg (fun t => t ◇ q101) (pm q98 q99 q100)).symm).trans (p0 (q99 ◇ q98) (q100 ◇ q99) q101)).symm
  have pq : forall (q102 q103 q104 q105:G), ((q105 ◇ q103) ◇ (q104 ◇ q104)) = ((q105 ◇ q102) ◇ (q104 ◇ q104)):=by
    intro q102 q103 q104 q105
    exact (((pn q102 q104 q105).symm).trans (pn q103 q104 q105)).symm
  have pr : forall (q93 q94 q95:G), ((q95 ◇ q94) ◇ (q94 ◇ q94)) = ((q95 ◇ q93) ◇ (q94 ◇ q94)):=by
    intro q93 q94 q95
    exact (((pn q93 q94 q95).symm).trans (pn q94 q94 q95)).symm
  have ps : forall (q106 q107 q108:G), (((q107 ◇ q107) ◇ q107) ◇ q108) = (((q107 ◇ q106) ◇ q107) ◇ q108):=by
    intro q106 q107 q108
    exact ((((cg (fun t => t ◇ q108) (po q106 q107)).symm).trans (p0 (q107 ◇ q107) q107 q108)).trans (cg (fun t => t ◇ q108) (p1 q107 q107))).symm
  have pt : forall (q106 q107 q108:G), (((q107 ◇ q106) ◇ (q107 ◇ q106)) ◇ q108) = (((q107 ◇ q107) ◇ q107) ◇ q108):=by
    intro q106 q107 q108
    exact (((cg (fun t => t ◇ q108) ((po q106 q107).symm)).symm).trans (p0 (q107 ◇ q106) q107 q108)).symm
  have pu : forall (q109 q110 q111:G), (((q110 ◇ q110) ◇ q109) ◇ q111) = (((q109 ◇ q109) ◇ q109) ◇ q111):=by
    intro q109 q110 q111
    exact (((cg (fun t => t ◇ q111) (p1 q109 q109)).symm).trans (pp q109 q109 q110 q111)).symm
  have pv : forall (q112 q113:G), ((q113 ◇ q113) ◇ (q112 ◇ q112)) = ((q113 ◇ q112) ◇ (q112 ◇ q112)):=by
    intro q112 q113
    exact ((pr q112 q112 q113).trans (p0 q113 q112 (q112 ◇ q112))).symm
  have pw : forall (q114 q115 q116:G), (((q116 ◇ q116) ◇ q116) ◇ q116) = (((q116 ◇ q114) ◇ q115) ◇ q116):=by
    intro q114 q115 q116
    exact (((p1 (q116 ◇ q116) q116).trans (cg (fun t => t ◇ q116) (p1 q116 q116))).symm).trans (((cg (fun t => (q116 ◇ q116) ◇ t) ((po q114 q116).symm)).symm).trans ((h (q116 ◇ q114) q115 q116).symm))
  have px : forall (q117 q118 q119 q120 q121:G), (((q121 ◇ q117) ◇ q118) ◇ q121) = (((q119 ◇ q119) ◇ q119) ◇ q121):=by
    intro q117 q118 q119 q120 q121
    exact (((pw q117 q118 q121).symm).trans (p9 q119 q120 q121 q121)).trans (pu q119 q120 q121)
  have py : forall (x y z:G), ((x ◇ y) ◇ z) = ((x ◇ x) ◇ z):=by
    intro x y z
    exact (h x y z).trans ((h x x z).symm)
  have pz : forall (q0 q2 q3 q1:G), (((q0 ◇ q0) ◇ q2) ◇ q3) = (((q0 ◇ q0) ◇ q0) ◇ q3):=by
    intro q0 q2 q3 q1
    exact (((((cg (fun t => (q3 ◇ q3) ◇ t) (pm q3 q3 q0)).trans (pm q3 q3 (q0 ◇ q0))).trans (cg (fun t => t ◇ q3) (pm q0 q0 q0))).symm).trans ((((cg (fun t => (q3 ◇ q3) ◇ t) (h q0 q1 q3)).symm).trans ((h (q0 ◇ q1) q2 q3).symm)).trans (cg (fun t => t ◇ q3) (py q0 q1 q2)))).symm
  have p10 : forall (q0 q1 q2 q3:G), ((((q1 ◇ q0) ◇ q1) ◇ q2) ◇ q3) = (((q2 ◇ q2) ◇ q2) ◇ q3):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => t ◇ q3) (cg (fun t => t ◇ q2) ((h q1 q0 q1).symm))).symm).trans (pu q2 (q1 ◇ q1) q3)
  have p11 : forall (q0 q1 q2:G), ((((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0)) ◇ (q0 ◇ q1)) = (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q1)):=by
    intro q0 q1 q2
    exact (((((((cg (fun t => t ◇ (q0 ◇ q1)) (cg (fun t => t ◇ (q0 ◇ (q0 ◇ q1))) (py q0 q1 (q0 ◇ q1)))).trans (cg (fun t => t ◇ (q0 ◇ q1)) (py (q0 ◇ q0) (q0 ◇ q1) (q0 ◇ (q0 ◇ q1))))).trans (cg (fun t => t ◇ (q0 ◇ q1)) (cg (fun t => t ◇ (q0 ◇ (q0 ◇ q1))) (pm q0 q0 q0)))).trans (py ((q0 ◇ q0) ◇ q0) (q0 ◇ (q0 ◇ q1)) (q0 ◇ q1))).trans (pt q0 (q0 ◇ q0) (q0 ◇ q1))).trans (cg (fun t => t ◇ (q0 ◇ q1)) (cg (fun t => t ◇ (q0 ◇ q0)) (pm q0 q0 q0)))).symm).trans ((((cg (fun t => t ◇ (q0 ◇ q1)) (h q0 q1 (q0 ◇ q1))).symm).trans (po q2 (q0 ◇ q1))).trans ((cg (fun t => t ◇ (q0 ◇ q1)) (py q0 q1 q2)).trans (pz q0 q2 (q0 ◇ q1) (((q0 ◇ q0) ◇ q2) ◇ (q0 ◇ q1)))))
  have p12 : forall (q0 q1 q2 q3:G), (((q2 ◇ q1) ◇ q3) ◇ (q1 ◇ q1)) = (((q2 ◇ q0) ◇ q1) ◇ (q1 ◇ q1)):=by
    intro q0 q1 q2 q3
    exact (((((cg (fun t => t ◇ ((q2 ◇ q0) ◇ (q1 ◇ q1))) (pm q1 q1 q1)).trans (pm q1 (q1 ◇ q1) (q2 ◇ q0))).trans (pv q1 (q2 ◇ q0))).symm).trans (((cg (fun t => ((q1 ◇ q1) ◇ (q1 ◇ q1)) ◇ t) (pr q0 q1 q2)).symm).trans ((h (q2 ◇ q1) q3 (q1 ◇ q1)).symm))).symm
  have p13 : forall (q0 q1 q2 q3 q4:G), ((q4 ◇ q3) ◇ ((q1 ◇ q0) ◇ q1)) = ((q4 ◇ q2) ◇ ((q1 ◇ q1) ◇ q1)):=by
    intro q0 q1 q2 q3 q4
    exact (((cg (fun t => (q4 ◇ q3) ◇ t) ((h q1 q0 q1).symm)).symm).trans (pq q2 q3 (q1 ◇ q1) q4)).trans (cg (fun t => (q4 ◇ q2) ◇ t) (pm q1 q1 q1))
  have p14 : forall (q0 q1 q2 q3:G), (((q3 ◇ q3) ◇ q3) ◇ (q1 ◇ q0)) = (((q2 ◇ q2) ◇ q2) ◇ (q1 ◇ q0)):=by
    intro q0 q1 q2 q3
    exact (((p10 q0 q1 q2 (q1 ◇ q0)).symm).trans (px q1 q2 q3 q0 (q1 ◇ q0))).symm
  have p15 : forall (q0 q1 q2:G), (((q1 ◇ q0) ◇ q2) ◇ (q0 ◇ q0)) = (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0)):=by
    intro q0 q1 q2
    exact (((pu q0 q1 (q0 ◇ q0)).symm).trans (((cg (fun t => t ◇ (q0 ◇ q0)) (py q1 q0 q0)).symm).trans ((p12 q0 q0 q1 q2).symm))).symm
  have p16 : forall (q0 q1 q2 q3 q4:G), (((q3 ◇ q1) ◇ q0) ◇ (q2 ◇ q2)) = (((q2 ◇ q2) ◇ q2) ◇ (q2 ◇ q2)):=by
    intro q0 q1 q2 q3 q4
    exact (((pr q0 q2 (q3 ◇ q1)).symm).trans ((p12 q1 q2 q3 q4).symm)).trans (p15 q2 q3 q4)
  have p17 : forall (q0 q1 q2 q3 q4:G), ((q4 ◇ q3) ◇ ((q1 ◇ q0) ◇ q1)) = ((q4 ◇ q1) ◇ ((q1 ◇ q1) ◇ q1)):=by
    intro q0 q1 q2 q3 q4
    exact (p13 q0 q1 q2 q3 q4).trans ((p13 q1 q1 q2 q1 q4).symm)
  have p18 : forall (q0 q2 q1 q3:G), (((q0 ◇ q0) ◇ q0) ◇ ((q0 ◇ q0) ◇ q2)) = (((q2 ◇ q2) ◇ q2) ◇ (q0 ◇ q2)):=by
    intro q0 q2 q1 q3
    exact (((((cg (fun t => ((q0 ◇ q2) ◇ (q0 ◇ q2)) ◇ t) (py q0 q1 q2)).trans (cg (fun t => t ◇ ((q0 ◇ q0) ◇ q2)) (py q0 q2 (q0 ◇ q2)))).trans (py (q0 ◇ q0) (q0 ◇ q2) ((q0 ◇ q0) ◇ q2))).trans (cg (fun t => t ◇ ((q0 ◇ q0) ◇ q2)) (pm q0 q0 q0))).symm).trans ((((cg (fun t => ((q0 ◇ q2) ◇ (q0 ◇ q2)) ◇ t) ((h q0 q1 q2).symm)).symm).trans ((h (q2 ◇ q2) q3 (q0 ◇ q2)).symm)).trans (pz q2 q3 (q0 ◇ q2) (((q2 ◇ q2) ◇ q3) ◇ (q0 ◇ q2))))
  have p19 : forall (q0:G), (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0)) = ((q0 ◇ q0) ◇ q0):=by
    intro q0
    exact ((((((cg (fun t => t ◇ (q0 ◇ (q0 ◇ q0))) (cg (fun t => t ◇ (q0 ◇ q0)) (pm q0 q0 q0))).trans (p11 q0 (q0 ◇ q0) ((((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0)) ◇ (q0 ◇ (q0 ◇ q0))))).trans (pm q0 (q0 ◇ q0) q0)).trans (pm q0 q0 q0)).symm).trans ((((p18 q0 (q0 ◇ q0) q0 q0).symm).trans (pm q0 (q0 ◇ q0) (q0 ◇ q0))).trans (cg (fun t => t ◇ (q0 ◇ q0)) (pm q0 q0 q0)))).symm
  have p1a : forall (q0 q1 q2 q3 q4:G), (((q3 ◇ q1) ◇ q0) ◇ (q2 ◇ q2)) = ((q2 ◇ q2) ◇ q2):=by
    intro q0 q1 q2 q3 q4
    exact (p16 q0 q1 q2 q3 q4).trans (p19 q2)
  have p1b : forall (q0 q2 q3 q1:G), (((q0 ◇ q0) ◇ q0) ◇ (q3 ◇ (q2 ◇ q2))) = ((q3 ◇ q2) ◇ (q2 ◇ q2)):=by
    intro q0 q2 q3 q1
    exact (((cg (fun t => t ◇ (q3 ◇ (q2 ◇ q2))) (py q0 q1 q2)).trans (pz q0 q2 (q3 ◇ (q2 ◇ q2)) (((q0 ◇ q0) ◇ q2) ◇ (q3 ◇ (q2 ◇ q2))))).symm).trans ((((cg (fun t => t ◇ (q3 ◇ (q2 ◇ q2))) ((h q0 q1 q2).symm)).symm).trans (pm (q0 ◇ q2) (q2 ◇ q2) q3)).trans (pv q2 q3))
  have p1c : forall (q1 q2 q0 q3:G), ((q2 ◇ q1) ◇ (q1 ◇ q1)) = ((q1 ◇ q1) ◇ q1):=by
    intro q1 q2 q0 q3
    exact (((((((cg (fun t => t ◇ ((q2 ◇ q1) ◇ (q1 ◇ q1))) (py q2 (q1 ◇ q1) (q2 ◇ (q1 ◇ q1)))).trans (py (q2 ◇ q2) (q2 ◇ (q1 ◇ q1)) ((q2 ◇ q1) ◇ (q1 ◇ q1)))).trans (cg (fun t => t ◇ ((q2 ◇ q1) ◇ (q1 ◇ q1))) (pm q2 q2 q2))).trans (p1b q2 q1 (q2 ◇ q1) (((q2 ◇ q2) ◇ q2) ◇ ((q2 ◇ q1) ◇ (q1 ◇ q1))))).trans (p1a q1 q1 q1 q2 (((q2 ◇ q1) ◇ q1) ◇ (q1 ◇ q1)))).symm).trans ((((cg (fun t => ((q2 ◇ (q1 ◇ q1)) ◇ (q2 ◇ (q1 ◇ q1))) ◇ t) (p1b q0 q1 q2 q0)).symm).trans ((h ((q0 ◇ q0) ◇ q0) q3 (q2 ◇ (q1 ◇ q1))).symm)).trans ((p10 q0 q0 q3 (q2 ◇ (q1 ◇ q1))).trans (p1b q3 q1 q2 (((q3 ◇ q3) ◇ q3) ◇ (q2 ◇ (q1 ◇ q1))))))).symm
  have p1d : forall (q93 q94 q95 q0 q1 q2 q3:G), ((q95 ◇ q93) ◇ (q94 ◇ q94)) = ((q94 ◇ q94) ◇ q94):=by
    intro q93 q94 q95 q0 q1 q2 q3
    exact (((p1c q94 q95 ((q95 ◇ q94) ◇ (q94 ◇ q94)) ((q95 ◇ q94) ◇ (q94 ◇ q94))).symm).trans (pr q93 q94 q95)).symm
  have p1e : forall (q1 q2 q0:G), ((q2 ◇ q1) ◇ ((q1 ◇ q1) ◇ q1)) = ((q1 ◇ q1) ◇ q1):=by
    intro q1 q2 q0
    exact (((py q2 (q1 ◇ q1) ((q1 ◇ q0) ◇ q1)).trans (p17 q0 q1 ((q2 ◇ q2) ◇ ((q1 ◇ q0) ◇ q1)) q2 q2)).symm).trans ((((cg (fun t => (q2 ◇ (q1 ◇ q1)) ◇ t) ((h q1 q0 q1).symm)).symm).trans (p1c (q1 ◇ q1) q2 q0 q0)).trans ((cg (fun t => t ◇ (q1 ◇ q1)) (pm q1 q1 q1)).trans (p1d q1 q1 (q1 ◇ q1) (((q1 ◇ q1) ◇ q1) ◇ (q1 ◇ q1)) (((q1 ◇ q1) ◇ q1) ◇ (q1 ◇ q1)) (((q1 ◇ q1) ◇ q1) ◇ (q1 ◇ q1)) (((q1 ◇ q1) ◇ q1) ◇ (q1 ◇ q1)))))
  have p1f : forall (q0 q1:G), (((q0 ◇ q0) ◇ q0) ◇ q1) = ((q1 ◇ q1) ◇ q1):=by
    intro q0 q1
    exact ((((p1e q1 q1 q0).symm).trans ((h (q1 ◇ q1) q0 q1).symm)).trans (pu q0 q1 q1)).symm
  have p1g : forall (q106 q107 q108 q0 q1:G), (((q107 ◇ q106) ◇ q107) ◇ q108) = ((q108 ◇ q108) ◇ q108):=by
    intro q106 q107 q108 q0 q1
    exact (((p1f q107 q108).symm).trans (ps q106 q107 q108)).symm
  have p1h : forall (q0 q1 q2 q3:G), (((q0 ◇ q0) ◇ q2) ◇ (q3 ◇ (q0 ◇ q1))) = ((q3 ◇ q3) ◇ (q0 ◇ q1)):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => t ◇ (q3 ◇ (q0 ◇ q1))) (pm q2 q2 q0)).symm).trans (((cg (fun t => t ◇ (q3 ◇ (q0 ◇ q1))) (h q0 q1 q2)).symm).trans (pm q2 (q0 ◇ q1) q3))
  have p1i : forall (q0 q1 q2 q3:G), (((q2 ◇ q2) ◇ (q0 ◇ q1)) ◇ q3) = ((q3 ◇ q3) ◇ q3):=by
    intro q0 q1 q2 q3
    exact (((cg (fun t => t ◇ q3) (p1h q0 q1 (q0 ◇ q0) q2)).symm).trans (pu (q2 ◇ (q0 ◇ q1)) (q0 ◇ q0) q3)).trans ((((((((cg (fun t => t ◇ q3) (cg (fun t => t ◇ (q2 ◇ (q0 ◇ q1))) (py q2 (q0 ◇ q1) (q2 ◇ (q0 ◇ q1))))).trans (cg (fun t => t ◇ q3) (py (q2 ◇ q2) (q2 ◇ (q0 ◇ q1)) (q2 ◇ (q0 ◇ q1))))).trans (cg (fun t => t ◇ q3) (cg (fun t => t ◇ (q2 ◇ (q0 ◇ q1))) (pm q2 q2 q2)))).trans (h ((q2 ◇ q2) ◇ q2) (q2 ◇ (q0 ◇ q1)) q3)).trans (cg (fun t => (q3 ◇ q3) ◇ t) (p1g q2 q2 q3 (((q2 ◇ q2) ◇ q2) ◇ q3) (((q2 ◇ q2) ◇ q2) ◇ q3)))).trans (pm q3 q3 (q3 ◇ q3))).trans (cg (fun t => t ◇ q3) (pm q3 q3 q3))).trans (p1g q3 q3 q3 (((q3 ◇ q3) ◇ q3) ◇ q3) (((q3 ◇ q3) ◇ q3) ◇ q3)))
  have p1j : forall (q0 q1 q2 q3:G), (((q1 ◇ q0) ◇ q2) ◇ q3) = ((q3 ◇ q3) ◇ q3):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => t ◇ q3) ((h q1 q0 q2).symm)).symm).trans (p1i q1 q2 q2 q3)
  have p1k : forall (q0 q1 q2:G), (((q2 ◇ q2) ◇ q2) ◇ (q0 ◇ q1)) = ((q2 ◇ q2) ◇ (q0 ◇ q1)):=by
    intro q0 q1 q2
    exact (((((cg (fun t => t ◇ ((q2 ◇ q2) ◇ (q0 ◇ q1))) (cg (fun t => t ◇ (q0 ◇ q0)) (pm q0 q0 q0))).trans (cg (fun t => t ◇ ((q2 ◇ q2) ◇ (q0 ◇ q1))) (p1d q0 q0 (q0 ◇ q0) (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0)) (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0)) (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0)) (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0))))).trans (p1h q0 q1 q0 (q2 ◇ q2))).trans (cg (fun t => t ◇ (q0 ◇ q1)) (pm q2 q2 q2))).symm).trans ((((cg (fun t => (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ (q0 ◇ q0)) ◇ t) (p1h q0 q1 (q0 ◇ q0) q2)).symm).trans (p18 (q0 ◇ q0) (q2 ◇ (q0 ◇ q1)) q0 q0)).trans (((((((((cg (fun t => t ◇ ((q0 ◇ q0) ◇ (q2 ◇ (q0 ◇ q1)))) (cg (fun t => t ◇ (q2 ◇ (q0 ◇ q1))) (py q2 (q0 ◇ q1) (q2 ◇ (q0 ◇ q1))))).trans (cg (fun t => t ◇ ((q0 ◇ q0) ◇ (q2 ◇ (q0 ◇ q1)))) (py (q2 ◇ q2) (q2 ◇ (q0 ◇ q1)) (q2 ◇ (q0 ◇ q1))))).trans (cg (fun t => t ◇ ((q0 ◇ q0) ◇ (q2 ◇ (q0 ◇ q1)))) (cg (fun t => t ◇ (q2 ◇ (q0 ◇ q1))) (pm q2 q2 q2)))).trans (py ((q2 ◇ q2) ◇ q2) (q2 ◇ (q0 ◇ q1)) ((q0 ◇ q0) ◇ (q2 ◇ (q0 ◇ q1))))).trans (cg (fun t => t ◇ ((q0 ◇ q0) ◇ (q2 ◇ (q0 ◇ q1)))) (p18 q2 q2 (((q2 ◇ q2) ◇ q2) ◇ ((q2 ◇ q2) ◇ q2)) (((q2 ◇ q2) ◇ q2) ◇ ((q2 ◇ q2) ◇ q2))))).trans (cg (fun t => t ◇ ((q0 ◇ q0) ◇ (q2 ◇ (q0 ◇ q1)))) (p1d q2 q2 (q2 ◇ q2) (((q2 ◇ q2) ◇ q2) ◇ (q2 ◇ q2)) (((q2 ◇ q2) ◇ q2) ◇ (q2 ◇ q2)) (((q2 ◇ q2) ◇ q2) ◇ (q2 ◇ q2)) (((q2 ◇ q2) ◇ q2) ◇ (q2 ◇ q2))))).trans (p1h q2 (q0 ◇ q1) q2 (q0 ◇ q0))).trans (cg (fun t => t ◇ (q2 ◇ (q0 ◇ q1))) (pm q0 q0 q0))).trans (p1h q0 q1 q0 q2)))
  have p1l : forall (q0 q1 q2 q3:G), ((q3 ◇ q3) ◇ (q1 ◇ q0)) = ((q2 ◇ q2) ◇ (q1 ◇ q0)):=by
    intro q0 q1 q2 q3
    exact ((p1k q1 q0 q3).symm).trans ((p14 q0 q1 q2 q3).trans (p1k q1 q0 q2))
  have p1m : forall (q0 q1 q3 q2:G), ((q0 ◇ q0) ◇ (q1 ◇ q3)) = ((q1 ◇ q1) ◇ q3):=by
    intro q0 q1 q3 q2
    exact (((p1l q3 q1 q0 q3).symm).trans ((h q1 q2 q3).symm)).trans (py q1 q2 q3)
  have p1n : forall (q0 q1 q2 q3:G), ((q2 ◇ q2) ◇ q2) = ((q0 ◇ q0) ◇ q2):=by
    intro q0 q1 q2 q3
    exact ((((p1m q0 (q0 ◇ q0) q2 ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q2))).trans (cg (fun t => t ◇ q2) (pm q0 q0 q0))).trans (p1j q0 q0 q0 q2)).symm).trans ((((p1k (q0 ◇ q0) q2 q0).symm).trans ((p18 q0 q2 q1 q3).trans (p1k q0 q2 q2))).trans (pm q2 q2 q0))
  exact ((py x y z).trans ((p1n x u z u).symm)).trans ((p1j u w v z).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_60641_to_62572 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_60641_to_62572
