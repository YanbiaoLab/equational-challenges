-- Equation60607 → Equation61407
-- Recorded verdict: true
-- Premise: (x ◇ y) ◇ z = (z ◇ x) ◇ (x ◇ z)
-- Conclusion: (x ◇ y) ◇ z = (y ◇ (x ◇ x)) ◇ z
-- Original submission SHA-256: 30de0e8d79cb288c8a57d8ecf0af80937a7d7a8bc6afa49f857bc209d62992a6
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ z = (z ◇ x) ◇ (x ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ z = (y ◇ (x ◇ x)) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have p0 : forall (x y z:G), ((x ◇ y) ◇ z) = ((x ◇ x) ◇ z):=by
    intro x y z
    exact (h x y z).trans ((h x x z).symm)
  have p1 : forall (q5 q6 q7:G), ((q7 ◇ q7) ◇ (q5 ◇ q7)) = ((q5 ◇ q5) ◇ q7):=by
    intro q5 q6 q7
    exact (((p0 q7 q5 (q5 ◇ q7)).symm).trans ((h q5 q6 q7).symm)).trans (p0 q5 q6 q7)
  have p2 : forall (q5 q7:G), ((q7 ◇ q5) ◇ (q5 ◇ q7)) = ((q5 ◇ q5) ◇ q7):=by
    intro q5 q7
    exact (((p0 q5 q5 q7).symm).trans (h q5 q5 q7)).symm
  have p3 : forall (q8 q9 q10 q11:G), (((q8 ◇ q8) ◇ q10) ◇ ((q10 ◇ q10) ◇ q8)) = (((q8 ◇ q8) ◇ q11) ◇ (q10 ◇ q8)):=by
    intro q8 q9 q10 q11
    exact ((((cg (fun t => t ◇ ((q8 ◇ q10) ◇ (q10 ◇ q8))) (p0 q8 q9 q10)).trans (cg (fun t => ((q8 ◇ q8) ◇ q10) ◇ t) (p0 q8 q10 (q10 ◇ q8)))).trans (cg (fun t => ((q8 ◇ q8) ◇ q10) ◇ t) (p1 q10 ((q8 ◇ q8) ◇ (q10 ◇ q8)) q8))).symm).trans ((((cg (fun t => t ◇ ((q8 ◇ q10) ◇ (q10 ◇ q8))) ((h q8 q9 q10).symm)).symm).trans ((h (q8 ◇ q10) q11 (q10 ◇ q8)).symm)).trans (cg (fun t => t ◇ (q10 ◇ q8)) (p0 q8 q10 q11)))
  have p4 : forall (q12 q13 q14 q15:G), (((q12 ◇ q12) ◇ q14) ◇ q15) = (((q12 ◇ q12) ◇ q12) ◇ q15):=by
    intro q12 q13 q14 q15
    exact (((cg (fun t => t ◇ q15) (p0 q12 q13 q14)).symm).trans (p0 (q12 ◇ q13) q14 q15)).trans (((cg (fun t => t ◇ q15) (p0 q12 q13 (q12 ◇ q13))).trans (p0 (q12 ◇ q12) (q12 ◇ q13) q15)).trans (cg (fun t => t ◇ q15) (p1 q12 ((q12 ◇ q12) ◇ (q12 ◇ q12)) q12)))
  have p5 : forall (q16 q17 q18:G), (((q17 ◇ q17) ◇ q17) ◇ q18) = (((q17 ◇ q16) ◇ q17) ◇ q18):=by
    intro q16 q17 q18
    exact (((cg (fun t => t ◇ q18) ((h q17 q16 q17).symm)).symm).trans (p4 q17 q16 (q17 ◇ q17) q18)).symm
  have p6 : forall (q19 q20 q21:G), (((q20 ◇ q20) ◇ q20) ◇ q21) = (((q19 ◇ q19) ◇ q19) ◇ q21):=by
    intro q19 q20 q21
    exact (((p4 q19 (((q19 ◇ q19) ◇ q20) ◇ q21) q20 q21).symm).trans (((cg (fun t => t ◇ q21) (p1 q19 q19 q20)).symm).trans (p4 q20 q19 (q19 ◇ q20) q21))).symm
  have p7 : forall (q22 q23 q24 q25:G), (((q24 ◇ q23) ◇ q24) ◇ q25) = (((q22 ◇ q22) ◇ q22) ◇ q25):=by
    intro q22 q23 q24 q25
    exact (((p6 q22 q24 q25).symm).trans (p5 q23 q24 q25)).symm
  have p8 : forall (q8 q9 q10 q26:G), (((q10 ◇ q8) ◇ (q10 ◇ q8)) ◇ q26) = (((q8 ◇ q8) ◇ q8) ◇ q26):=by
    intro q8 q9 q10 q26
    exact ((((cg (fun t => t ◇ q26) (p0 q8 q9 q10)).trans (p4 q8 (((q8 ◇ q8) ◇ q10) ◇ q26) q10 q26)).symm).trans ((((cg (fun t => t ◇ q26) ((h q8 q9 q10).symm)).symm).trans (h (q10 ◇ q8) (q8 ◇ q10) q26)).trans ((p0 q26 (q10 ◇ q8) ((q10 ◇ q8) ◇ q26)).trans (p1 (q10 ◇ q8) ((q26 ◇ q26) ◇ ((q10 ◇ q8) ◇ q26)) q26)))).symm
  have p9 : forall (q8 q9 q27 q11:G), (((q8 ◇ q8) ◇ q8) ◇ (q27 ◇ (q8 ◇ q9))) = ((q27 ◇ q27) ◇ (q8 ◇ q9)):=by
    intro q8 q9 q27 q11
    exact (((cg (fun t => t ◇ (q27 ◇ (q8 ◇ q9))) (p2 q8 q27)).trans (p4 q8 (((q8 ◇ q8) ◇ q27) ◇ (q27 ◇ (q8 ◇ q9))) q27 (q27 ◇ (q8 ◇ q9)))).symm).trans ((((cg (fun t => t ◇ (q27 ◇ (q8 ◇ q9))) (h q8 q9 q27)).symm).trans ((h q27 q11 (q8 ◇ q9)).symm)).trans (p0 q27 q11 (q8 ◇ q9)))
  have pa : forall (q28 q29 q30:G), (((q28 ◇ q28) ◇ q28) ◇ ((q28 ◇ q28) ◇ q29)) = (((q29 ◇ q29) ◇ q29) ◇ (q28 ◇ q29)):=by
    intro q28 q29 q30
    exact ((((cg (fun t => t ◇ ((q28 ◇ q28) ◇ q29)) (p0 q28 q29 (q29 ◇ q29))).trans (p0 (q28 ◇ q28) (q29 ◇ q29) ((q28 ◇ q28) ◇ q29))).trans (cg (fun t => t ◇ ((q28 ◇ q28) ◇ q29)) (p1 q28 ((q28 ◇ q28) ◇ (q28 ◇ q28)) q28))).symm).trans ((((cg (fun t => ((q28 ◇ q29) ◇ (q29 ◇ q29)) ◇ t) (p1 q28 q28 q29)).symm).trans ((h (q29 ◇ q29) q30 (q28 ◇ q29)).symm)).trans (p4 q29 (((q29 ◇ q29) ◇ q30) ◇ (q28 ◇ q29)) q30 (q28 ◇ q29)))
  have pb : forall (q31 q32 q33:G), (((q33 ◇ q33) ◇ q33) ◇ (q31 ◇ q33)) = (((q31 ◇ q31) ◇ q31) ◇ (q31 ◇ q33)):=by
    intro q31 q32 q33
    exact ((((((cg (fun t => ((q31 ◇ q33) ◇ (q31 ◇ q33)) ◇ t) (p0 q31 q32 q33)).trans (cg (fun t => t ◇ ((q31 ◇ q31) ◇ q33)) (p0 q31 q33 (q31 ◇ q33)))).trans (p0 (q31 ◇ q31) (q31 ◇ q33) ((q31 ◇ q31) ◇ q33))).trans (cg (fun t => t ◇ ((q31 ◇ q31) ◇ q33)) (p1 q31 ((q31 ◇ q31) ◇ (q31 ◇ q31)) q31))).trans (pa q31 q33 (((q31 ◇ q31) ◇ q31) ◇ ((q31 ◇ q31) ◇ q33)))).symm).trans ((((cg (fun t => ((q31 ◇ q33) ◇ (q31 ◇ q33)) ◇ t) ((h q31 q32 q33).symm)).symm).trans (p1 (q33 ◇ q31) q31 (q31 ◇ q33))).trans (p8 q31 (((q33 ◇ q31) ◇ (q33 ◇ q31)) ◇ (q31 ◇ q33)) q33 (q31 ◇ q33)))
  have pc : forall (q34 q35:G), (((q34 ◇ q34) ◇ q34) ◇ ((q34 ◇ q34) ◇ q35)) = (((q34 ◇ q34) ◇ q34) ◇ (q34 ◇ q35)):=by
    intro q34 q35
    exact ((((cg (fun t => t ◇ ((q34 ◇ q34) ◇ q35)) (p0 q34 q35 (q34 ◇ q35))).trans (p0 (q34 ◇ q34) (q34 ◇ q35) ((q34 ◇ q34) ◇ q35))).trans (cg (fun t => t ◇ ((q34 ◇ q34) ◇ q35)) (p1 q34 ((q34 ◇ q34) ◇ (q34 ◇ q34)) q34))).symm).trans ((((cg (fun t => ((q34 ◇ q35) ◇ (q34 ◇ q35)) ◇ t) (p1 q34 q34 q35)).symm).trans (p1 (q35 ◇ q35) q34 (q34 ◇ q35))).trans ((cg (fun t => t ◇ (q34 ◇ q35)) (p1 q35 ((q35 ◇ q35) ◇ (q35 ◇ q35)) q35)).trans (pb q34 (((q35 ◇ q35) ◇ q35) ◇ (q34 ◇ q35)) q35)))
  have pd : forall (q36 q37 q38 q39 q40:G), (((q40 ◇ q39) ◇ q40) ◇ (q37 ◇ (q38 ◇ q36))) = ((q37 ◇ q37) ◇ (q38 ◇ q36)):=by
    intro q36 q37 q38 q39 q40
    exact (((p9 q38 q36 q37 q36).symm).trans ((p7 q38 q39 q40 (q37 ◇ (q38 ◇ q36))).symm)).symm
  have pe : forall (q41 q42:G), (((q41 ◇ q41) ◇ q41) ◇ (q42 ◇ q42)) = ((q41 ◇ q41) ◇ (q42 ◇ q42)):=by
    intro q41 q42
    exact ((((((cg (fun t => ((q41 ◇ q41) ◇ q42) ◇ t) (p0 q41 q42 (q42 ◇ q42))).trans (p4 q41 (((q41 ◇ q41) ◇ q42) ◇ ((q41 ◇ q41) ◇ (q42 ◇ q42))) q42 ((q41 ◇ q41) ◇ (q42 ◇ q42)))).trans (pc q41 (q42 ◇ q42))).trans (pd q42 q41 q42 q41 q41)).symm).trans ((((cg (fun t => t ◇ ((q41 ◇ q42) ◇ (q42 ◇ q42))) (p1 q41 q41 q42)).symm).trans (p2 (q41 ◇ q42) (q42 ◇ q42))).trans (((cg (fun t => t ◇ (q42 ◇ q42)) (p0 q41 q42 (q41 ◇ q42))).trans (p0 (q41 ◇ q41) (q41 ◇ q42) (q42 ◇ q42))).trans (cg (fun t => t ◇ (q42 ◇ q42)) (p1 q41 ((q41 ◇ q41) ◇ (q41 ◇ q41)) q41))))).symm
  have pf : forall (q43 q44 q45:G), (((q45 ◇ q44) ◇ q45) ◇ (q43 ◇ q43)) = ((q45 ◇ q45) ◇ (q43 ◇ q43)):=by
    intro q43 q44 q45
    exact (((pe q45 q43).symm).trans (p5 q44 q45 (q43 ◇ q43))).symm
  have pg : forall (q46 q47 q48:G), ((q48 ◇ q48) ◇ (q46 ◇ q46)) = ((q47 ◇ q47) ◇ (q46 ◇ q46)):=by
    intro q46 q47 q48
    exact (((pe q48 q46).symm).trans (p7 q47 q48 q48 (q46 ◇ q46))).trans (pf q46 q47 q47)
  have ph : forall (q49 q50 q51:G), ((q49 ◇ q49) ◇ (q50 ◇ q50)) = ((q50 ◇ q50) ◇ q50):=by
    intro q49 q50 q51
    exact (((pg q50 q49 q50).symm).trans ((h q50 q51 q50).symm)).trans (p0 q50 q51 q50)
  have pi : forall (q52 q53 q54 q55:G), ((((q52 ◇ q52) ◇ q52) ◇ (q53 ◇ q52)) ◇ q55) = ((((q52 ◇ q52) ◇ q52) ◇ (q52 ◇ q53)) ◇ q55):=by
    intro q52 q53 q54 q55
    exact ((cg (fun t => t ◇ q55) (p4 q52 (((q52 ◇ q52) ◇ q54) ◇ (q53 ◇ q52)) q54 (q53 ◇ q52))).symm).trans ((((cg (fun t => t ◇ q55) (p3 q52 q52 q53 q54)).symm).trans (p0 ((q52 ◇ q52) ◇ q53) ((q53 ◇ q53) ◇ q52) q55)).trans ((cg (fun t => t ◇ q55) (p4 q52 (((q52 ◇ q52) ◇ q53) ◇ ((q52 ◇ q52) ◇ q53)) q53 ((q52 ◇ q52) ◇ q53))).trans (cg (fun t => t ◇ q55) (pc q52 q53))))
  have pj : forall (q56 q57 q58 q59:G), ((q59 ◇ q59) ◇ (((q56 ◇ q56) ◇ q56) ◇ q59)) = ((((q56 ◇ q56) ◇ q56) ◇ (q56 ◇ q57)) ◇ q59):=by
    intro q56 q57 q58 q59
    exact ((((cg (fun t => t ◇ q59) (p4 q56 (((q56 ◇ q56) ◇ q58) ◇ (q57 ◇ q56)) q58 (q57 ◇ q56))).trans (pi q56 q57 ((((q56 ◇ q56) ◇ q56) ◇ (q57 ◇ q56)) ◇ q59) q59)).symm).trans ((((cg (fun t => t ◇ q59) (p3 q56 q56 q57 q58)).symm).trans (h ((q56 ◇ q56) ◇ q57) ((q57 ◇ q57) ◇ q56) q59)).trans ((cg (fun t => (q59 ◇ ((q56 ◇ q56) ◇ q57)) ◇ t) (p4 q56 (((q56 ◇ q56) ◇ q57) ◇ q59) q57 q59)).trans (p0 q59 ((q56 ◇ q56) ◇ q57) (((q56 ◇ q56) ◇ q56) ◇ q59))))).symm
  have pk : forall (q60 q61 q62:G), ((q62 ◇ q62) ◇ (((q61 ◇ q61) ◇ q61) ◇ q62)) = (((q60 ◇ q60) ◇ q60) ◇ q62):=by
    intro q60 q61 q62
    exact (pj q61 q61 q60 q62).trans (p7 q60 q61 (q61 ◇ q61) q62)
  have pl : forall (q32 q63:G), ((q63 ◇ q63) ◇ q63) = ((q63 ◇ q32) ◇ q63):=by
    intro q32 q63
    exact ((h q63 q32 q63).trans (p1 q63 q32 q63)).symm
  have pm : forall (q64 q65:G), (((q65 ◇ q65) ◇ q64) ◇ (q65 ◇ q65)) = ((q65 ◇ q65) ◇ q65):=by
    intro q64 q65
    exact ((pl q64 (q65 ◇ q65)).symm).trans (ph (q65 ◇ q65) q65 q64)
  have pn : forall (q66 q67 q68:G), ((q68 ◇ q68) ◇ (q68 ◇ q67)) = ((q68 ◇ q66) ◇ (q68 ◇ q67)):=by
    intro q66 q67 q68
    exact ((h q68 q66 (q68 ◇ q67)).trans (pd q67 q68 q68 q67 q68)).symm
  have po : forall (q66 q67 q68:G), ((q68 ◇ q67) ◇ (q68 ◇ q67)) = ((q68 ◇ q66) ◇ (q68 ◇ q67)):=by
    intro q66 q67 q68
    exact (((pn q66 q67 q68).symm).trans (pn q67 q67 q68)).symm
  have pp : forall (q69 q70 q71:G), ((q70 ◇ q69) ◇ (q70 ◇ q70)) = ((q70 ◇ q70) ◇ q70):=by
    intro q69 q70 q71
    exact (((pn q69 q70 q70).symm).trans ((h q70 q71 q70).symm)).trans (p0 q70 q71 q70)
  have pq : forall (q72 q73 q74 q75:G), ((q75 ◇ q73) ◇ (q75 ◇ q74)) = ((q75 ◇ q72) ◇ (q75 ◇ q74)):=by
    intro q72 q73 q74 q75
    exact (((pn q72 q74 q75).symm).trans (pn q73 q74 q75)).symm
  have pr : forall (q76 q77:G), ((q77 ◇ q77) ◇ (q77 ◇ q76)) = ((q77 ◇ q76) ◇ (q77 ◇ q76)):=by
    intro q76 q77
    exact ((po q76 q76 q77).trans (p0 q77 q76 (q77 ◇ q76))).symm
  have ps : forall (q78 q79 q80:G), (((q79 ◇ q78) ◇ q80) ◇ (q79 ◇ q78)) = (((q78 ◇ q78) ◇ q78) ◇ (q79 ◇ q78)):=by
    intro q78 q79 q80
    exact (((p8 q78 (((q79 ◇ q78) ◇ (q79 ◇ q78)) ◇ (q79 ◇ q78)) q79 (q79 ◇ q78)).symm).trans (((cg (fun t => t ◇ (q79 ◇ q78)) ((po q78 q78 q79).symm)).symm).trans (pl q80 (q79 ◇ q78)))).symm
  have pt : forall (q81 q82:G), (((q82 ◇ q82) ◇ q82) ◇ q82) = (((q81 ◇ q81) ◇ q81) ◇ q82):=by
    intro q81 q82
    exact (((p1 (q82 ◇ q82) ((q82 ◇ q82) ◇ ((q82 ◇ q82) ◇ q82)) q82).trans (cg (fun t => t ◇ q82) (p1 q82 ((q82 ◇ q82) ◇ (q82 ◇ q82)) q82))).symm).trans ((((cg (fun t => (q82 ◇ q82) ◇ t) ((pl q81 q82).symm)).symm).trans (p1 (q82 ◇ q81) q81 q82)).trans (p8 q81 (((q82 ◇ q81) ◇ (q82 ◇ q81)) ◇ q82) q82 q82))
  have pu : forall (q60 q61 q62:G), ((q62 ◇ q62) ◇ (((q61 ◇ q61) ◇ q61) ◇ q62)) = ((q62 ◇ q62) ◇ (((q60 ◇ q60) ◇ q60) ◇ q62)):=by
    intro q60 q61 q62
    exact (pk q60 q61 q62).trans ((pk q60 q60 q62).symm)
  have pv : forall (q83 q84 q85:G), (((q85 ◇ q85) ◇ q85) ◇ q85) = (((q84 ◇ q83) ◇ q84) ◇ q85):=by
    intro q83 q84 q85
    exact (((cg (fun t => t ◇ q85) (pl q83 q84)).symm).trans ((pt q84 q85).symm)).symm
  have pw : forall (x y z:G), ((x ◇ y) ◇ z) = ((x ◇ x) ◇ z):=by
    intro x y z
    exact (h x y z).trans ((h x x z).symm)
  have px : forall (q0 q1 q2 q3 q4:G), (((q3 ◇ q2) ◇ q3) ◇ q4) = (((q1 ◇ q0) ◇ q1) ◇ q4):=by
    intro q0 q1 q2 q3 q4
    exact (((pv q0 q1 q4).symm).trans (pv q2 q3 q4)).symm
  have py : forall (q0 q2 q1:G), ((q2 ◇ q2) ◇ (q0 ◇ q2)) = ((q0 ◇ q0) ◇ q2):=by
    intro q0 q2 q1
    exact (((pw q2 q0 (q0 ◇ q2)).symm).trans ((h q0 q1 q2).symm)).trans (pw q0 q1 q2)
  have pz : forall (q0 q2 q3 q1:G), (((q0 ◇ q0) ◇ q2) ◇ q3) = (((q0 ◇ q0) ◇ q0) ◇ q3):=by
    intro q0 q2 q3 q1
    exact (((cg (fun t => t ◇ q3) (pw q0 q1 q2)).symm).trans (pw (q0 ◇ q1) q2 q3)).trans (((cg (fun t => t ◇ q3) (pw q0 q1 (q0 ◇ q1))).trans (pw (q0 ◇ q0) (q0 ◇ q1) q3)).trans (cg (fun t => t ◇ q3) (pp q0 q0 ((q0 ◇ q0) ◇ (q0 ◇ q0)))))
  have p10 : forall (q0 q1 q2:G), (((q2 ◇ q1) ◇ q2) ◇ (q0 ◇ q0)) = ((q0 ◇ q0) ◇ q0):=by
    intro q0 q1 q2
    exact ((((cg (fun t => t ◇ (q0 ◇ q0)) (pm q0 q0)).trans (pm q0 q0)).symm).trans (((cg (fun t => t ◇ (q0 ◇ q0)) (cg (fun t => t ◇ (q0 ◇ q0)) (pp q0 q0 q0))).symm).trans (pv q1 q2 (q0 ◇ q0)))).symm
  have p11 : forall (q0 q1 q2 q3:G), (((q2 ◇ q0) ◇ q3) ◇ (q2 ◇ q1)) = (((q1 ◇ q1) ◇ q1) ◇ (q2 ◇ q1)):=by
    intro q0 q1 q2 q3
    exact ((((pp (q2 ◇ q0) (q2 ◇ q1) (((q2 ◇ q1) ◇ (q2 ◇ q0)) ◇ ((q2 ◇ q1) ◇ (q2 ◇ q1)))).trans (ps q1 q2 (q2 ◇ q1))).symm).trans (((cg (fun t => ((q2 ◇ q1) ◇ (q2 ◇ q0)) ◇ t) ((po q0 q1 q2).symm)).symm).trans ((h (q2 ◇ q0) q3 (q2 ◇ q1)).symm))).symm
  have p12 : forall (q0 q1 q2 q3:G), (((q2 ◇ q2) ◇ q2) ◇ (q3 ◇ q2)) = (((q1 ◇ q0) ◇ q1) ◇ (q3 ◇ q2)):=by
    intro q0 q1 q2 q3
    exact ((((px q0 q1 q2 q3 (q3 ◇ q2)).symm).trans ((pl q3 (q3 ◇ q2)).symm)).trans (ps q2 q3 (q3 ◇ q2))).symm
  have p13 : forall (q0 q1 q2 q3:G), (((q2 ◇ q2) ◇ q2) ◇ (q3 ◇ q2)) = (((q1 ◇ q0) ◇ q3) ◇ (q3 ◇ q2)):=by
    intro q0 q1 q2 q3
    exact (((cg (fun t => t ◇ (q3 ◇ q2)) ((h q1 q0 q3).symm)).symm).trans (p11 q1 q2 q3 (q1 ◇ q3))).symm
  have p14 : forall (q0 q1 q2 q3:G), ((((q1 ◇ q0) ◇ q1) ◇ q2) ◇ q3) = (((q1 ◇ q1) ◇ q1) ◇ q3):=by
    intro q0 q1 q2 q3
    exact (((cg (fun t => t ◇ q3) (cg (fun t => t ◇ q2) ((h q1 q0 q1).symm))).symm).trans (pz (q1 ◇ q1) q2 q3 q0)).trans ((cg (fun t => t ◇ q3) (cg (fun t => t ◇ (q1 ◇ q1)) (pp q1 q1 ((q1 ◇ q1) ◇ (q1 ◇ q1))))).trans (cg (fun t => t ◇ q3) (pm q1 q1)))
  have p15 : forall (q0 q1 q2:G), (((q1 ◇ q1) ◇ q1) ◇ ((q1 ◇ q0) ◇ q1)) = ((q1 ◇ q1) ◇ q1):=by
    intro q0 q1 q2
    exact ((pz q1 q2 ((q1 ◇ q0) ◇ q1) (((q1 ◇ q1) ◇ q2) ◇ ((q1 ◇ q0) ◇ q1))).symm).trans ((((cg (fun t => ((q1 ◇ q1) ◇ q2) ◇ t) ((h q1 q0 q1).symm)).symm).trans (pp q2 (q1 ◇ q1) q0)).trans ((cg (fun t => t ◇ (q1 ◇ q1)) (pp q1 q1 ((q1 ◇ q1) ◇ (q1 ◇ q1)))).trans (pm q1 q1)))
  have p16 : forall (q0 q1 q2:G), (((q1 ◇ q1) ◇ q1) ◇ (q1 ◇ (q1 ◇ q0))) = ((q1 ◇ q0) ◇ (q1 ◇ q0)):=by
    intro q0 q1 q2
    exact (((cg (fun t => t ◇ (q1 ◇ (q1 ◇ q0))) ((pl q0 q1).symm)).symm).trans ((h q1 q2 (q1 ◇ q0)).symm)).trans ((pw q1 q2 (q1 ◇ q0)).trans (pr q0 q1))
  have p17 : forall (q0 q1 q2:G), (((q0 ◇ q0) ◇ q0) ◇ (q1 ◇ q0)) = ((q1 ◇ q0) ◇ (q1 ◇ q0)):=by
    intro q0 q1 q2
    exact (((((((cg (fun t => t ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))) (pw q1 (q1 ◇ q0) ((q1 ◇ q1) ◇ q1))).trans (cg (fun t => t ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))) (py (q1 ◇ q1) q1 ((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ q1))))).trans (cg (fun t => t ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))) (cg (fun t => t ◇ q1) (pp q1 q1 ((q1 ◇ q1) ◇ (q1 ◇ q1)))))).trans (p14 q1 q1 q1 ((q1 ◇ q0) ◇ (q1 ◇ q0)))).trans (p10 (q1 ◇ q0) q1 q1)).trans (ps q0 q1 (q1 ◇ q0))).symm).trans ((((cg (fun t => ((q1 ◇ (q1 ◇ q0)) ◇ ((q1 ◇ q1) ◇ q1)) ◇ t) (p16 q0 q1 q0)).symm).trans ((h ((q1 ◇ q1) ◇ q1) q2 (q1 ◇ (q1 ◇ q0))).symm)).trans ((p14 q1 q1 q2 (q1 ◇ (q1 ◇ q0))).trans (p16 q0 q1 (((q1 ◇ q1) ◇ q1) ◇ (q1 ◇ (q1 ◇ q0))))))
  have p18 : forall (q0 q1 q2 q3:G), (((q1 ◇ q0) ◇ q1) ◇ (q3 ◇ q2)) = ((q3 ◇ q2) ◇ (q3 ◇ q2)):=by
    intro q0 q1 q2 q3
    exact (((p17 q2 q3 (((q2 ◇ q2) ◇ q2) ◇ (q3 ◇ q2))).symm).trans (p12 q0 q1 q2 q3)).symm
  have p19 : forall (q0 q1 q2 q3:G), (((q1 ◇ q0) ◇ q3) ◇ (q3 ◇ q2)) = ((q3 ◇ q2) ◇ (q3 ◇ q2)):=by
    intro q0 q1 q2 q3
    exact (((p17 q2 q3 (((q2 ◇ q2) ◇ q2) ◇ (q3 ◇ q2))).symm).trans (p13 q0 q1 q2 q3)).symm
  have p1a : forall (q0 q1 q2:G), ((q2 ◇ q2) ◇ (q2 ◇ (q1 ◇ q0))) = ((q2 ◇ q2) ◇ (q1 ◇ q0)):=by
    intro q0 q1 q2
    exact (((((cg (fun t => t ◇ (q2 ◇ (q1 ◇ q0))) (ps q0 q1 (q1 ◇ q0))).trans (cg (fun t => t ◇ (q2 ◇ (q1 ◇ q0))) (p18 q0 q0 q0 q1))).trans (py q2 (q1 ◇ q0) (((q1 ◇ q0) ◇ (q1 ◇ q0)) ◇ (q2 ◇ (q1 ◇ q0))))).symm).trans ((((cg (fun t => t ◇ (q2 ◇ (q1 ◇ q0))) (cg (fun t => t ◇ (q1 ◇ q0)) ((po q0 q0 q1).symm))).symm).trans (p17 (q1 ◇ q0) q2 q0)).trans (pw q2 (q1 ◇ q0) (q2 ◇ (q1 ◇ q0))))).symm
  have p1b : forall (q0 q1 q2 q3:G), ((q3 ◇ q3) ◇ (q2 ◇ q1)) = ((q3 ◇ q0) ◇ (q2 ◇ q1)):=by
    intro q0 q1 q2 q3
    exact (((h q3 q0 (q2 ◇ q1)).trans (p19 q1 q2 (q2 ◇ q1) q3)).trans ((pw q3 (q2 ◇ q1) (q3 ◇ (q2 ◇ q1))).trans (p1a q1 q2 q3))).symm
  have p1c : forall (q0 q1 q2:G), ((q2 ◇ q0) ◇ (q1 ◇ q2)) = ((q1 ◇ q1) ◇ q2):=by
    intro q0 q1 q2
    exact ((p1b q0 q2 q1 q2).symm).trans (py q1 q2 q0)
  have p1d : forall (q0 q1 q2 q3:G), ((q3 ◇ q1) ◇ (q2 ◇ q1)) = ((q3 ◇ q0) ◇ (q2 ◇ q1)):=by
    intro q0 q1 q2 q3
    exact (((p1b q0 q1 q2 q3).symm).trans (p1b q1 q1 q2 q3)).symm
  have p1e : forall (q0 q1 q2:G), ((q2 ◇ q2) ◇ (q1 ◇ q0)) = ((q2 ◇ q0) ◇ (q1 ◇ q0)):=by
    intro q0 q1 q2
    exact ((p1d q0 q0 q1 q2).trans (pw q2 q0 (q1 ◇ q0))).symm
  have p1f : forall (q0 q1 q2 q3:G), ((q3 ◇ q2) ◇ (q3 ◇ (q1 ◇ q0))) = ((q3 ◇ q0) ◇ (q1 ◇ q0)):=by
    intro q0 q1 q2 q3
    exact (((p1e q0 q1 q3).symm).trans (((p1a q0 q1 q3).symm).trans (pq q2 q3 (q1 ◇ q0) q3))).symm
  have p1g : forall (q0 q1 q2:G), (((q2 ◇ q0) ◇ q2) ◇ ((q2 ◇ q1) ◇ q2)) = ((q2 ◇ q2) ◇ q2):=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ ((q2 ◇ q1) ◇ q2)) (pl q0 q2)).symm).trans (p15 q1 q2 q0)
  have p1h : forall (q0 q1 q2 q3 q4:G), (((q3 ◇ q0) ◇ (q2 ◇ q1)) ◇ q4) = (((q3 ◇ q3) ◇ q3) ◇ q4):=by
    intro q0 q1 q2 q3 q4
    exact (((cg (fun t => t ◇ q4) (p1b q0 q1 q2 q3)).symm).trans (pw (q3 ◇ q3) (q2 ◇ q1) q4)).trans (cg (fun t => t ◇ q4) (pp q3 q3 ((q3 ◇ q3) ◇ (q3 ◇ q3))))
  have p1i : forall (q0 q1 q2 q3:G), (((q2 ◇ q0) ◇ q1) ◇ q3) = (((q1 ◇ q1) ◇ q1) ◇ q3):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => t ◇ q3) ((h q2 q0 q1).symm)).symm).trans (p1h q2 q1 q2 q1 q3)
  have p1j : forall (q0 q1 q2 q3 q4:G), (((q3 ◇ q0) ◇ q4) ◇ (q2 ◇ q1)) = ((q2 ◇ q1) ◇ (q2 ◇ q1)):=by
    intro q0 q1 q2 q3 q4
    exact ((((((((cg (fun t => ((q2 ◇ q1) ◇ (q3 ◇ q0)) ◇ t) (p1e q1 q2 q3)).trans (pw (q2 ◇ q1) (q3 ◇ q0) ((q3 ◇ q1) ◇ (q2 ◇ q1)))).trans (p1c (q2 ◇ q1) (q3 ◇ q1) (q2 ◇ q1))).trans (p1e q1 q2 (q3 ◇ q1))).trans (p1i q1 q1 q3 (q2 ◇ q1))).trans (p18 q1 q1 q1 q2)).symm).trans (((cg (fun t => ((q2 ◇ q1) ◇ (q3 ◇ q0)) ◇ t) ((p1b q0 q1 q2 q3).symm)).symm).trans ((h (q3 ◇ q0) q4 (q2 ◇ q1)).symm))).symm
  have p1k : forall (q0 q1 q2 q3:G), (((q0 ◇ q0) ◇ q0) ◇ (q2 ◇ (q0 ◇ q1))) = ((q2 ◇ q1) ◇ (q0 ◇ q1)):=by
    intro q0 q1 q2 q3
    exact ((pz q0 q2 (q2 ◇ (q0 ◇ q1)) (((q0 ◇ q0) ◇ q2) ◇ (q2 ◇ (q0 ◇ q1)))).symm).trans ((((cg (fun t => t ◇ (q2 ◇ (q0 ◇ q1))) (pw q0 q1 q2)).symm).trans ((h q2 q3 (q0 ◇ q1)).symm)).trans ((pw q2 q3 (q0 ◇ q1)).trans (p1e q1 q0 q2)))
  have p1l : forall (q0 q1 q3 q2:G), ((q3 ◇ q0) ◇ (q3 ◇ q0)) = ((q1 ◇ q0) ◇ (q3 ◇ q0)):=by
    intro q0 q1 q3 q2
    exact (((((((cg (fun t => t ◇ ((q1 ◇ q0) ◇ (q3 ◇ q0))) (pw q1 (q3 ◇ q0) (q1 ◇ (q3 ◇ q0)))).trans (cg (fun t => t ◇ ((q1 ◇ q0) ◇ (q3 ◇ q0))) (p1f q0 q3 q1 q1))).trans (pw (q1 ◇ q0) (q3 ◇ q0) ((q1 ◇ q0) ◇ (q3 ◇ q0)))).trans (p1f q0 q3 (q1 ◇ q0) (q1 ◇ q0))).trans (p1i q0 q0 q1 (q3 ◇ q0))).trans (p1j q0 q0 q3 q0 q0)).symm).trans ((((cg (fun t => ((q1 ◇ (q3 ◇ q0)) ◇ (q1 ◇ (q3 ◇ q0))) ◇ t) (p1k q3 q0 q1 q0)).symm).trans (pu q2 q3 (q1 ◇ (q3 ◇ q0)))).trans ((((((((cg (fun t => t ◇ (((q2 ◇ q2) ◇ q2) ◇ (q1 ◇ (q3 ◇ q0)))) (pw q1 (q3 ◇ q0) (q1 ◇ (q3 ◇ q0)))).trans (cg (fun t => t ◇ (((q2 ◇ q2) ◇ q2) ◇ (q1 ◇ (q3 ◇ q0)))) (p1f q0 q3 q1 q1))).trans (pw (q1 ◇ q0) (q3 ◇ q0) (((q2 ◇ q2) ◇ q2) ◇ (q1 ◇ (q3 ◇ q0))))).trans (p1h q0 q0 q1 q1 (((q2 ◇ q2) ◇ q2) ◇ (q1 ◇ (q3 ◇ q0))))).trans (p1k q1 (q3 ◇ q0) ((q2 ◇ q2) ◇ q2) (((q1 ◇ q1) ◇ q1) ◇ (((q2 ◇ q2) ◇ q2) ◇ (q1 ◇ (q3 ◇ q0)))))).trans (cg (fun t => t ◇ (q1 ◇ (q3 ◇ q0))) (p1j q2 q0 q3 q2 q2))).trans (p1c (q3 ◇ q0) q1 (q3 ◇ q0))).trans (p1e q0 q3 q1)))
  have p1m : forall (q0 q1 q2 q3:G), ((q1 ◇ q0) ◇ (q3 ◇ q0)) = ((q3 ◇ q3) ◇ q0):=by
    intro q0 q1 q2 q3
    exact (((p1l q0 q1 q3 q2).symm).trans (p1l q0 q0 q3 q2)).trans (p1c q0 q3 q0)
  have p1n : forall (q0 q1 q2 q3:G), (((q1 ◇ q1) ◇ q1) ◇ q2) = ((q2 ◇ q2) ◇ q2):=by
    intro q0 q1 q2 q3
    exact ((p1i q2 q1 q2 q2).symm).trans ((((p1m q2 (q2 ◇ q0) (((q2 ◇ q0) ◇ q2) ◇ ((q2 ◇ q1) ◇ q2)) (q2 ◇ q1)).trans (cg (fun t => t ◇ q2) (p1m q1 q2 ((q2 ◇ q1) ◇ (q2 ◇ q1)) q2))).symm).trans (p1g q0 q1 q2))
  have p1o : forall (q0 q1 q2:G), ((q1 ◇ q1) ◇ q0) = ((q0 ◇ q0) ◇ q0):=by
    intro q0 q1 q2
    exact ((((((cg (fun t => ((q2 ◇ q2) ◇ q0) ◇ t) (p1m q0 q1 ((q1 ◇ q0) ◇ (q1 ◇ q0)) q1)).trans (p1m q0 (q2 ◇ q2) (((q2 ◇ q2) ◇ q0) ◇ ((q1 ◇ q1) ◇ q0)) (q1 ◇ q1))).trans (cg (fun t => t ◇ q0) (pp q1 q1 ((q1 ◇ q1) ◇ (q1 ◇ q1))))).trans (p1n (((q1 ◇ q1) ◇ q1) ◇ q0) q1 q0 (((q1 ◇ q1) ◇ q1) ◇ q0))).symm).trans ((((cg (fun t => t ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))) (p1m q0 q1 q0 q2)).symm).trans (pp (q2 ◇ q0) (q1 ◇ q0) q0)).trans ((cg (fun t => t ◇ (q1 ◇ q0)) (p1m q0 q1 ((q1 ◇ q0) ◇ (q1 ◇ q0)) q1)).trans (p1m q0 (q1 ◇ q1) (((q1 ◇ q1) ◇ q0) ◇ (q1 ◇ q0)) q1)))).symm
  exact ((pw x y z).trans (p1o z x x)).trans (((pw y (x ◇ x) z).trans (p1o z y x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_60607_to_61407 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_60607_to_61407
