-- Equation60607 → Equation61264
-- Recorded verdict: true
-- Premise: (x ◇ y) ◇ z = (z ◇ x) ◇ (x ◇ z)
-- Conclusion: (x ◇ y) ◇ y = (z ◇ (x ◇ w)) ◇ y
-- Original submission SHA-256: d8a72bc92f9b432f96a6762807be464f658b5b12db03c83f6c619a5cc03687da
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
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ y = (z ◇ (x ◇ w)) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have p0 : forall (x y z:G), ((x ◇ y) ◇ z) = ((x ◇ x) ◇ z):=by
    intro x y z
    exact (h x y z).trans ((h x x z).symm)
  have p1 : forall (q0 q1:G), ((q1 ◇ q0) ◇ (q0 ◇ q1)) = ((q0 ◇ q0) ◇ q1):=by
    intro q0 q1
    exact (((p0 q0 q0 q1).symm).trans (h q0 q0 q1)).symm
  have p2 : forall (q0 q2 q1:G), ((q1 ◇ q1) ◇ (q0 ◇ q1)) = ((q0 ◇ q0) ◇ q1):=by
    intro q0 q2 q1
    exact (((p0 q1 q0 (q0 ◇ q1)).symm).trans ((h q0 q2 q1).symm)).trans (p0 q0 q2 q1)
  have p3 : forall (q3 q4 q5 q6:G), (((q3 ◇ q3) ◇ q5) ◇ ((q5 ◇ q5) ◇ q3)) = (((q3 ◇ q3) ◇ q6) ◇ (q5 ◇ q3)):=by
    intro q3 q4 q5 q6
    exact ((((cg (fun t => t ◇ ((q3 ◇ q5) ◇ (q5 ◇ q3))) (p0 q3 q4 q5)).trans (cg (fun t => ((q3 ◇ q3) ◇ q5) ◇ t) (p0 q3 q5 (q5 ◇ q3)))).trans (cg (fun t => ((q3 ◇ q3) ◇ q5) ◇ t) (p2 q5 ((q3 ◇ q3) ◇ (q5 ◇ q3)) q3))).symm).trans ((((cg (fun t => t ◇ ((q3 ◇ q5) ◇ (q5 ◇ q3))) ((h q3 q4 q5).symm)).symm).trans ((h (q3 ◇ q5) q6 (q5 ◇ q3)).symm)).trans (cg (fun t => t ◇ (q5 ◇ q3)) (p0 q3 q5 q6)))
  have p4 : forall (q7 q8 q9 q10:G), (((q7 ◇ q7) ◇ q9) ◇ q10) = (((q7 ◇ q7) ◇ q7) ◇ q10):=by
    intro q7 q8 q9 q10
    exact (((cg (fun t => t ◇ q10) (p0 q7 q8 q9)).symm).trans (p0 (q7 ◇ q8) q9 q10)).trans (((cg (fun t => t ◇ q10) (p0 q7 q8 (q7 ◇ q8))).trans (p0 (q7 ◇ q7) (q7 ◇ q8) q10)).trans (cg (fun t => t ◇ q10) (p1 q7 q7)))
  have p5 : forall (q11 q12 q13:G), (((q12 ◇ q12) ◇ q12) ◇ q13) = (((q12 ◇ q11) ◇ q12) ◇ q13):=by
    intro q11 q12 q13
    exact (((cg (fun t => t ◇ q13) ((h q12 q11 q12).symm)).symm).trans (p4 q12 q11 (q12 ◇ q12) q13)).symm
  have p6 : forall (q3 q4 q5 q6:G), (((q5 ◇ q5) ◇ q3) ◇ ((q3 ◇ q3) ◇ q5)) = (((q5 ◇ q3) ◇ q6) ◇ (q3 ◇ q5)):=by
    intro q3 q4 q5 q6
    exact ((((cg (fun t => ((q3 ◇ q5) ◇ (q5 ◇ q3)) ◇ t) (p0 q3 q4 q5)).trans (cg (fun t => t ◇ ((q3 ◇ q3) ◇ q5)) (p0 q3 q5 (q5 ◇ q3)))).trans (cg (fun t => t ◇ ((q3 ◇ q3) ◇ q5)) (p2 q5 ((q3 ◇ q3) ◇ (q5 ◇ q3)) q3))).symm).trans (((cg (fun t => ((q3 ◇ q5) ◇ (q5 ◇ q3)) ◇ t) ((h q3 q4 q5).symm)).symm).trans ((h (q5 ◇ q3) q6 (q3 ◇ q5)).symm))
  have p7 : forall (q14 q15 q16:G), (((q15 ◇ q15) ◇ q15) ◇ q16) = (((q14 ◇ q14) ◇ q14) ◇ q16):=by
    intro q14 q15 q16
    exact (((p4 q14 (((q14 ◇ q14) ◇ q15) ◇ q16) q15 q16).symm).trans (((cg (fun t => t ◇ q16) (p2 q14 q14 q15)).symm).trans (p4 q15 q14 (q14 ◇ q15) q16))).symm
  have p8 : forall (q17 q18 q19 q20:G), (((q19 ◇ q18) ◇ q19) ◇ q20) = (((q17 ◇ q17) ◇ q17) ◇ q20):=by
    intro q17 q18 q19 q20
    exact (((p7 q17 q19 q20).symm).trans (p5 q18 q19 q20)).symm
  have p9 : forall (q21 q22 q23:G), (((q22 ◇ q21) ◇ (q22 ◇ q21)) ◇ q23) = (((q21 ◇ q21) ◇ q21) ◇ q23):=by
    intro q21 q22 q23
    exact (((p4 q21 (((q21 ◇ q21) ◇ q22) ◇ q23) q22 q23).symm).trans (((cg (fun t => t ◇ q23) (p1 q21 q22)).symm).trans (p0 (q22 ◇ q21) (q21 ◇ q22) q23))).symm
  have pa : forall (q3 q4 q24 q6:G), (((q3 ◇ q3) ◇ q3) ◇ (q24 ◇ (q3 ◇ q4))) = ((q24 ◇ q24) ◇ (q3 ◇ q4)):=by
    intro q3 q4 q24 q6
    exact (((cg (fun t => t ◇ (q24 ◇ (q3 ◇ q4))) (p1 q3 q24)).trans (p4 q3 (((q3 ◇ q3) ◇ q24) ◇ (q24 ◇ (q3 ◇ q4))) q24 (q24 ◇ (q3 ◇ q4)))).symm).trans ((((cg (fun t => t ◇ (q24 ◇ (q3 ◇ q4))) (h q3 q4 q24)).symm).trans ((h q24 q6 (q3 ◇ q4)).symm)).trans (p0 q24 q6 (q3 ◇ q4)))
  have pb : forall (q25 q26 q27:G), (((q25 ◇ q25) ◇ q25) ◇ ((q26 ◇ q26) ◇ q25)) = (((q25 ◇ q25) ◇ q25) ◇ (q26 ◇ q25)):=by
    intro q25 q26 q27
    exact ((((cg (fun t => ((q25 ◇ q25) ◇ q26) ◇ t) (p0 q25 q26 (q26 ◇ q25))).trans (cg (fun t => ((q25 ◇ q25) ◇ q26) ◇ t) (p2 q26 ((q25 ◇ q25) ◇ (q26 ◇ q25)) q25))).trans (p4 q25 (((q25 ◇ q25) ◇ q26) ◇ ((q26 ◇ q26) ◇ q25)) q26 ((q26 ◇ q26) ◇ q25))).symm).trans ((((cg (fun t => t ◇ ((q25 ◇ q26) ◇ (q26 ◇ q25))) (p1 q25 q26)).symm).trans ((h (q25 ◇ q26) q27 (q26 ◇ q25)).symm)).trans ((cg (fun t => t ◇ (q26 ◇ q25)) (p0 q25 q26 q27)).trans (p4 q25 (((q25 ◇ q25) ◇ q27) ◇ (q26 ◇ q25)) q27 (q26 ◇ q25))))
  have pc : forall (q28 q29 q30:G), ((((q28 ◇ q28) ◇ q28) ◇ (q28 ◇ q28)) ◇ q30) = (((q28 ◇ q28) ◇ q28) ◇ q30):=by
    intro q28 q29 q30
    exact ((cg (fun t => t ◇ q30) (p4 q28 (((q28 ◇ q28) ◇ q29) ◇ (q28 ◇ q28)) q29 (q28 ◇ q28))).symm).trans (((cg (fun t => t ◇ q30) (p6 q28 q28 q28 q29)).symm).trans (p9 q28 (q28 ◇ q28) q30))
  have pd : forall (q31 q32 q33 q34 q35:G), (((q35 ◇ q34) ◇ q35) ◇ (q32 ◇ (q33 ◇ q31))) = ((q32 ◇ q32) ◇ (q33 ◇ q31)):=by
    intro q31 q32 q33 q34 q35
    exact (((pa q33 q31 q32 q31).symm).trans ((p8 q33 q34 q35 (q32 ◇ (q33 ◇ q31))).symm)).symm
  have pe : forall (q36 q37 q38:G), (((q36 ◇ q36) ◇ q36) ◇ ((q36 ◇ q36) ◇ q37)) = (((q37 ◇ q37) ◇ q37) ◇ (q36 ◇ q37)):=by
    intro q36 q37 q38
    exact ((((cg (fun t => t ◇ ((q36 ◇ q36) ◇ q37)) (p0 q36 q37 (q37 ◇ q37))).trans (p0 (q36 ◇ q36) (q37 ◇ q37) ((q36 ◇ q36) ◇ q37))).trans (cg (fun t => t ◇ ((q36 ◇ q36) ◇ q37)) (p1 q36 q36))).symm).trans ((((cg (fun t => ((q36 ◇ q37) ◇ (q37 ◇ q37)) ◇ t) (p2 q36 q36 q37)).symm).trans ((h (q37 ◇ q37) q38 (q36 ◇ q37)).symm)).trans (p4 q37 (((q37 ◇ q37) ◇ q38) ◇ (q36 ◇ q37)) q38 (q36 ◇ q37)))
  have pf : forall (q39 q40 q41:G), (((q41 ◇ q41) ◇ q41) ◇ (q39 ◇ q41)) = (((q39 ◇ q39) ◇ q39) ◇ (q39 ◇ q41)):=by
    intro q39 q40 q41
    exact ((((((cg (fun t => ((q39 ◇ q41) ◇ (q39 ◇ q41)) ◇ t) (p0 q39 q40 q41)).trans (cg (fun t => t ◇ ((q39 ◇ q39) ◇ q41)) (p0 q39 q41 (q39 ◇ q41)))).trans (p0 (q39 ◇ q39) (q39 ◇ q41) ((q39 ◇ q39) ◇ q41))).trans (cg (fun t => t ◇ ((q39 ◇ q39) ◇ q41)) (p1 q39 q39))).trans (pe q39 q41 (((q39 ◇ q39) ◇ q39) ◇ ((q39 ◇ q39) ◇ q41)))).symm).trans ((((cg (fun t => ((q39 ◇ q41) ◇ (q39 ◇ q41)) ◇ t) ((h q39 q40 q41).symm)).symm).trans (p2 (q41 ◇ q39) q39 (q39 ◇ q41))).trans (p9 q39 q41 (q39 ◇ q41)))
  have pg : forall (q42 q43 q44 q45:G), ((((q43 ◇ q42) ◇ q43) ◇ (q44 ◇ q44)) ◇ q45) = (((q44 ◇ q44) ◇ q44) ◇ q45):=by
    intro q42 q43 q44 q45
    exact ((cg (fun t => t ◇ q45) ((p8 q44 q42 q43 (q44 ◇ q44)).symm)).symm).trans (pc q44 q42 q45)
  have ph : forall (q46 q47:G), (((q46 ◇ q46) ◇ q46) ◇ ((q46 ◇ q46) ◇ q47)) = (((q46 ◇ q46) ◇ q46) ◇ (q46 ◇ q47)):=by
    intro q46 q47
    exact ((((cg (fun t => t ◇ ((q46 ◇ q46) ◇ q47)) (p0 q46 q47 (q47 ◇ q47))).trans (p0 (q46 ◇ q46) (q47 ◇ q47) ((q46 ◇ q46) ◇ q47))).trans (cg (fun t => t ◇ ((q46 ◇ q46) ◇ q47)) (p1 q46 q46))).symm).trans ((((cg (fun t => ((q46 ◇ q47) ◇ (q47 ◇ q47)) ◇ t) (p2 q46 q46 q47)).symm).trans (p1 (q47 ◇ q47) (q46 ◇ q47))).trans ((cg (fun t => t ◇ (q46 ◇ q47)) (p1 q47 q47)).trans (pf q46 (((q47 ◇ q47) ◇ q47) ◇ (q46 ◇ q47)) q47)))
  have pi : forall (q48 q49 q50 q51:G), ((((q48 ◇ q48) ◇ q48) ◇ (q49 ◇ q48)) ◇ q51) = ((((q48 ◇ q48) ◇ q48) ◇ (q48 ◇ q49)) ◇ q51):=by
    intro q48 q49 q50 q51
    exact ((cg (fun t => t ◇ q51) (p4 q48 (((q48 ◇ q48) ◇ q50) ◇ (q49 ◇ q48)) q50 (q49 ◇ q48))).symm).trans ((((cg (fun t => t ◇ q51) (p3 q48 q48 q49 q50)).symm).trans (p0 ((q48 ◇ q48) ◇ q49) ((q49 ◇ q49) ◇ q48) q51)).trans ((cg (fun t => t ◇ q51) (p4 q48 (((q48 ◇ q48) ◇ q49) ◇ ((q48 ◇ q48) ◇ q49)) q49 ((q48 ◇ q48) ◇ q49))).trans (cg (fun t => t ◇ q51) (ph q48 q49))))
  have pj : forall (q48 q49 q50 q51:G), ((((q48 ◇ q48) ◇ q48) ◇ (q48 ◇ q50)) ◇ q51) = ((((q48 ◇ q48) ◇ q48) ◇ (q48 ◇ q49)) ◇ q51):=by
    intro q48 q49 q50 q51
    exact (((((cg (fun t => t ◇ q51) (p4 q48 (((q48 ◇ q48) ◇ q49) ◇ ((q49 ◇ q49) ◇ q48)) q49 ((q49 ◇ q49) ◇ q48))).trans (cg (fun t => t ◇ q51) (pb q48 q49 (((q48 ◇ q48) ◇ q48) ◇ ((q49 ◇ q49) ◇ q48))))).trans (pi q48 q49 ((((q48 ◇ q48) ◇ q48) ◇ (q49 ◇ q48)) ◇ q51) q51)).symm).trans ((((cg (fun t => t ◇ q51) ((p3 q48 q48 q49 q50).symm)).symm).trans (p0 ((q48 ◇ q48) ◇ q50) (q49 ◇ q48) q51)).trans ((cg (fun t => t ◇ q51) (p4 q48 (((q48 ◇ q48) ◇ q50) ◇ ((q48 ◇ q48) ◇ q50)) q50 ((q48 ◇ q48) ◇ q50))).trans (cg (fun t => t ◇ q51) (ph q48 q50))))).symm
  have pk : forall (q52 q53 q54:G), ((((q53 ◇ q53) ◇ q53) ◇ (q53 ◇ q52)) ◇ q54) = (((q53 ◇ q53) ◇ q53) ◇ q54):=by
    intro q52 q53 q54
    exact ((pj q53 q52 q53 q54).symm).trans (pg q53 q53 q53 q54)
  have pl : forall (q55 q56 q57 q58 q59:G), ((((q56 ◇ q55) ◇ q56) ◇ (q58 ◇ q57)) ◇ q59) = (((q58 ◇ q58) ◇ q58) ◇ q59):=by
    intro q55 q56 q57 q58 q59
    exact ((cg (fun t => t ◇ q59) ((p8 q58 q55 q56 (q58 ◇ q57)).symm)).symm).trans (pk q57 q58 q59)
  have pm : forall (q60 q61 q62 q63:G), (((q61 ◇ q61) ◇ q61) ◇ (q62 ◇ q61)) = (((q61 ◇ q61) ◇ q60) ◇ (q62 ◇ q61)):=by
    intro q60 q61 q62 q63
    exact ((((p3 q61 q60 q62 q60).symm).trans (p3 q61 q60 q62 q63)).trans (p4 q61 (((q61 ◇ q61) ◇ q63) ◇ (q62 ◇ q61)) q63 (q62 ◇ q61))).symm
  have pn : forall (q3 q4 q5 q6:G), (((q5 ◇ q3) ◇ q6) ◇ (q3 ◇ q5)) = (((q5 ◇ q3) ◇ q3) ◇ (q3 ◇ q5)):=by
    intro q3 q4 q5 q6
    exact ((p6 q3 q4 q5 q6).symm).trans (p6 q3 q4 q5 q3)
  have po : forall (q64 q65 q66 q67:G), ((q67 ◇ q67) ◇ (((q64 ◇ q64) ◇ q64) ◇ q67)) = (((q65 ◇ q65) ◇ q65) ◇ q67):=by
    intro q64 q65 q66 q67
    exact ((((cg (fun t => t ◇ q67) (p4 q64 (((q64 ◇ q64) ◇ q66) ◇ (q65 ◇ q64)) q66 (q65 ◇ q64))).trans (pl q64 q64 q64 q65 q67)).symm).trans ((((cg (fun t => t ◇ q67) (p3 q64 q64 q65 q66)).symm).trans (h ((q64 ◇ q64) ◇ q65) ((q65 ◇ q65) ◇ q64) q67)).trans ((cg (fun t => (q67 ◇ ((q64 ◇ q64) ◇ q65)) ◇ t) (p4 q64 (((q64 ◇ q64) ◇ q65) ◇ q67) q65 q67)).trans (p0 q67 ((q64 ◇ q64) ◇ q65) (((q64 ◇ q64) ◇ q64) ◇ q67))))).symm
  have pp : forall (q68 q69 q70:G), ((((q68 ◇ q68) ◇ q68) ◇ q69) ◇ q70) = (((q69 ◇ q69) ◇ q69) ◇ q70):=by
    intro q68 q69 q70
    exact ((cg (fun t => t ◇ q70) (po q68 q68 q68 q69)).symm).trans (p4 q69 q68 (((q68 ◇ q68) ◇ q68) ◇ q69) q70)
  have pq : forall (q71 q72 q73 q74:G), ((((q72 ◇ q71) ◇ q72) ◇ q73) ◇ q74) = (((q73 ◇ q73) ◇ q73) ◇ q74):=by
    intro q71 q72 q73 q74
    exact ((cg (fun t => t ◇ q74) (p5 q71 q72 q73)).symm).trans (pp q72 q73 q74)
  have pr : forall (q64 q65 q66 q75:G), (((q75 ◇ q75) ◇ q75) ◇ (q65 ◇ q64)) = (((q64 ◇ q64) ◇ q64) ◇ (q65 ◇ q64)):=by
    intro q64 q65 q66 q75
    exact ((((((((cg (fun t => ((q65 ◇ q64) ◇ ((q64 ◇ q64) ◇ q66)) ◇ t) (p4 q64 (((q64 ◇ q64) ◇ q65) ◇ ((q65 ◇ q65) ◇ q64)) q65 ((q65 ◇ q65) ◇ q64))).trans (cg (fun t => ((q65 ◇ q64) ◇ ((q64 ◇ q64) ◇ q66)) ◇ t) (pb q64 q65 (((q64 ◇ q64) ◇ q64) ◇ ((q65 ◇ q65) ◇ q64))))).trans (p0 (q65 ◇ q64) ((q64 ◇ q64) ◇ q66) (((q64 ◇ q64) ◇ q64) ◇ (q65 ◇ q64)))).trans (p2 ((q64 ◇ q64) ◇ q64) (((q65 ◇ q64) ◇ (q65 ◇ q64)) ◇ (((q64 ◇ q64) ◇ q64) ◇ (q65 ◇ q64))) (q65 ◇ q64))).trans (cg (fun t => t ◇ (q65 ◇ q64)) (pb q64 q64 (((q64 ◇ q64) ◇ q64) ◇ ((q64 ◇ q64) ◇ q64))))).trans (pl q64 q64 q64 q64 (q65 ◇ q64))).symm).trans ((((cg (fun t => ((q65 ◇ q64) ◇ ((q64 ◇ q64) ◇ q66)) ◇ t) ((p3 q64 q64 q65 q66).symm)).symm).trans ((h ((q64 ◇ q64) ◇ q66) q75 (q65 ◇ q64)).symm)).trans ((cg (fun t => t ◇ (q65 ◇ q64)) (p4 q64 (((q64 ◇ q64) ◇ q66) ◇ q75) q66 q75)).trans (pq q64 q64 q75 (q65 ◇ q64))))).symm
  have ps : forall (q76 q77 q78 q79:G), (((q77 ◇ q77) ◇ q77) ◇ (q77 ◇ q77)) = ((q78 ◇ q78) ◇ (q77 ◇ q77)):=by
    intro q76 q77 q78 q79
    exact (((((pq q76 q77 q78 ((q78 ◇ q78) ◇ (q77 ◇ q77))).trans (pd q77 (q78 ◇ q78) q77 q78 q78)).trans (cg (fun t => t ◇ (q77 ◇ q77)) (p1 q78 q78))).trans (pr q77 q77 (((q78 ◇ q78) ◇ q78) ◇ (q77 ◇ q77)) q78)).symm).trans ((((cg (fun t => t ◇ ((q78 ◇ q78) ◇ (q77 ◇ q77))) (cg (fun t => t ◇ q78) ((h q77 q76 q77).symm))).symm).trans (p3 (q77 ◇ q77) q76 q78 q79)).trans (((cg (fun t => t ◇ (q78 ◇ (q77 ◇ q77))) (cg (fun t => t ◇ q79) (p1 q77 q77))).trans (pq q77 q77 q79 (q78 ◇ (q77 ◇ q77)))).trans (pd q77 q78 q77 q79 q79)))
  have pt : forall (q80 q81:G), (((q80 ◇ q80) ◇ q80) ◇ (q80 ◇ q80)) = ((q80 ◇ q80) ◇ q80):=by
    intro q80 q81
    exact ((ps q80 q80 q80 q80).trans ((h q80 q81 q80).symm)).trans (p0 q80 q81 q80)
  have pu : forall (q76 q77 q78 q79 q80 q81:G), ((q78 ◇ q78) ◇ (q77 ◇ q77)) = ((q77 ◇ q77) ◇ q77):=by
    intro q76 q77 q78 q79 q80 q81
    exact (((pt q77 (((q77 ◇ q77) ◇ q77) ◇ (q77 ◇ q77))).symm).trans (ps q76 q77 q78 q79)).symm
  have pv : forall (q76 q78 q79:G), (((q78 ◇ q78) ◇ q78) ◇ ((q78 ◇ q76) ◇ q78)) = ((q78 ◇ q78) ◇ q78):=by
    intro q76 q78 q79
    exact (((cg (fun t => t ◇ ((q78 ◇ q76) ◇ q78)) (cg (fun t => t ◇ q78) (p1 q78 q78))).trans (pq q78 q78 q78 ((q78 ◇ q76) ◇ q78))).symm).trans ((((cg (fun t => (((q78 ◇ q78) ◇ (q78 ◇ q78)) ◇ q78) ◇ t) ((h q78 q76 q78).symm)).symm).trans (p3 (q78 ◇ q78) q76 q78 q79)).trans (((((cg (fun t => t ◇ (q78 ◇ (q78 ◇ q78))) (cg (fun t => t ◇ q79) (p1 q78 q78))).trans (pn q78 ((((q78 ◇ q78) ◇ q78) ◇ q79) ◇ (q78 ◇ (q78 ◇ q78))) (q78 ◇ q78) q79)).trans (pq q78 q78 q78 (q78 ◇ (q78 ◇ q78)))).trans (p1 q78 (q78 ◇ q78))).trans (p1 q78 q78)))
  have pw : forall (q82 q83 q84:G), (((q84 ◇ q84) ◇ q83) ◇ ((q84 ◇ q82) ◇ q84)) = ((q84 ◇ q84) ◇ q84):=by
    intro q82 q83 q84
    exact (((pv q82 q84 q82).symm).trans (pm q83 q84 (q84 ◇ q82) q82)).symm
  have px : forall (q85 q76 q78 q79:G), (((q85 ◇ q85) ◇ q85) ◇ (q85 ◇ q76)) = ((q78 ◇ q78) ◇ (q85 ◇ q76)):=by
    intro q85 q76 q78 q79
    exact ((((((((((cg (fun t => t ◇ ((q78 ◇ q78) ◇ (q85 ◇ q76))) (cg (fun t => t ◇ q78) (cg (fun t => t ◇ (q85 ◇ (q85 ◇ q76))) (p0 q85 q76 q85)))).trans (cg (fun t => t ◇ ((q78 ◇ q78) ◇ (q85 ◇ q76))) (cg (fun t => t ◇ q78) (pd q76 q85 q85 q85 q85)))).trans (cg (fun t => t ◇ ((q78 ◇ q78) ◇ (q85 ◇ q76))) (p0 (q85 ◇ q85) (q85 ◇ q76) q78))).trans (cg (fun t => t ◇ ((q78 ◇ q78) ◇ (q85 ◇ q76))) (cg (fun t => t ◇ q78) (p1 q85 q85)))).trans (pq q85 q85 q78 ((q78 ◇ q78) ◇ (q85 ◇ q76)))).trans (pd q76 (q78 ◇ q78) q85 q78 q78)).trans (cg (fun t => t ◇ (q85 ◇ q76)) (p1 q78 q78))).trans (pr q76 q85 (((q78 ◇ q78) ◇ q78) ◇ (q85 ◇ q76)) q78)).trans (pf q85 (((q76 ◇ q76) ◇ q76) ◇ (q85 ◇ q76)) q76)).symm).trans ((((cg (fun t => t ◇ ((q78 ◇ q78) ◇ (q85 ◇ q76))) (cg (fun t => t ◇ q78) (h q85 q76 (q85 ◇ q76)))).symm).trans (p3 (q85 ◇ q76) q85 q78 q79)).trans (((((cg (fun t => t ◇ (q78 ◇ (q85 ◇ q76))) (cg (fun t => t ◇ q79) (p0 q85 q76 (q85 ◇ q76)))).trans (cg (fun t => t ◇ (q78 ◇ (q85 ◇ q76))) (p0 (q85 ◇ q85) (q85 ◇ q76) q79))).trans (cg (fun t => t ◇ (q78 ◇ (q85 ◇ q76))) (cg (fun t => t ◇ q79) (p1 q85 q85)))).trans (pq q85 q85 q79 (q78 ◇ (q85 ◇ q76)))).trans (pd q76 q78 q85 q79 q79)))
  have py : forall (q86 q87 q88 q89:G), ((q89 ◇ q89) ◇ (q87 ◇ q88)) = ((q86 ◇ q86) ◇ (q87 ◇ q88)):=by
    intro q86 q87 q88 q89
    exact (((px q87 q88 q86 q86).symm).trans (px q87 q88 q89 q86)).symm
  have pz : forall (q90 q91 q92:G), ((q90 ◇ q90) ◇ (q91 ◇ q92)) = ((q91 ◇ q91) ◇ q92):=by
    intro q90 q91 q92
    exact ((py q90 q91 q92 q92).symm).trans (p2 q91 q90 q92)
  have p10 : forall (q93 q94 q95:G), ((q95 ◇ q93) ◇ (q95 ◇ q94)) = ((q95 ◇ q95) ◇ q94):=by
    intro q93 q94 q95
    exact ((h q95 q93 (q95 ◇ q94)).trans (pd q94 q95 q95 q94 q95)).trans (pz q95 q95 q94)
  have p11 : forall (q96:G), (((q96 ◇ q96) ◇ q96) ◇ q96) = ((q96 ◇ q96) ◇ q96):=by
    intro q96
    exact ((cg (fun t => t ◇ q96) (p1 q96 q96)).symm).trans (((p10 q96 q96 (q96 ◇ q96)).symm).trans (pw q96 q96 q96))
  have p12 : forall (q97 q98 q99:G), (((q98 ◇ q97) ◇ q98) ◇ q99) = ((q99 ◇ q99) ◇ q99):=by
    intro q97 q98 q99
    exact (((p11 q99).symm).trans ((p8 q99 q97 q98 q99).symm)).symm
  have p13 : forall (q100 q101 q102 q103 q104:G), (((q101 ◇ q100) ◇ q101) ◇ (q102 ◇ q103)) = ((q102 ◇ q102) ◇ q103):=by
    intro q100 q101 q102 q103 q104
    exact ((p8 q102 q100 q101 (q102 ◇ q103)).trans (px q102 q103 q104 q100)).trans (pz q104 q102 q103)
  have p14 : forall (q85 q76 q105:G), ((q76 ◇ q76) ◇ q76) = ((q85 ◇ q85) ◇ q76):=by
    intro q85 q76 q105
    exact (((((((cg (fun t => (q105 ◇ q105) ◇ t) (cg (fun t => t ◇ (q85 ◇ (q85 ◇ q76))) (p0 q85 q76 q85))).trans (cg (fun t => (q105 ◇ q105) ◇ t) (pd q76 q85 q85 q85 q85))).trans (cg (fun t => (q105 ◇ q105) ◇ t) (pz q85 q85 q76))).trans (pz q105 (q85 ◇ q85) q76)).trans (cg (fun t => t ◇ q76) (p1 q85 q85))).trans (p12 q85 q85 q76)).symm).trans ((((cg (fun t => (q105 ◇ q105) ◇ t) (h q85 q76 (q85 ◇ q76))).symm).trans (pu q85 (q85 ◇ q76) q105 q85 q85 q85)).trans ((((cg (fun t => t ◇ (q85 ◇ q76)) (p0 q85 q76 (q85 ◇ q76))).trans (cg (fun t => t ◇ (q85 ◇ q76)) (pz q85 q85 q76))).trans (p4 q85 (((q85 ◇ q85) ◇ q76) ◇ (q85 ◇ q76)) q76 (q85 ◇ q76))).trans (p13 q85 q85 q85 q76 (((q85 ◇ q85) ◇ q85) ◇ (q85 ◇ q76)))))
  exact (calc
    ((x ◇ y) ◇ y) = ((x ◇ x) ◇ y):=(h x y y).trans ((h x x y).symm)
    _ = ((z ◇ z) ◇ y):=(((p14 z y w).symm).trans (p14 x y w)).symm
    _ = ((z ◇ (x ◇ w)) ◇ y):=((h z (x ◇ w) y).trans ((h z z y).symm)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_60607_to_61264 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_60607_to_61264
