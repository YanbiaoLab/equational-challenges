-- Equation60641 → Equation60446
-- Recorded verdict: true
-- Premise: (x ◇ y) ◇ z = (z ◇ z) ◇ (x ◇ z)
-- Conclusion: (x ◇ y) ◇ y = (z ◇ w) ◇ (u ◇ y)
-- Original submission SHA-256: f2d877bf3956b9a391492842aeb38f4dd8a32154ff874b3648b92540f2edd8a5
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
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), (x ◇ y) ◇ y = (z ◇ w) ◇ (u ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have p0 : forall (x y z:G), ((x ◇ y) ◇ z) = ((x ◇ x) ◇ z):=by
    intro x y z
    exact (h x y z).trans ((h x x z).symm)
  have p1 : forall (q4 q5:G), ((q5 ◇ q5) ◇ (q4 ◇ q5)) = ((q4 ◇ q4) ◇ q5):=by
    intro q4 q5
    exact (((p0 q4 q4 q5).symm).trans (h q4 q4 q5)).symm
  have p2 : forall (q6 q7 q8 q9:G), (((q8 ◇ q8) ◇ q8) ◇ q9) = (((q6 ◇ q6) ◇ q8) ◇ q9):=by
    intro q6 q7 q8 q9
    exact (((cg (fun t => t ◇ q9) (p0 q6 q7 q8)).symm).trans ((((cg (fun t => t ◇ q9) ((h q6 q7 q8).symm)).symm).trans (h (q8 ◇ q8) (q6 ◇ q8) q9)).trans ((p1 (q8 ◇ q8) q9).trans (cg (fun t => t ◇ q9) (p1 q8 q8))))).symm
  have p3 : forall (q7 q8 q10 q11:G), (((q8 ◇ q7) ◇ q8) ◇ (q10 ◇ (q8 ◇ q8))) = ((q10 ◇ q10) ◇ (q8 ◇ q8)):=by
    intro q7 q8 q10 q11
    exact (((cg (fun t => t ◇ (q10 ◇ (q8 ◇ q8))) ((h q8 q7 q8).symm)).symm).trans ((h q10 q11 (q8 ◇ q8)).symm)).trans (p0 q10 q11 (q8 ◇ q8))
  have p4 : forall (q12 q13 q14 q15:G), (((q12 ◇ q12) ◇ q14) ◇ q15) = (((q12 ◇ q12) ◇ q12) ◇ q15):=by
    intro q12 q13 q14 q15
    exact (((cg (fun t => t ◇ q15) (p0 q12 q13 q14)).symm).trans (p0 (q12 ◇ q13) q14 q15)).trans (((cg (fun t => t ◇ q15) (p0 q12 q13 (q12 ◇ q13))).trans (p0 (q12 ◇ q12) (q12 ◇ q13) q15)).trans (cg (fun t => t ◇ q15) (p1 q12 q12)))
  have p5 : forall (q6 q7 q8 q9 q12 q13 q14 q15:G), (((q8 ◇ q8) ◇ q8) ◇ q9) = (((q6 ◇ q6) ◇ q6) ◇ q9):=by
    intro q6 q7 q8 q9 q12 q13 q14 q15
    exact (p2 q6 q7 q8 q9).trans (p4 q6 (((q6 ◇ q6) ◇ q8) ◇ q9) q8 q9)
  have p6 : forall (q16 q17 q18 q19:G), ((((q17 ◇ q16) ◇ q17) ◇ q18) ◇ q19) = (((q18 ◇ q18) ◇ q18) ◇ q19):=by
    intro q16 q17 q18 q19
    exact ((cg (fun t => t ◇ q19) (cg (fun t => t ◇ q18) ((h q17 q16 q17).symm))).symm).trans ((p2 (q17 ◇ q17) q16 q18 q19).symm)
  have p7 : forall (q6 q7 q11:G), (((q6 ◇ q6) ◇ q6) ◇ (q11 ◇ (q6 ◇ q11))) = ((q6 ◇ q6) ◇ q11):=by
    intro q6 q7 q11
    exact (((p0 q6 q7 q11).symm).trans (((h q6 q7 q11).trans (h q11 q11 (q6 ◇ q11))).trans (((cg (fun t => t ◇ (q11 ◇ (q6 ◇ q11))) (p0 q6 q11 (q6 ◇ q11))).trans (p0 (q6 ◇ q6) (q6 ◇ q11) (q11 ◇ (q6 ◇ q11)))).trans (cg (fun t => t ◇ (q11 ◇ (q6 ◇ q11))) (p1 q6 q6))))).symm
  have p8 : forall (q20 q21 q22:G), (((q21 ◇ q21) ◇ q21) ◇ (q20 ◇ (q22 ◇ q20))) = ((q22 ◇ q22) ◇ q20):=by
    intro q20 q21 q22
    exact (((p7 q22 q20 q20).symm).trans (p5 q21 q20 q22 (q20 ◇ (q22 ◇ q20)) q20 q20 q20 q20)).symm
  have p9 : forall (q23 q24 q4 q25:G), (((q23 ◇ q23) ◇ q23) ◇ (q4 ◇ (q23 ◇ q24))) = ((q4 ◇ q4) ◇ (q23 ◇ q24)):=by
    intro q23 q24 q4 q25
    exact (((p0 (q23 ◇ q23) (q23 ◇ q24) (q4 ◇ (q23 ◇ q24))).trans (cg (fun t => t ◇ (q4 ◇ (q23 ◇ q24))) (p1 q23 q23))).symm).trans ((((cg (fun t => t ◇ (q4 ◇ (q23 ◇ q24))) (p0 q23 q24 (q23 ◇ q24))).symm).trans ((h q4 q25 (q23 ◇ q24)).symm)).trans (p0 q4 q25 (q23 ◇ q24)))
  have pa : forall (q26 q27 q28:G), ((q28 ◇ q28) ◇ (((q26 ◇ q26) ◇ q26) ◇ q28)) = (((q26 ◇ q26) ◇ q26) ◇ q28):=by
    intro q26 q27 q28
    exact (((p4 q26 (((q26 ◇ q26) ◇ q27) ◇ q28) q27 q28).symm).trans (((cg (fun t => t ◇ q28) (p7 q26 q26 q27)).symm).trans (h ((q26 ◇ q26) ◇ q26) (q27 ◇ (q26 ◇ q27)) q28))).symm
  have pb : forall (q29 q30 q31 q32:G), (((q31 ◇ q31) ◇ q31) ◇ (q30 ◇ (q32 ◇ q29))) = ((q30 ◇ q30) ◇ (q32 ◇ q29)):=by
    intro q29 q30 q31 q32
    exact (((p9 q32 q29 q30 q29).symm).trans (p5 q31 q29 q32 (q30 ◇ (q32 ◇ q29)) q29 q29 q29 q29)).symm
  have pc : forall (q33 q34 q35 q36:G), (((q35 ◇ q35) ◇ q33) ◇ q36) = (((q34 ◇ q34) ◇ q34) ◇ q36):=by
    intro q33 q34 q35 q36
    exact (((cg (fun t => t ◇ q36) (p8 q33 q34 q35)).symm).trans (h ((q34 ◇ q34) ◇ q34) (q33 ◇ (q35 ◇ q33)) q36)).trans (pa q34 ((q36 ◇ q36) ◇ (((q34 ◇ q34) ◇ q34) ◇ q36)) q36)
  have pd : forall (q37 q38 q39 q40 q41:G), (((q38 ◇ q38) ◇ q37) ◇ (q40 ◇ (q41 ◇ q39))) = ((q40 ◇ q40) ◇ (q41 ◇ q39)):=by
    intro q37 q38 q39 q40 q41
    exact (pc q37 q37 q38 (q40 ◇ (q41 ◇ q39))).trans (pb q39 q40 q37 q41)
  have pe : forall (q42 q43 q44 q45:G), (((q44 ◇ q44) ◇ q44) ◇ (q43 ◇ q43)) = ((q44 ◇ q44) ◇ (q43 ◇ q43)):=by
    intro q42 q43 q44 q45
    exact ((((((cg (fun t => t ◇ ((q44 ◇ q44) ◇ (q43 ◇ q43))) (p0 q44 (q43 ◇ q43) (q44 ◇ (q43 ◇ q43)))).trans (p0 (q44 ◇ q44) (q44 ◇ (q43 ◇ q43)) ((q44 ◇ q44) ◇ (q43 ◇ q43)))).trans (cg (fun t => t ◇ ((q44 ◇ q44) ◇ (q43 ◇ q43))) (p1 q44 q44))).trans (pd q44 q44 q43 (q44 ◇ q44) q43)).trans (cg (fun t => t ◇ (q43 ◇ q43)) (p1 q44 q44))).symm).trans ((((cg (fun t => ((q44 ◇ (q43 ◇ q43)) ◇ (q44 ◇ (q43 ◇ q43))) ◇ t) (p3 q42 q43 q44 q42)).symm).trans ((h ((q43 ◇ q42) ◇ q43) q45 (q44 ◇ (q43 ◇ q43))).symm)).trans ((p6 q42 q43 q45 (q44 ◇ (q43 ◇ q43))).trans (pd q45 q45 q43 q44 q43)))
  have pf : forall (q46 q47 q48:G), ((q48 ◇ q48) ◇ (q46 ◇ q46)) = ((q47 ◇ q47) ◇ (q46 ◇ q46)):=by
    intro q46 q47 q48
    exact (((pe q46 q46 q48 q46).symm).trans (p5 q47 q46 q48 (q46 ◇ q46) q46 q46 q46 q46)).trans (pe (((q47 ◇ q47) ◇ q47) ◇ (q46 ◇ q46)) q46 q47 (((q47 ◇ q47) ◇ q47) ◇ (q46 ◇ q46)))
  have pg : forall (q49 q50 q51:G), ((q49 ◇ q49) ◇ (q51 ◇ q51)) = ((q51 ◇ q50) ◇ q51):=by
    intro q49 q50 q51
    exact ((pf q51 q49 q51).symm).trans ((h q51 q50 q51).symm)
  have ph : forall (q49 q50 q51:G), ((q51 ◇ q50) ◇ q51) = ((q51 ◇ q49) ◇ q51):=by
    intro q49 q50 q51
    exact ((pg q49 q50 q51).symm).trans (pg q49 q49 q51)
  have pi : forall (q52 q53:G), ((q53 ◇ q53) ◇ q53) = ((q53 ◇ q52) ◇ q53):=by
    intro q52 q53
    exact (((pg q53 q52 q53).symm).trans (p1 q53 q53)).symm
  have pj : forall (q54 q55:G), ((q54 ◇ q54) ◇ (q55 ◇ q55)) = ((q55 ◇ q55) ◇ q55):=by
    intro q54 q55
    exact ((pf q55 q54 q55).symm).trans (p1 q55 q55)
  have pk : forall (q56 q57 q58:G), (((q58 ◇ q58) ◇ q56) ◇ (q58 ◇ q58)) = ((q58 ◇ q57) ◇ q58):=by
    intro q56 q57 q58
    exact ((ph q56 (q58 ◇ q58) (q58 ◇ q58)).symm).trans (pg (q58 ◇ q58) q57 q58)
  have pl : forall (q59 q60 q61:G), ((q61 ◇ q59) ◇ (q60 ◇ q60)) = ((q60 ◇ q60) ◇ q60):=by
    intro q59 q60 q61
    exact ((h q61 q59 (q60 ◇ q60)).trans (pd (q60 ◇ q60) q60 q60 q61 q60)).trans (pj q61 q60)
  have pm : forall (q62 q63 q64:G), (((q64 ◇ q64) ◇ q64) ◇ q64) = (((q64 ◇ q62) ◇ q63) ◇ q64):=by
    intro q62 q63 q64
    exact (((p1 (q64 ◇ q64) q64).trans (cg (fun t => t ◇ q64) (p1 q64 q64))).symm).trans (((cg (fun t => (q64 ◇ q64) ◇ t) ((pi q62 q64).symm)).symm).trans ((h (q64 ◇ q62) q63 q64).symm))
  have pn : forall (q65 q66 q67 q68 q69:G), (((q69 ◇ q65) ◇ q66) ◇ q69) = (((q68 ◇ q68) ◇ q67) ◇ q69):=by
    intro q65 q66 q67 q68 q69
    exact ((pm q65 q66 q69).symm).trans ((pc q67 q69 q68 q69).symm)
  have po : forall (q70 q71:G), (((q71 ◇ q71) ◇ q71) ◇ ((q70 ◇ q70) ◇ q70)) = ((q70 ◇ q70) ◇ q70):=by
    intro q70 q71
    exact ((((pj (q70 ◇ q70) q70).symm).trans ((pk q71 (q70 ◇ q70) (q70 ◇ q70)).symm)).trans (((cg (fun t => t ◇ ((q70 ◇ q70) ◇ (q70 ◇ q70))) (cg (fun t => t ◇ q71) (p1 q70 q70))).trans (cg (fun t => (((q70 ◇ q70) ◇ q70) ◇ q71) ◇ t) (p1 q70 q70))).trans (p6 q70 q70 q71 ((q70 ◇ q70) ◇ q70)))).symm
  have pp : forall (x y z:G), ((x ◇ y) ◇ z) = ((x ◇ x) ◇ z):=by
    intro x y z
    exact (h x y z).trans ((h x x z).symm)
  have pq : forall (x y z:G), ((z ◇ z) ◇ (x ◇ z)) = ((x ◇ x) ◇ z):=by
    intro x y z
    exact (((pp x x z).symm).trans (h x x z)).symm
  have pr : forall (q0 q1 q2 q3:G), ((q3 ◇ q2) ◇ ((q1 ◇ q0) ◇ q1)) = ((q1 ◇ q1) ◇ q1):=by
    intro q0 q1 q2 q3
    exact (((cg (fun t => (q3 ◇ q2) ◇ t) ((h q1 q0 q1).symm)).symm).trans (pl q2 (q1 ◇ q1) q3)).trans ((cg (fun t => t ◇ (q1 ◇ q1)) (pl q1 q1 q1)).trans (pl q1 q1 (q1 ◇ q1)))
  have ps : forall (q0 q1 q2:G), (((q2 ◇ q0) ◇ q1) ◇ q2) = ((q2 ◇ q2) ◇ q2):=by
    intro q0 q1 q2
    exact (((pr q0 q2 q2 q2).symm).trans ((h (q2 ◇ q0) q1 q2).symm)).symm
  have pt : forall (q65 q66 q67 q68 q69 q0 q1 q2:G), (((q68 ◇ q68) ◇ q67) ◇ q69) = ((q69 ◇ q69) ◇ q69):=by
    intro q65 q66 q67 q68 q69 q0 q1 q2
    exact (((ps q65 q66 q69).symm).trans (pn q65 q66 q67 q68 q69)).symm
  have pu : forall (q0 q2 q1:G), (((q0 ◇ q0) ◇ q0) ◇ (q2 ◇ (q0 ◇ q2))) = ((q0 ◇ q0) ◇ q2):=by
    intro q0 q2 q1
    exact (((pp q0 q1 q2).symm).trans (((h q0 q1 q2).trans (h q2 q2 (q0 ◇ q2))).trans (((cg (fun t => t ◇ (q2 ◇ (q0 ◇ q2))) (pp q0 q2 (q0 ◇ q2))).trans (pp (q0 ◇ q0) (q0 ◇ q2) (q2 ◇ (q0 ◇ q2)))).trans (cg (fun t => t ◇ (q2 ◇ (q0 ◇ q2))) (pl q0 q0 q0))))).symm
  have pv : forall (q0 q1:G), ((q1 ◇ q1) ◇ q1) = ((q0 ◇ q0) ◇ q1):=by
    intro q0 q1
    exact ((((((((cg (fun t => t ◇ ((q1 ◇ (q0 ◇ q1)) ◇ ((q0 ◇ q0) ◇ q1))) (cg (fun t => t ◇ ((q0 ◇ q0) ◇ q0)) (po q0 q0))).trans (cg (fun t => t ◇ ((q1 ◇ (q0 ◇ q1)) ◇ ((q0 ◇ q0) ◇ q1))) (po q0 q0))).trans (cg (fun t => ((q0 ◇ q0) ◇ q0) ◇ t) (pp q1 (q0 ◇ q1) ((q0 ◇ q0) ◇ q1)))).trans (cg (fun t => ((q0 ◇ q0) ◇ q0) ◇ t) (pq (q0 ◇ q0) ((q1 ◇ q1) ◇ ((q0 ◇ q0) ◇ q1)) q1))).trans (cg (fun t => ((q0 ◇ q0) ◇ q0) ◇ t) (cg (fun t => t ◇ q1) (pl q0 q0 q0)))).trans (cg (fun t => ((q0 ◇ q0) ◇ q0) ◇ t) (pt (((q0 ◇ q0) ◇ q0) ◇ q1) (((q0 ◇ q0) ◇ q0) ◇ q1) q0 q0 q1 (((q0 ◇ q0) ◇ q0) ◇ q1) (((q0 ◇ q0) ◇ q0) ◇ q1) (((q0 ◇ q0) ◇ q0) ◇ q1)))).trans (po q1 q0)).symm).trans ((((cg (fun t => ((((q0 ◇ q0) ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ ((q0 ◇ q0) ◇ q0)) ◇ t) (cg (fun t => (q1 ◇ (q0 ◇ q1)) ◇ t) (pu q0 q1 q0))).symm).trans (pu ((q0 ◇ q0) ◇ q0) (q1 ◇ (q0 ◇ q1)) q0)).trans ((cg (fun t => t ◇ (q1 ◇ (q0 ◇ q1))) (po q0 q0)).trans (pu q0 q1 (((q0 ◇ q0) ◇ q0) ◇ (q1 ◇ (q0 ◇ q1))))))
  have pw : forall (q0 q1 q2:G), ((q1 ◇ q1) ◇ q2) = ((q0 ◇ q0) ◇ q2):=by
    intro q0 q1 q2
    exact (((pv q0 q2).symm).trans (pv q1 q2)).symm
  have px : forall (q0 q1 q3 q2:G), ((q0 ◇ q0) ◇ (q1 ◇ q3)) = ((q1 ◇ q1) ◇ q3):=by
    intro q0 q1 q3 q2
    exact (((pw q0 q3 (q1 ◇ q3)).symm).trans ((h q1 q2 q3).symm)).trans (pp q1 q2 q3)
  exact (pp x y y).trans ((((pp z w (u ◇ y)).trans (px z u y u)).trans (pw x u y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_60641_to_60446 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_60641_to_60446
