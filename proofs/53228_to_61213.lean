-- Equation53228 → Equation61213
-- Recorded verdict: true
-- Premise: x ◇ y = (((x ◇ z) ◇ y) ◇ y) ◇ x
-- Conclusion: (x ◇ y) ◇ y = (x ◇ (z ◇ w)) ◇ u
-- Original submission SHA-256: c025ee649b576db4e3b1a8afc592c7eed830dee629268cefd6f603a71f50739d
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (((x ◇ z) ◇ y) ◇ y) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), (x ◇ y) ◇ y = (x ◇ (z ◇ w)) ◇ u
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have cg : ∀ (f : G → G) {a b : G}, a = b → f a = f b := by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1 : G), ((q1 ◇ q1) ◇ (q1 ◇ q0)) = ((q1 ◇ q0) ◇ q1) := by
    intro q0 q1
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (q1 ◇ q0)) ((h q1 q1 q0).symm)).symm).trans ((h (q1 ◇ q0) q1 q1).symm)).trans (rfl))
  have apc1 : forall (q2 q3 : G), ((((q3 ◇ q2) ◇ q3) ◇ (q3 ◇ q2)) ◇ q3) = (q3 ◇ (q3 ◇ q2)) := by
    intro q2 q3
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q3) (cg (fun t => t ◇ (q3 ◇ q2)) (apc0 q2 q3))).symm).trans ((h q3 (q3 ◇ q2) q3).symm)).trans (rfl))
  have apc2 : forall (q4 q5 : G), (((q4 ◇ q4) ◇ q4) ◇ ((q4 ◇ q4) ◇ q5)) = (((q4 ◇ q4) ◇ q5) ◇ (q4 ◇ q4)) := by
    intro q4 q5
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ ((q4 ◇ q4) ◇ q5)) (apc0 q4 q4)).symm).trans (apc0 q5 (q4 ◇ q4))).trans (rfl))
  have apc3 : forall (x y z : G), ((((x ◇ z) ◇ y) ◇ y) ◇ x) = ((((x ◇ x) ◇ y) ◇ y) ◇ x) := by
    intro x y z
    exact ((rfl).symm).trans (((h x y z).symm.trans (h x y x)).trans (rfl))
  have apc4 : forall (q6 q7 : G), ((((q6 ◇ q6) ◇ q7) ◇ q7) ◇ q6) = (q6 ◇ q7) := by
    intro q6 q7
    exact ((rfl).symm).trans ((((apc3 q6 q7 q6).symm).trans ((h q6 q7 q6).symm)).trans (rfl))
  have apc5 : forall (q0 q1 q8 : G), (((q1 ◇ q8) ◇ q1) ◇ ((q1 ◇ q0) ◇ q8)) = (((q1 ◇ q0) ◇ q8) ◇ q1) := by
    intro q0 q1 q8
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ ((q1 ◇ q0) ◇ q8)) (cg (fun t => t ◇ q1) ((h q1 q8 q0).symm))).symm).trans ((h ((q1 ◇ q0) ◇ q8) q1 q8).symm)).trans (rfl))
  have apc6 : forall (q9 : G), (((q9 ◇ q9) ◇ q9) ◇ (q9 ◇ q9)) = (((q9 ◇ q9) ◇ q9) ◇ q9) := by
    intro q9
    exact (((rfl).symm).trans ((((apc5 q9 q9 q9).symm).trans (apc2 q9 q9)).trans (rfl))).symm
  have apc7 : forall (q10 : G), (q10 ◇ (q10 ◇ q10)) = (q10 ◇ q10) := by
    intro q10
    exact (((apc4 q10 q10).symm).trans ((((cg (fun t => t ◇ q10) (apc6 q10)).symm).trans (apc1 q10 q10)).trans (rfl))).symm
  have apc9 : forall (q11 q12 : G), ((((q11 ◇ q12) ◇ (q11 ◇ q12)) ◇ (q11 ◇ q12)) ◇ q11) = (q11 ◇ ((q11 ◇ q12) ◇ (q11 ◇ q12))) := by
    intro q11 q12
    exact ((cg (fun t => t ◇ q11) (apc0 (q11 ◇ q12) (q11 ◇ q12))).symm).trans ((((cg (fun t => t ◇ q11) (cg (fun t => t ◇ ((q11 ◇ q12) ◇ (q11 ◇ q12))) (apc7 (q11 ◇ q12)))).symm).trans ((h q11 ((q11 ◇ q12) ◇ (q11 ◇ q12)) q12).symm)).trans (rfl))
  have apc10 : forall (q13 q14 : G), (q13 ◇ ((q13 ◇ q14) ◇ (q13 ◇ q14))) = (q13 ◇ (q13 ◇ q14)) := by
    intro q13 q14
    exact ((rfl).symm).trans ((((apc9 q13 q14).symm).trans ((h q13 (q13 ◇ q14) q14).symm)).trans (rfl))
  have apc24 : forall (q15 q0 q1 q8 : G), ((((q8 ◇ q15) ◇ q1) ◇ q1) ◇ (((q8 ◇ q0) ◇ q15) ◇ q15)) = ((((q8 ◇ q0) ◇ q15) ◇ q15) ◇ q1) := by
    intro q15 q0 q1 q8
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (((q8 ◇ q0) ◇ q15) ◇ q15)) (cg (fun t => t ◇ q1) (cg (fun t => t ◇ q1) ((h q8 q15 q0).symm)))).symm).trans ((h (((q8 ◇ q0) ◇ q15) ◇ q15) q1 q8).symm)).trans (rfl))
  have apc30 : forall (q2 q16 q17 : G), (((((q16 ◇ q2) ◇ q16) ◇ q17) ◇ q17) ◇ (q16 ◇ q16)) = ((q16 ◇ q16) ◇ q17) := by
    intro q2 q16 q17
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (q16 ◇ q16)) (cg (fun t => t ◇ q17) (cg (fun t => t ◇ q17) (apc0 q2 q16)))).symm).trans ((h (q16 ◇ q16) q17 (q16 ◇ q2)).symm)).trans (rfl))
  have apc33 : forall (q18 q19 : G), (((q18 ◇ q19) ◇ q19) ◇ ((((q18 ◇ q19) ◇ q19) ◇ q19) ◇ q19)) = (((q18 ◇ q19) ◇ q19) ◇ (((q18 ◇ q19) ◇ q19) ◇ q19)) := by
    intro q18 q19
    exact ((rfl).symm).trans ((((cg (fun t => ((q18 ◇ q19) ◇ q19) ◇ t) (apc24 q19 q19 q19 q18)).symm).trans (apc10 ((q18 ◇ q19) ◇ q19) q19)).trans (rfl))
  have apc34 : forall (q20 q21 q22 : G), (((((q22 ◇ q21) ◇ q20) ◇ q20) ◇ (((q22 ◇ q21) ◇ q20) ◇ q20)) ◇ (q22 ◇ q20)) = (((((q22 ◇ q21) ◇ q20) ◇ q20) ◇ q22) ◇ (((q22 ◇ q21) ◇ q20) ◇ q20)) := by
    intro q20 q21 q22
    exact ((rfl).symm).trans ((((cg (fun t => ((((q22 ◇ q21) ◇ q20) ◇ q20) ◇ (((q22 ◇ q21) ◇ q20) ◇ q20)) ◇ t) ((h q22 q20 q21).symm)).symm).trans (apc0 q22 (((q22 ◇ q21) ◇ q20) ◇ q20))).trans (rfl))
  have apc35 : forall (q23 q24 : G), (((((q24 ◇ q23) ◇ q23) ◇ q23) ◇ q24) ◇ (((q24 ◇ q23) ◇ q23) ◇ q23)) = (((((q24 ◇ q23) ◇ q23) ◇ q23) ◇ q23) ◇ (q24 ◇ q23)) := by
    intro q23 q24
    exact (((rfl).symm).trans ((((cg (fun t => t ◇ (q24 ◇ q23)) (apc24 q23 q23 q23 q24)).symm).trans (apc34 q23 q23 q24)).trans (rfl))).symm
  have apc36 : forall (q25 q26 : G), (((((q26 ◇ q25) ◇ q25) ◇ q25) ◇ q25) ◇ (q26 ◇ q25)) = ((q26 ◇ q25) ◇ (((q26 ◇ q25) ◇ q25) ◇ q25)) := by
    intro q25 q26
    exact (((rfl).symm).trans ((((cg (fun t => t ◇ (((q26 ◇ q25) ◇ q25) ◇ q25)) ((h q26 q25 q25).symm)).symm).trans (apc35 q25 q26)).trans (rfl))).symm
  have apc37 : forall (q27 q28 : G), ((q27 ◇ q28) ◇ (((q27 ◇ q28) ◇ q28) ◇ q28)) = ((q27 ◇ q28) ◇ q28) := by
    intro q27 q28
    exact ((rfl).symm).trans ((((apc36 q28 q27).symm).trans ((h (q27 ◇ q28) q28 q28).symm)).trans (rfl))
  have apc38 : forall (q18 q19 : G), (((q18 ◇ q19) ◇ q19) ◇ (((q18 ◇ q19) ◇ q19) ◇ q19)) = (((q18 ◇ q19) ◇ q19) ◇ q19) := by
    intro q18 q19
    exact (((rfl).symm).trans ((((apc37 (q18 ◇ q19) q19).symm).trans ((apc33 q18 q19).trans (rfl))).trans (rfl))).symm
  have apc39 : forall (q29 q30 q31 : G), (((((q29 ◇ q30) ◇ q30) ◇ q31) ◇ q31) ◇ (q29 ◇ q30)) = ((q29 ◇ q30) ◇ q31) := by
    intro q29 q30 q31
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (q29 ◇ q30)) (cg (fun t => t ◇ q31) (cg (fun t => t ◇ q31) (apc37 q29 q30)))).symm).trans ((h (q29 ◇ q30) q31 (((q29 ◇ q30) ◇ q30) ◇ q30)).symm)).trans (rfl))
  have apc41 : forall (q32 q33 : G), (q32 ◇ (((q32 ◇ q33) ◇ q33) ◇ q33)) = ((((q32 ◇ q33) ◇ q33) ◇ q33) ◇ q32) := by
    intro q32 q33
    exact (((cg (fun t => t ◇ q32) (apc38 q32 q33)).symm).trans ((((cg (fun t => t ◇ q32) (cg (fun t => t ◇ (((q32 ◇ q33) ◇ q33) ◇ q33)) (apc37 q32 q33))).symm).trans ((h q32 (((q32 ◇ q33) ◇ q33) ◇ q33) q33).symm)).trans (rfl))).symm
  have apc42 : forall (q34 q35 : G), (((((q35 ◇ q34) ◇ q35) ◇ q35) ◇ q35) ◇ (q35 ◇ q34)) = ((q35 ◇ q34) ◇ (q35 ◇ q35)) := by
    intro q34 q35
    exact (((rfl).symm).trans ((((cg (fun t => (q35 ◇ q34) ◇ t) ((h q35 q35 q34).symm)).symm).trans (apc41 (q35 ◇ q34) q35)).trans (rfl))).symm
  have apc43 : forall (q36 q37 : G), ((q37 ◇ q36) ◇ (q37 ◇ q37)) = ((q37 ◇ q36) ◇ q37) := by
    intro q36 q37
    exact ((rfl).symm).trans ((((apc42 q36 q37).symm).trans ((h (q37 ◇ q36) q37 q37).symm)).trans (rfl))
  have apc54 : forall (q38 q39 q40 : G), (((((q40 ◇ q38) ◇ q39) ◇ q40) ◇ ((q40 ◇ q38) ◇ q39)) ◇ (q40 ◇ q39)) = ((q40 ◇ q39) ◇ ((q40 ◇ q38) ◇ q39)) := by
    intro q38 q39 q40
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (q40 ◇ q39)) (cg (fun t => t ◇ ((q40 ◇ q38) ◇ q39)) (apc5 q38 q40 q39))).symm).trans ((h (q40 ◇ q39) ((q40 ◇ q38) ◇ q39) q40).symm)).trans (rfl))
  have apc55 : forall (q41 q42 q43 : G), (((((q43 ◇ q41) ◇ q42) ◇ q43) ◇ ((q43 ◇ q41) ◇ q42)) ◇ (q43 ◇ q43)) = ((q43 ◇ q43) ◇ ((q43 ◇ q41) ◇ q42)) := by
    intro q41 q42 q43
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (q43 ◇ q43)) (cg (fun t => t ◇ ((q43 ◇ q41) ◇ q42)) (apc5 q41 q43 q42))).symm).trans (apc30 q42 q43 ((q43 ◇ q41) ◇ q42))).trans (rfl))
  have apc62 : forall (q44 q45 q46 : G), (((((q46 ◇ q44) ◇ q45) ◇ q45) ◇ q46) ◇ ((q46 ◇ q44) ◇ q45)) = ((q46 ◇ q45) ◇ ((q46 ◇ q44) ◇ q45)) := by
    intro q44 q45 q46
    exact (((apc54 q44 q45 q46).symm).trans ((((cg (fun t => ((((q46 ◇ q44) ◇ q45) ◇ q46) ◇ ((q46 ◇ q44) ◇ q45)) ◇ t) ((h q46 q45 q44).symm)).symm).trans (apc5 q45 ((q46 ◇ q44) ◇ q45) q46)).trans (rfl))).symm
  have apc85 : forall (q47 q48 q49 : G), (((((((q48 ◇ q47) ◇ q47) ◇ q47) ◇ q48) ◇ q49) ◇ q49) ◇ q48) = (q48 ◇ q49) := by
    intro q47 q48 q49
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q48) (cg (fun t => t ◇ q49) (cg (fun t => t ◇ q49) (apc41 q48 q47)))).symm).trans ((h q48 q49 (((q48 ◇ q47) ◇ q47) ◇ q47)).symm)).trans (rfl))
  have apc86 : forall (q50 q51 : G), ((((q51 ◇ q50) ◇ ((q51 ◇ q50) ◇ q50)) ◇ ((q51 ◇ q50) ◇ q50)) ◇ q51) = (q51 ◇ ((q51 ◇ q50) ◇ q50)) := by
    intro q50 q51
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q51) (cg (fun t => t ◇ ((q51 ◇ q50) ◇ q50)) (apc62 q50 q50 q51))).symm).trans (apc85 q50 q51 ((q51 ◇ q50) ◇ q50))).trans (rfl))
  have apc101 : forall (q52 q53 q54 : G), (((((q53 ◇ q52) ◇ q52) ◇ q52) ◇ q54) ◇ ((((q53 ◇ q52) ◇ q52) ◇ q52) ◇ q52)) = (((((q53 ◇ q52) ◇ q52) ◇ q52) ◇ q54) ◇ (((q53 ◇ q52) ◇ q52) ◇ q52)) := by
    intro q52 q53 q54
    exact ((rfl).symm).trans ((((cg (fun t => ((((q53 ◇ q52) ◇ q52) ◇ q52) ◇ q54) ◇ t) (apc24 q52 q52 q52 q53)).symm).trans (apc43 q54 (((q53 ◇ q52) ◇ q52) ◇ q52))).trans (rfl))
  have apc103 : forall (q55 q56 : G), (((((q55 ◇ q56) ◇ q56) ◇ q56) ◇ ((q55 ◇ q56) ◇ q56)) ◇ (((q55 ◇ q56) ◇ q56) ◇ q56)) = (((((q55 ◇ q56) ◇ q56) ◇ q56) ◇ q56) ◇ ((q55 ◇ q56) ◇ q56)) := by
    intro q55 q56
    exact ((rfl).symm).trans ((((apc101 q56 q55 ((q55 ◇ q56) ◇ q56)).symm).trans (apc5 q56 ((q55 ◇ q56) ◇ q56) q56)).trans (rfl))
  have apc113 : forall (q57 q58 : G), ((((((q57 ◇ q58) ◇ q58) ◇ q58) ◇ q58) ◇ ((q57 ◇ q58) ◇ q58)) ◇ ((q57 ◇ q58) ◇ q58)) = (((q57 ◇ q58) ◇ q58) ◇ q58) := by
    intro q57 q58
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ ((q57 ◇ q58) ◇ q58)) (apc103 q57 q58)).symm).trans (apc1 q58 ((q57 ◇ q58) ◇ q58))).trans (apc38 q57 q58))
  have apc114 : forall (q59 q60 : G), ((((q59 ◇ q60) ◇ q60) ◇ q60) ◇ ((q59 ◇ q60) ◇ q60)) = ((((q59 ◇ q60) ◇ q60) ◇ q60) ◇ q60) := by
    intro q59 q60
    exact (((apc24 q60 q60 q60 q59).symm).trans ((((cg (fun t => t ◇ (((q59 ◇ q60) ◇ q60) ◇ q60)) (apc113 q59 q60)).symm).trans ((h (((q59 ◇ q60) ◇ q60) ◇ q60) ((q59 ◇ q60) ◇ q60) q60).symm)).trans (rfl))).symm
  have apc115 : forall (q55 q56 : G), (((((q55 ◇ q56) ◇ q56) ◇ q56) ◇ q56) ◇ ((q55 ◇ q56) ◇ q56)) = (((((q55 ◇ q56) ◇ q56) ◇ q56) ◇ q56) ◇ q56) := by
    intro q55 q56
    exact (((rfl).symm).trans (((((cg (fun t => t ◇ (((q55 ◇ q56) ◇ q56) ◇ q56)) (apc114 q55 q56)).trans (apc114 (q55 ◇ q56) q56)).symm).trans ((apc103 q55 q56).trans (rfl))).trans (rfl))).symm
  have apc117 : forall (q61 q62 : G), (((q61 ◇ q62) ◇ q62) ◇ ((q61 ◇ q62) ◇ q62)) = (((q61 ◇ q62) ◇ q62) ◇ q62) := by
    intro q61 q62
    exact ((((cg (fun t => t ◇ ((q61 ◇ q62) ◇ q62)) (apc115 q61 q62)).trans (apc39 (q61 ◇ q62) q62 q62)).symm).trans ((((cg (fun t => t ◇ ((q61 ◇ q62) ◇ q62)) (cg (fun t => t ◇ ((q61 ◇ q62) ◇ q62)) (apc114 q61 q62))).symm).trans ((h ((q61 ◇ q62) ◇ q62) ((q61 ◇ q62) ◇ q62) q62).symm)).trans (rfl))).symm
  have apc118 : forall (q63 q64 : G), ((q63 ◇ q64) ◇ ((q63 ◇ q64) ◇ q64)) = ((q63 ◇ q64) ◇ q64) := by
    intro q63 q64
    exact (((apc37 q63 q64).symm).trans ((((cg (fun t => (q63 ◇ q64) ◇ t) (apc117 q63 q64)).symm).trans (apc10 (q63 ◇ q64) q64)).trans (rfl))).symm
  have apc119 : forall (q50 q51 : G), ((((q51 ◇ q50) ◇ q50) ◇ q50) ◇ q51) = (q51 ◇ ((q51 ◇ q50) ◇ q50)) := by
    intro q50 q51
    exact ((cg (fun t => t ◇ q51) (apc117 q51 q50)).symm).trans ((((cg (fun t => t ◇ q51) (cg (fun t => t ◇ ((q51 ◇ q50) ◇ q50)) (apc118 q51 q50))).symm).trans ((apc86 q50 q51).trans (rfl))).trans (rfl))
  have apc120 : forall (q65 q66 : G), (q65 ◇ ((q65 ◇ q66) ◇ q66)) = (q65 ◇ q66) := by
    intro q65 q66
    exact ((rfl).symm).trans ((((apc119 q66 q65).symm).trans ((h q65 q66 q66).symm)).trans (rfl))
  have apc125 : forall (q67 q68 q69 : G), ((((q67 ◇ q68) ◇ q68) ◇ q69) ◇ (((q67 ◇ q68) ◇ q68) ◇ q68)) = ((((q67 ◇ q68) ◇ q68) ◇ q69) ◇ ((q67 ◇ q68) ◇ q68)) := by
    intro q67 q68 q69
    exact ((rfl).symm).trans ((((cg (fun t => (((q67 ◇ q68) ◇ q68) ◇ q69) ◇ t) (apc117 q67 q68)).symm).trans (apc43 q69 ((q67 ◇ q68) ◇ q68))).trans (rfl))
  have apc126 : forall (q70 q71 : G), ((((q70 ◇ q71) ◇ q71) ◇ (q70 ◇ q71)) ◇ ((q70 ◇ q71) ◇ q71)) = ((((q70 ◇ q71) ◇ q71) ◇ q71) ◇ (q70 ◇ q71)) := by
    intro q70 q71
    exact ((rfl).symm).trans ((((apc125 q70 q71 (q70 ◇ q71)).symm).trans (apc5 q71 (q70 ◇ q71) q71)).trans (rfl))
  have apc127 : forall (q72 q73 : G), (((((q72 ◇ q73) ◇ q73) ◇ q73) ◇ (q72 ◇ q73)) ◇ (q72 ◇ q73)) = ((q72 ◇ q73) ◇ q73) := by
    intro q72 q73
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (q72 ◇ q73)) (apc126 q72 q73)).symm).trans (apc1 q73 (q72 ◇ q73))).trans (apc118 q72 q73))
  have apc128 : forall (q74 q75 : G), (((q74 ◇ q75) ◇ q75) ◇ (q74 ◇ q75)) = (((q74 ◇ q75) ◇ q75) ◇ q75) := by
    intro q74 q75
    exact (((apc117 q74 q75).symm).trans ((((cg (fun t => t ◇ ((q74 ◇ q75) ◇ q75)) (apc127 q74 q75)).symm).trans ((h ((q74 ◇ q75) ◇ q75) (q74 ◇ q75) q75).symm)).trans (rfl))).symm
  have apc129 : forall (q76 q77 : G), ((((q76 ◇ q77) ◇ q77) ◇ q77) ◇ (q76 ◇ q77)) = ((((q76 ◇ q77) ◇ q77) ◇ q77) ◇ q77) := by
    intro q76 q77
    exact (((apc128 (q76 ◇ q77) q77).symm).trans ((((cg (fun t => (((q76 ◇ q77) ◇ q77) ◇ q77) ◇ t) (apc127 q76 q77)).symm).trans (apc120 (((q76 ◇ q77) ◇ q77) ◇ q77) (q76 ◇ q77))).trans (rfl))).symm
  have apc130 : forall (q78 q79 : G), ((q78 ◇ q79) ◇ (q78 ◇ q79)) = ((q78 ◇ q79) ◇ q79) := by
    intro q78 q79
    exact ((((cg (fun t => t ◇ (q78 ◇ q79)) (apc129 q78 q79)).trans (apc39 q78 q79 q79)).symm).trans ((((cg (fun t => t ◇ (q78 ◇ q79)) (cg (fun t => t ◇ (q78 ◇ q79)) (apc128 q78 q79))).symm).trans ((h (q78 ◇ q79) (q78 ◇ q79) q79).symm)).trans (rfl))).symm
  have apc131 : forall (q13 q14 : G), (q13 ◇ (q13 ◇ q14)) = (q13 ◇ q14) := by
    intro q13 q14
    exact (((apc120 q13 q14).symm).trans ((((cg (fun t => q13 ◇ t) (apc130 q13 q14)).symm).trans ((apc10 q13 q14).trans (rfl))).trans (rfl))).symm
  have apc132 : forall (q2 q3 : G), ((((q3 ◇ q2) ◇ q3) ◇ (q3 ◇ q2)) ◇ q3) = (q3 ◇ q2) := by
    intro q2 q3
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc1 q2 q3).trans (apc131 q3 q2))).trans (rfl))
  have apc134 : forall (q80 q81 q82 : G), (((q80 ◇ q81) ◇ q82) ◇ ((q80 ◇ q81) ◇ q81)) = (((q80 ◇ q81) ◇ q82) ◇ (q80 ◇ q81)) := by
    intro q80 q81 q82
    exact ((rfl).symm).trans ((((cg (fun t => ((q80 ◇ q81) ◇ q82) ◇ t) (apc130 q80 q81)).symm).trans (apc43 q82 (q80 ◇ q81))).trans (rfl))
  have apc135 : forall (q83 q84 : G), (((q84 ◇ q83) ◇ q84) ◇ (q84 ◇ q83)) = (((q84 ◇ q83) ◇ q83) ◇ q84) := by
    intro q83 q84
    exact ((rfl).symm).trans ((((apc134 q84 q83 q84).symm).trans (apc5 q83 q84 q83)).trans (rfl))
  have apc136 : forall (q2 q3 : G), ((((q3 ◇ q2) ◇ q2) ◇ q3) ◇ q3) = (q3 ◇ q2) := by
    intro q2 q3
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q3) (apc135 q2 q3)).symm).trans ((apc132 q2 q3).trans (rfl))).trans (rfl))
  have apc137 : forall (q85 q86 : G), ((q85 ◇ q86) ◇ q86) = ((q85 ◇ q86) ◇ q85) := by
    intro q85 q86
    exact ((apc130 q85 q86).symm).trans ((((cg (fun t => t ◇ (q85 ◇ q86)) (apc136 q86 q85)).symm).trans ((h (q85 ◇ q86) q85 q86).symm)).trans (rfl))
  have apc139 : forall (q65 q66 : G), (q65 ◇ ((q65 ◇ q66) ◇ q65)) = (q65 ◇ q66) := by
    intro q65 q66
    exact ((rfl).symm).trans ((((cg (fun t => q65 ◇ t) (apc137 q65 q66)).symm).trans ((apc120 q65 q66).trans (rfl))).trans (rfl))
  have apc142 : forall (q87 q88 q89 : G), ((((q87 ◇ q89) ◇ q88) ◇ (q87 ◇ q89)) ◇ q87) = (q87 ◇ q88) := by
    intro q87 q88 q89
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q87) (apc137 (q87 ◇ q89) q88)).symm).trans ((h q87 q88 q89).symm)).trans (rfl))
  have apc143 : forall (q90 q91 : G), ((q91 ◇ q91) ◇ q91) = ((q91 ◇ q91) ◇ q90) := by
    intro q90 q91
    exact ((rfl).symm).trans ((((apc142 (q91 ◇ q91) q91 q90).symm).trans (apc55 q91 q90 q91)).trans (apc131 (q91 ◇ q91) q90))
  have apc144 : forall (q92 q93 q94 : G), ((q94 ◇ q94) ◇ q93) = ((q94 ◇ q94) ◇ q92) := by
    intro q92 q93 q94
    exact (((rfl).symm).trans ((((apc143 q92 q94).symm).trans (apc143 q93 q94)).trans (rfl))).symm
  have apc145 : forall (q95 q96 : G), ((q96 ◇ q96) ◇ q96) = ((q96 ◇ q95) ◇ q96) := by
    intro q95 q96
    exact ((rfl).symm).trans (((((apc143 (q96 ◇ q95) q96).symm).symm).trans (apc0 q95 q96)).trans (rfl))
  have apc149 : forall (q97 q98 : G), (q98 ◇ q98) = (q98 ◇ q97) := by
    intro q97 q98
    exact (((apc139 q98 q97).symm).trans ((((cg (fun t => q98 ◇ t) (apc145 q97 q98)).symm).trans (apc139 q98 q98)).trans (rfl))).symm
  have apc153 : forall (q99 q100 q101 q102 : G), ((q102 ◇ q102) ◇ q100) = ((q102 ◇ q99) ◇ q101) := by
    intro q99 q100 q101 q102
    exact (((rfl).symm).trans ((((cg (fun t => t ◇ q101) (apc149 q99 q102)).symm).trans (apc144 q100 q101 q102)).trans (rfl))).symm
  exact ((apc153 y ((x ◇ y) ◇ y) y x).symm).trans (((apc153 (z ◇ w) ((x ◇ y) ◇ y) u x).symm).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_53228_to_61213 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_53228_to_61213
