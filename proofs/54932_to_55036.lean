-- Equation54932 → Equation55036
-- Recorded verdict: true
-- Premise: x ◇ (y ◇ x) = y ◇ ((x ◇ z) ◇ z)
-- Conclusion: x ◇ (y ◇ x) = z ◇ ((w ◇ u) ◇ u)
-- Original submission SHA-256: 226848e4688aed552c7579af3efb9c1797f784057937cafd84c32964ec1a776f
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ x) = y ◇ ((x ◇ z) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ (y ◇ x) = z ◇ ((w ◇ u) ◇ u)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have cg : ∀ (f : G → G) {a b : G}, a = b → f a = f b := by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (x y z : G), (y ◇ ((x ◇ z) ◇ z)) = (y ◇ ((x ◇ x) ◇ x)) := by
    intro x y z
    exact ((rfl).symm).trans (((h x y z).symm.trans (h x y x)).trans (rfl))
  have apc1 : forall (q0 q1 : G), (q1 ◇ ((q0 ◇ q0) ◇ q0)) = (q0 ◇ (q1 ◇ q0)) := by
    intro q0 q1
    exact ((rfl).symm).trans ((((apc0 q0 q1 q0).symm).trans ((h q0 q1 q0).symm)).trans (rfl))
  have apc2 : forall (q2 q3 q4 q5 : G), (q5 ◇ ((q2 ◇ (q4 ◇ q2)) ◇ ((q2 ◇ q3) ◇ q3))) = (q4 ◇ (q5 ◇ q4)) := by
    intro q2 q3 q4 q5
    exact ((rfl).symm).trans ((((cg (fun t => q5 ◇ t) (cg (fun t => t ◇ ((q2 ◇ q3) ◇ q3)) ((h q2 q4 q3).symm))).symm).trans ((h q4 q5 ((q2 ◇ q3) ◇ q3)).symm)).trans (rfl))
  have apc3 : forall (q6 q7 : G), ((q6 ◇ q6) ◇ (q7 ◇ (q6 ◇ q6))) = (q6 ◇ (q7 ◇ q6)) := by
    intro q6 q7
    exact ((rfl).symm).trans ((((apc2 q6 q6 (q6 ◇ q6) q7).symm).trans ((h q6 q7 ((q6 ◇ q6) ◇ q6)).symm)).trans (rfl))
  have apc4 : forall (q8 q9 q10 : G), (q10 ◇ (q8 ◇ ((q8 ◇ (q9 ◇ q8)) ◇ q8))) = (q9 ◇ (q10 ◇ q9)) := by
    intro q8 q9 q10
    exact ((rfl).symm).trans ((((cg (fun t => q10 ◇ t) ((h q8 (q8 ◇ (q9 ◇ q8)) q8).symm)).symm).trans (apc2 q8 q8 q9 q10)).trans (rfl))
  have apc6 : forall (q11 q12 : G), (q11 ◇ ((q12 ◇ (q11 ◇ q11)) ◇ q11)) = (q12 ◇ ((q11 ◇ q11) ◇ q12)) := by
    intro q11 q12
    exact ((rfl).symm).trans ((((apc3 q11 (q12 ◇ (q11 ◇ q11))).symm).trans ((h q12 (q11 ◇ q11) (q11 ◇ q11)).symm)).trans (rfl))
  have apc7 : forall (q13 q14 : G), (q14 ◇ (q13 ◇ (q13 ◇ q13))) = (q13 ◇ (q14 ◇ q13)) := by
    intro q13 q14
    exact ((cg (fun t => q14 ◇ t) (apc1 q13 q13)).symm).trans ((((cg (fun t => q14 ◇ t) (apc6 q13 q13)).symm).trans (apc4 q13 q13 q14)).trans (rfl))
  have apc8 : forall (q15 q16 q17 q18 : G), (q18 ◇ ((q15 ◇ (q17 ◇ q15)) ◇ (((q15 ◇ q15) ◇ q16) ◇ q16))) = (q17 ◇ (q18 ◇ q17)) := by
    intro q15 q16 q17 q18
    exact ((rfl).symm).trans ((((cg (fun t => q18 ◇ t) (cg (fun t => t ◇ (((q15 ◇ q15) ◇ q16) ◇ q16)) (apc3 q15 q17))).symm).trans (apc2 (q15 ◇ q15) q16 q17 q18)).trans (rfl))
  have apc9 : forall (q19 q20 : G), (((q19 ◇ q19) ◇ q19) ◇ (q19 ◇ (q20 ◇ q19))) = (q19 ◇ (q20 ◇ q19)) := by
    intro q19 q20
    exact ((cg (fun t => ((q19 ◇ q19) ◇ q19) ◇ t) (apc1 q19 q20)).symm).trans ((((apc8 q19 q19 ((q19 ◇ q19) ◇ q19) q20).symm).trans ((h q19 q20 (((q19 ◇ q19) ◇ q19) ◇ q19)).symm)).trans (rfl))
  have apc11 : forall (q21 q22 : G), (q22 ◇ (((q21 ◇ q21) ◇ q21) ◇ q22)) = (q21 ◇ ((q21 ◇ (q22 ◇ q21)) ◇ q21)) := by
    intro q21 q22
    exact (((rfl).symm).trans ((((apc9 q21 (q21 ◇ (q22 ◇ q21))).symm).trans (apc4 q21 q22 ((q21 ◇ q21) ◇ q21))).trans (rfl))).symm
  have apc15 : forall (q23 q24 : G), (q23 ◇ ((q23 ◇ ((q24 ◇ q24) ◇ q23)) ◇ q23)) = (q23 ◇ ((q23 ◇ (q24 ◇ q23)) ◇ q23)) := by
    intro q23 q24
    exact ((rfl).symm).trans ((((apc11 q23 (q24 ◇ q24)).symm).trans (apc3 q24 ((q23 ◇ q23) ◇ q23))).trans (apc11 q23 q24))
  have apc18 : forall (q25 q26 q27 : G), (q27 ◇ (q26 ◇ ((q25 ◇ (q26 ◇ q25)) ◇ q26))) = ((q25 ◇ q26) ◇ (q27 ◇ (q25 ◇ q26))) := by
    intro q25 q26 q27
    exact ((rfl).symm).trans ((((cg (fun t => q27 ◇ t) (cg (fun t => q26 ◇ t) (cg (fun t => t ◇ q26) ((h q25 q26 q26).symm)))).symm).trans (apc4 q26 (q25 ◇ q26) q27)).trans (rfl))
  have apc24 : forall (q28 q29 q30 q31 : G), (q31 ◇ ((q29 ◇ (q30 ◇ q29)) ◇ ((q29 ◇ (q28 ◇ q29)) ◇ (q28 ◇ (q29 ◇ q29))))) = (q30 ◇ (q31 ◇ q30)) := by
    intro q28 q29 q30 q31
    exact ((rfl).symm).trans ((((cg (fun t => q31 ◇ t) (cg (fun t => (q29 ◇ (q30 ◇ q29)) ◇ t) (cg (fun t => t ◇ (q28 ◇ (q29 ◇ q29))) (apc3 q29 q28)))).symm).trans (apc8 q29 (q28 ◇ (q29 ◇ q29)) q30 q31)).trans (rfl))
  have apc25 : forall (q32 q33 : G), ((q32 ◇ (q32 ◇ q32)) ◇ (q32 ◇ (q33 ◇ q32))) = (q32 ◇ (q33 ◇ q32)) := by
    intro q32 q33
    exact (((rfl).symm).trans ((((apc24 q32 q32 q32 q33).symm).trans (apc7 (q32 ◇ (q32 ◇ q32)) q33)).trans (cg (fun t => (q32 ◇ (q32 ◇ q32)) ◇ t) (apc7 q32 q33)))).symm
  have apc26 : forall (q34 q35 q36 q9 q10 : G), (q10 ◇ ((((q34 ◇ q35) ◇ q35) ◇ (q34 ◇ (q9 ◇ q34))) ◇ ((((q34 ◇ q35) ◇ q35) ◇ q36) ◇ q36))) = (q9 ◇ (q10 ◇ q9)) := by
    intro q34 q35 q36 q9 q10
    exact ((rfl).symm).trans ((((cg (fun t => q10 ◇ t) (cg (fun t => t ◇ ((((q34 ◇ q35) ◇ q35) ◇ q36) ◇ q36)) (cg (fun t => ((q34 ◇ q35) ◇ q35) ◇ t) ((h q34 q9 q35).symm)))).symm).trans (apc2 ((q34 ◇ q35) ◇ q35) q36 q9 q10)).trans (rfl))
  have apc27 : forall (q37 q38 : G), (q38 ◇ ((q37 ◇ (q37 ◇ q37)) ◇ q38)) = (q37 ◇ ((q37 ◇ (q38 ◇ q37)) ◇ q37)) := by
    intro q37 q38
    exact (((rfl).symm).trans ((((apc25 q37 (q37 ◇ (q38 ◇ q37))).symm).trans (apc4 q37 q38 (q37 ◇ (q37 ◇ q37)))).trans (rfl))).symm
  have apc30 : forall (q39 q40 q41 q42 : G), (q42 ◇ ((q39 ◇ (q41 ◇ q39)) ◇ ((((q39 ◇ q39) ◇ q39) ◇ q40) ◇ q40))) = (q41 ◇ (q42 ◇ q41)) := by
    intro q39 q40 q41 q42
    exact ((rfl).symm).trans ((((cg (fun t => q42 ◇ t) (cg (fun t => t ◇ ((((q39 ◇ q39) ◇ q39) ◇ q40) ◇ q40)) (apc9 q39 q41))).symm).trans (apc26 q39 q39 q40 q41 q42)).trans (rfl))
  have apc47 : forall (q43 q44 q45 q46 : G), (q46 ◇ ((q44 ◇ (q45 ◇ q44)) ◇ ((q44 ◇ (q43 ◇ q44)) ◇ (q44 ◇ (q43 ◇ q44))))) = (q45 ◇ (q46 ◇ q45)) := by
    intro q43 q44 q45 q46
    exact ((rfl).symm).trans ((((cg (fun t => q46 ◇ t) (cg (fun t => (q44 ◇ (q45 ◇ q44)) ◇ t) (cg (fun t => t ◇ (q44 ◇ (q43 ◇ q44))) (apc9 q44 q43)))).symm).trans (apc30 q44 (q44 ◇ (q43 ◇ q44)) q45 q46)).trans (rfl))
  have apc48 : forall (q47 q48 q49 : G), ((q47 ◇ (q48 ◇ q47)) ◇ (q49 ◇ (q47 ◇ (q48 ◇ q47)))) = (q48 ◇ (q49 ◇ q48)) := by
    intro q47 q48 q49
    exact (((rfl).symm).trans ((((apc47 q48 q47 q48 q49).symm).trans (apc7 (q47 ◇ (q48 ◇ q47)) q49)).trans (rfl))).symm
  have apc49 : forall (q50 q51 q52 : G), ((q51 ◇ q50) ◇ (q52 ◇ (q51 ◇ q50))) = (q50 ◇ (q52 ◇ q50)) := by
    intro q50 q51 q52
    exact ((apc18 q51 q50 q52).symm).trans ((((cg (fun t => q52 ◇ t) (apc48 q51 q50 (q51 ◇ (q50 ◇ q51)))).symm).trans (apc47 q50 q51 q50 q52)).trans (rfl))
  have apc50 : forall (q47 q48 q49 q50 q51 q52 : G), (q48 ◇ (q49 ◇ q48)) = (q47 ◇ (q49 ◇ q47)) := by
    intro q47 q48 q49 q50 q51 q52
    exact (((rfl).symm).trans (((((apc49 (q48 ◇ q47) q47 q49).trans (apc49 q47 q48 q49)).symm).trans ((apc48 q47 q48 q49).trans (rfl))).trans (rfl))).symm
  have apc51 : forall (q53 q54 q55 : G), (q53 ◇ ((q54 ◇ q55) ◇ q53)) = (q54 ◇ (q55 ◇ q54)) := by
    intro q53 q54 q55
    exact ((rfl).symm).trans ((((apc50 q53 q55 (q54 ◇ q55) q53 q53 q53).symm).trans ((h q54 q55 q55).symm)).trans (rfl))
  have apc52 : forall (q23 q24 q53 q54 q55 : G), (q24 ◇ (q24 ◇ q24)) = (q24 ◇ (q23 ◇ q24)) := by
    intro q23 q24 q53 q54 q55
    exact ((rfl).symm).trans ((((((cg (fun t => q23 ◇ t) (cg (fun t => t ◇ q23) (apc51 q23 q24 q24))).trans (apc51 q23 q24 (q24 ◇ q24))).trans (apc51 q24 q24 q24)).symm).trans ((apc15 q23 q24).trans ((apc51 q23 q23 (q24 ◇ q23)).trans (apc51 q23 q24 q23)))).trans (rfl))
  have apc53 : forall (q37 q38 q53 q54 q55 : G), (q38 ◇ (q37 ◇ q38)) = (q37 ◇ (q37 ◇ q37)) := by
    intro q37 q38 q53 q54 q55
    exact (((rfl).symm).trans (((((apc51 q38 q37 (q37 ◇ q37)).trans (apc51 q37 q37 q37)).symm).trans ((apc27 q37 q38).trans ((apc51 q37 q37 (q38 ◇ q37)).trans (apc51 q37 q38 q37)))).trans (rfl))).symm
  have apc54 : forall (q56 q57 q58 : G), (q57 ◇ (q58 ◇ q57)) = (q56 ◇ (q56 ◇ q56)) := by
    intro q56 q57 q58
    exact (((apc53 q56 q58 (q58 ◇ (q56 ◇ q58)) (q58 ◇ (q56 ◇ q58)) (q58 ◇ (q56 ◇ q58))).symm).trans ((((apc52 q56 q58 q56 q56 q56).symm).trans (apc50 q57 q58 q58 q56 q56 q56)).trans (rfl))).symm
  have apc61 : forall (q53 q59 q54 q60 : G), (q60 ◇ ((q53 ◇ (q59 ◇ q53)) ◇ (q59 ◇ q54))) = (q54 ◇ (q60 ◇ q54)) := by
    intro q53 q59 q54 q60
    exact ((rfl).symm).trans ((((cg (fun t => q60 ◇ t) (cg (fun t => t ◇ (q59 ◇ q54)) (apc50 q53 q54 q59 q53 q53 q53))).symm).trans ((h q54 q60 (q59 ◇ q54)).symm)).trans (rfl))
  have apc62 : forall (q61 q62 q63 : G), (q61 ◇ (q63 ◇ q61)) = (q61 ◇ (q62 ◇ q61)) := by
    intro q61 q62 q63
    exact (((apc51 q62 q61 q62).symm).trans ((((apc61 q63 q61 q62 (q61 ◇ q62)).symm).trans (apc51 (q61 ◇ q62) q63 (q61 ◇ q63))).trans (apc51 q63 q61 q63))).symm
  have apc141 : forall (q61 q62 q63 : G), (q61 ◇ (q62 ◇ q61)) = (q61 ◇ (q61 ◇ q61)) := by
    intro q61 q62 q63
    exact ((rfl).symm).trans (((apc62 q61 q62 q63).symm.trans (apc62 q61 q61 q63)).trans (rfl))
  have apc142 : forall (x y z : G), (y ◇ ((x ◇ z) ◇ z)) = (x ◇ (x ◇ x)) := by
    intro x y z
    exact ((rfl).symm).trans (((h x y z).symm.trans (h x y x)).trans ((apc1 x y).trans (apc141 x y (x ◇ (y ◇ x)))))
  exact (calc
    (x ◇ (y ◇ x)) = (w ◇ (w ◇ w)) := apc54 w x y
    _ = (z ◇ ((w ◇ u) ◇ u)) := (apc142 w z u).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_54932_to_55036 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_54932_to_55036
