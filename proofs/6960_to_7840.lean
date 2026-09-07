-- Equation6960 → Equation7840
-- Recorded verdict: true
-- Premise: x = y ◇ (z ◇ ((x ◇ x) ◇ (y ◇ z)))
-- Conclusion: x = y ◇ (z ◇ ((x ◇ (x ◇ z)) ◇ y))
-- Original submission SHA-256: 4d4216a6c96c0faeef856c2be0d63e924ba0534c07f9bf7cf5df8bd808f2d611
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (z ◇ ((x ◇ x) ◇ (y ◇ z)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (z ◇ ((x ◇ (x ◇ z)) ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f : G → G) {a b : G}, a = b → f a = f b := by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1 q2 : G), (q2 ◇ (((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q2)) ◇ q0)) = q1 := by
    intro q0 q1 q2
    exact ((rfl).symm).trans ((((cg (fun t => q2 ◇ t) (cg (fun t => ((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q2)) ◇ t) ((h q0 (q1 ◇ q1) q2).symm))).symm).trans ((h q1 q2 ((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ q2))).symm)).trans (rfl))
  have apc1 : forall (q3 q4 q5 : G), (((q5 ◇ q5) ◇ ((q3 ◇ q3) ◇ (q4 ◇ q4))) ◇ (q5 ◇ q3)) = q4 := by
    intro q3 q4 q5
    exact ((rfl).symm).trans ((((cg (fun t => ((q5 ◇ q5) ◇ ((q3 ◇ q3) ◇ (q4 ◇ q4))) ◇ t) (cg (fun t => q5 ◇ t) (apc0 q5 q3 (q4 ◇ q4)))).symm).trans ((h q4 ((q5 ◇ q5) ◇ ((q3 ◇ q3) ◇ (q4 ◇ q4))) q5).symm)).trans (rfl))
  have apc3 : forall (q0 q6 q1 q2 : G), (q2 ◇ ((q6 ◇ ((q0 ◇ q0) ◇ (q2 ◇ q6))) ◇ ((q1 ◇ q1) ◇ q0))) = q1 := by
    intro q0 q6 q1 q2
    exact ((rfl).symm).trans ((((cg (fun t => q2 ◇ t) (cg (fun t => (q6 ◇ ((q0 ◇ q0) ◇ (q2 ◇ q6))) ◇ t) (cg (fun t => (q1 ◇ q1) ◇ t) ((h q0 q2 q6).symm)))).symm).trans ((h q1 q2 (q6 ◇ ((q0 ◇ q0) ◇ (q2 ◇ q6)))).symm)).trans (rfl))
  have apc4 : forall (q7 : G), (((q7 ◇ q7) ◇ (q7 ◇ q7)) ◇ ((q7 ◇ q7) ◇ (q7 ◇ q7))) = q7 := by
    intro q7
    exact ((rfl).symm).trans ((((cg (fun t => ((q7 ◇ q7) ◇ (q7 ◇ q7)) ◇ t) (apc1 q7 ((q7 ◇ q7) ◇ (q7 ◇ q7)) (q7 ◇ q7))).symm).trans (apc3 q7 ((q7 ◇ q7) ◇ (q7 ◇ q7)) q7 ((q7 ◇ q7) ◇ (q7 ◇ q7)))).trans (rfl))
  have apc5 : forall (q8 : G), (q8 ◇ ((q8 ◇ q8) ◇ q8)) = q8 := by
    intro q8
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ ((q8 ◇ q8) ◇ q8)) (apc4 q8)).symm).trans (apc1 q8 q8 (q8 ◇ q8))).trans (rfl))
  have apc9 : forall (q9 q10 : G), (q10 ◇ (((q10 ◇ q10) ◇ q10) ◇ ((q9 ◇ q9) ◇ q10))) = q9 := by
    intro q9 q10
    exact ((rfl).symm).trans ((((cg (fun t => q10 ◇ t) (cg (fun t => ((q10 ◇ q10) ◇ q10) ◇ t) (cg (fun t => (q9 ◇ q9) ◇ t) (apc5 q10)))).symm).trans ((h q9 q10 ((q10 ◇ q10) ◇ q10)).symm)).trans (rfl))
  have apc11 : forall (q11 q12 q13 : G), (q12 ◇ (q13 ◇ (q11 ◇ (q12 ◇ q13)))) = ((q11 ◇ q11) ◇ (q11 ◇ q11)) := by
    intro q11 q12 q13
    exact ((rfl).symm).trans ((((cg (fun t => q12 ◇ t) (cg (fun t => q13 ◇ t) (cg (fun t => t ◇ (q12 ◇ q13)) (apc4 q11)))).symm).trans ((h ((q11 ◇ q11) ◇ (q11 ◇ q11)) q12 q13).symm)).trans (rfl))
  have apc16 : forall (q14 q15 q16 : G), (q16 ◇ ((q14 ◇ ((q15 ◇ q15) ◇ q16)) ◇ ((q14 ◇ q14) ◇ (q14 ◇ q14)))) = q15 := by
    intro q14 q15 q16
    exact ((rfl).symm).trans ((((cg (fun t => q16 ◇ t) (cg (fun t => t ◇ ((q14 ◇ q14) ◇ (q14 ◇ q14))) (cg (fun t => t ◇ ((q15 ◇ q15) ◇ q16)) (apc4 q14)))).symm).trans (apc0 ((q14 ◇ q14) ◇ (q14 ◇ q14)) q15 q16)).trans (rfl))
  have apc20 : forall (q17 q18 q19 q20 : G), ((q18 ◇ ((q17 ◇ q17) ◇ ((q20 ◇ q20) ◇ q18))) ◇ (((q19 ◇ q19) ◇ q17) ◇ q19)) = q20 := by
    intro q17 q18 q19 q20
    exact ((rfl).symm).trans ((((cg (fun t => (q18 ◇ ((q17 ◇ q17) ◇ ((q20 ◇ q20) ◇ q18))) ◇ t) (cg (fun t => t ◇ q19) (cg (fun t => (q19 ◇ q19) ◇ t) ((h q17 (q20 ◇ q20) q18).symm)))).symm).trans (apc0 q19 q20 (q18 ◇ ((q17 ◇ q17) ◇ ((q20 ◇ q20) ◇ q18))))).trans (rfl))
  have apc21 : forall (q21 : G), (((q21 ◇ q21) ◇ q21) ◇ ((q21 ◇ q21) ◇ q21)) = ((q21 ◇ q21) ◇ q21) := by
    intro q21
    exact (((rfl).symm).trans ((((apc20 q21 (((q21 ◇ q21) ◇ q21) ◇ ((q21 ◇ q21) ◇ q21)) q21 ((q21 ◇ q21) ◇ q21)).symm).trans (apc1 q21 (((q21 ◇ q21) ◇ q21) ◇ ((q21 ◇ q21) ◇ q21)) ((q21 ◇ q21) ◇ q21))).trans (rfl))).symm
  have apc22 : forall (q22 q23 q24 : G), (q23 ◇ (q24 ◇ (((q22 ◇ q22) ◇ q22) ◇ (q23 ◇ q24)))) = ((q22 ◇ q22) ◇ q22) := by
    intro q22 q23 q24
    exact ((rfl).symm).trans ((((cg (fun t => q23 ◇ t) (cg (fun t => q24 ◇ t) (cg (fun t => t ◇ (q23 ◇ q24)) (apc21 q22)))).symm).trans ((h ((q22 ◇ q22) ◇ q22) q23 q24).symm)).trans (rfl))
  have apc23 : forall (q25 q26 : G), ((q26 ◇ q26) ◇ q26) = ((q25 ◇ q25) ◇ q25) := by
    intro q25 q26
    exact (((rfl).symm).trans ((((cg (fun t => (q25 ◇ q25) ◇ t) (apc9 q25 q26)).symm).trans (apc22 q26 (q25 ◇ q25) q26)).trans (rfl))).symm
  have apc24 : forall (q27 q28 : G), (q28 ◇ ((q27 ◇ q27) ◇ q27)) = q28 := by
    intro q27 q28
    exact ((rfl).symm).trans ((((cg (fun t => q28 ◇ t) (apc23 q27 q28)).symm).trans (apc5 q28)).trans (rfl))
  have apc26 : forall (q29 q30 : G), ((q30 ◇ q30) ◇ (q30 ◇ (q29 ◇ q29))) = q29 := by
    intro q29 q30
    exact ((rfl).symm).trans ((((cg (fun t => (q30 ◇ q30) ◇ t) (cg (fun t => q30 ◇ t) (apc24 q30 (q29 ◇ q29)))).symm).trans ((h q29 (q30 ◇ q30) q30).symm)).trans (rfl))
  have apc30 : forall (q31 q32 q33 q34 : G), (((q33 ◇ q33) ◇ ((q31 ◇ q31) ◇ (q32 ◇ q32))) ◇ ((q33 ◇ q31) ◇ ((q34 ◇ q34) ◇ q32))) = q34 := by
    intro q31 q32 q33 q34
    exact ((rfl).symm).trans ((((cg (fun t => ((q33 ◇ q33) ◇ ((q31 ◇ q31) ◇ (q32 ◇ q32))) ◇ t) (cg (fun t => (q33 ◇ q31) ◇ t) (cg (fun t => (q34 ◇ q34) ◇ t) (apc1 q31 q32 q33)))).symm).trans ((h q34 ((q33 ◇ q33) ◇ ((q31 ◇ q31) ◇ (q32 ◇ q32))) (q33 ◇ q31)).symm)).trans (rfl))
  have apc35 : forall (q35 q36 q37 : G), ((q36 ◇ (q35 ◇ q35)) ◇ (((q37 ◇ q37) ◇ q35) ◇ q37)) = q36 := by
    intro q35 q36 q37
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (((q37 ◇ q37) ◇ q35) ◇ q37)) (cg (fun t => q36 ◇ t) (apc24 q36 (q35 ◇ q35)))).symm).trans (apc20 q35 q36 q37 q36)).trans (rfl))
  have apc39 : forall (q38 q39 : G), ((q39 ◇ q39) ◇ (q39 ◇ q38)) = ((q38 ◇ q38) ◇ (q38 ◇ q38)) := by
    intro q38 q39
    exact ((rfl).symm).trans ((((cg (fun t => (q39 ◇ q39) ◇ t) (cg (fun t => q39 ◇ t) (apc24 q39 q38))).symm).trans (apc11 q38 (q39 ◇ q39) q39)).trans (rfl))
  have apc60 : forall (q40 q41 q42 : G), ((q42 ◇ (q40 ◇ q40)) ◇ ((q41 ◇ q40) ◇ ((q41 ◇ q41) ◇ (q41 ◇ q41)))) = q42 := by
    intro q40 q41 q42
    exact ((rfl).symm).trans ((((cg (fun t => (q42 ◇ (q40 ◇ q40)) ◇ t) (cg (fun t => t ◇ ((q41 ◇ q41) ◇ (q41 ◇ q41))) (cg (fun t => q41 ◇ t) (apc26 q40 q42)))).symm).trans (apc16 q41 q42 (q42 ◇ (q40 ◇ q40)))).trans (rfl))
  have apc61 : forall (q43 q44 q45 : G), ((q44 ◇ ((q45 ◇ (q43 ◇ q43)) ◇ (q45 ◇ (q43 ◇ q43)))) ◇ (q43 ◇ q45)) = q44 := by
    intro q43 q44 q45
    exact ((rfl).symm).trans ((((cg (fun t => (q44 ◇ ((q45 ◇ (q43 ◇ q43)) ◇ (q45 ◇ (q43 ◇ q43)))) ◇ t) (cg (fun t => t ◇ q45) (apc26 q43 q45))).symm).trans (apc35 (q45 ◇ (q43 ◇ q43)) q44 q45)).trans (rfl))
  have apc62 : forall (q46 q47 : G), ((q47 ◇ q46) ◇ (q46 ◇ (q46 ◇ q46))) = q47 := by
    intro q46 q47
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (q46 ◇ (q46 ◇ q46))) (cg (fun t => q47 ◇ t) (apc26 q46 (q46 ◇ q46)))).symm).trans (apc61 q46 q47 (q46 ◇ q46))).trans (rfl))
  have apc63 : forall (q48 q49 q50 : G), ((q49 ◇ q48) ◇ ((q48 ◇ (q48 ◇ q48)) ◇ ((q50 ◇ q50) ◇ q49))) = q50 := by
    intro q48 q49 q50
    exact ((rfl).symm).trans ((((cg (fun t => (q49 ◇ q48) ◇ t) (cg (fun t => (q48 ◇ (q48 ◇ q48)) ◇ t) (cg (fun t => (q50 ◇ q50) ◇ t) (apc62 q48 q49)))).symm).trans ((h q50 (q49 ◇ q48) (q48 ◇ (q48 ◇ q48))).symm)).trans (rfl))
  have apc64 : forall (q51 : G), ((q51 ◇ (q51 ◇ q51)) ◇ (q51 ◇ q51)) = (q51 ◇ q51) := by
    intro q51
    exact ((rfl).symm).trans ((((cg (fun t => (q51 ◇ (q51 ◇ q51)) ◇ t) (apc35 (q51 ◇ q51) (q51 ◇ q51) q51)).symm).trans (apc63 (q51 ◇ q51) q51 (q51 ◇ q51))).trans (rfl))
  have apc66 : forall (q52 q53 : G), ((((q52 ◇ q52) ◇ q53) ◇ (q53 ◇ q53)) ◇ q52) = q53 := by
    intro q52 q53
    exact ((rfl).symm).trans ((((cg (fun t => (((q52 ◇ q52) ◇ q53) ◇ (q53 ◇ q53)) ◇ t) (apc30 q53 q53 q53 q52)).symm).trans (apc63 (q53 ◇ q53) ((q52 ◇ q52) ◇ q53) q53)).trans (rfl))
  have apc68 : forall (q54 q55 q56 : G), (((q56 ◇ (q54 ◇ q54)) ◇ q55) ◇ ((q55 ◇ (q55 ◇ q55)) ◇ q54)) = q56 := by
    intro q54 q55 q56
    exact ((rfl).symm).trans ((((cg (fun t => ((q56 ◇ (q54 ◇ q54)) ◇ q55) ◇ t) (cg (fun t => (q55 ◇ (q55 ◇ q55)) ◇ t) (apc26 q54 q56))).symm).trans (apc63 q55 (q56 ◇ (q54 ◇ q54)) q56)).trans (rfl))
  have apc73 : forall (q57 q58 : G), ((q57 ◇ q57) ◇ (((q58 ◇ q58) ◇ q57) ◇ q58)) = (q57 ◇ (q57 ◇ q57)) := by
    intro q57 q58
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (((q58 ◇ q58) ◇ q57) ◇ q58)) (apc64 q57)).symm).trans (apc35 q57 (q57 ◇ (q57 ◇ q57)) q58)).trans (rfl))
  have apc74 : forall (q59 q60 : G), (((q60 ◇ q60) ◇ q59) ◇ (q60 ◇ (q59 ◇ (q59 ◇ q59)))) = q59 := by
    intro q59 q60
    exact ((rfl).symm).trans ((((cg (fun t => ((q60 ◇ q60) ◇ q59) ◇ t) (cg (fun t => q60 ◇ t) (apc73 q59 q60))).symm).trans ((h q59 ((q60 ◇ q60) ◇ q59) q60).symm)).trans (rfl))
  have apc75 : forall (q61 q62 : G), ((((q61 ◇ q62) ◇ (q61 ◇ q62)) ◇ q62) ◇ q61) = q62 := by
    intro q61 q62
    exact ((rfl).symm).trans ((((cg (fun t => (((q61 ◇ q62) ◇ (q61 ◇ q62)) ◇ q62) ◇ t) (apc62 q62 q61)).symm).trans (apc74 q62 (q61 ◇ q62))).trans (rfl))
  have apc77 : forall (q63 : G), ((((q63 ◇ q63) ◇ q63) ◇ q63) ◇ (q63 ◇ q63)) = q63 := by
    intro q63
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (q63 ◇ q63)) (cg (fun t => t ◇ q63) (apc24 q63 ((q63 ◇ q63) ◇ q63)))).symm).trans (apc75 (q63 ◇ q63) q63)).trans (rfl))
  have apc78 : forall (q64 q65 : G), ((((q64 ◇ q64) ◇ q64) ◇ q65) ◇ (q65 ◇ q65)) = q65 := by
    intro q64 q65
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (q65 ◇ q65)) (cg (fun t => t ◇ q65) (apc23 q64 q65))).symm).trans (apc77 q65)).trans (rfl))
  have apc87 : forall (q66 q67 : G), (((q67 ◇ q67) ◇ q66) ◇ (q66 ◇ q66)) = (q66 ◇ (q67 ◇ (q67 ◇ q67))) := by
    intro q66 q67
    exact (((rfl).symm).trans ((((cg (fun t => t ◇ (q67 ◇ (q67 ◇ q67))) (apc66 q67 q66)).symm).trans (apc62 q67 (((q67 ◇ q67) ◇ q66) ◇ (q66 ◇ q66)))).trans (rfl))).symm
  have apc88 : forall (q52 q53 q66 q67 : G), ((q53 ◇ (q52 ◇ (q52 ◇ q52))) ◇ q52) = q53 := by
    intro q52 q53 q66 q67
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q52) (apc87 q53 q52)).symm).trans ((apc66 q52 q53).trans (rfl))).trans (rfl))
  have apc89 : forall (q68 q69 q70 q71 : G), (q71 ◇ ((q69 ◇ (q68 ◇ (q71 ◇ q69))) ◇ ((q70 ◇ q70) ◇ ((q68 ◇ q68) ◇ (q68 ◇ q68))))) = q70 := by
    intro q68 q69 q70 q71
    exact ((rfl).symm).trans ((((cg (fun t => q71 ◇ t) (cg (fun t => t ◇ ((q70 ◇ q70) ◇ ((q68 ◇ q68) ◇ (q68 ◇ q68)))) (cg (fun t => q69 ◇ t) (cg (fun t => t ◇ (q71 ◇ q69)) (apc4 q68))))).symm).trans (apc3 ((q68 ◇ q68) ◇ (q68 ◇ q68)) q69 q70 q71)).trans (rfl))
  have apc90 : forall (q72 q73 q74 : G), (q74 ◇ ((q73 ◇ (q72 ◇ (q74 ◇ q73))) ◇ q72)) = (q72 ◇ q72) := by
    intro q72 q73 q74
    exact ((rfl).symm).trans ((((cg (fun t => q74 ◇ t) (cg (fun t => (q73 ◇ (q72 ◇ (q74 ◇ q73))) ◇ t) (apc26 q72 (q72 ◇ q72)))).symm).trans (apc89 q72 q73 (q72 ◇ q72) q74)).trans (rfl))
  have apc92 : forall (q75 q76 : G), (q75 ◇ (((q75 ◇ q75) ◇ q76) ◇ ((q75 ◇ q75) ◇ q76))) = q76 := by
    intro q75 q76
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (((q75 ◇ q75) ◇ q76) ◇ ((q75 ◇ q75) ◇ q76))) (apc16 ((q75 ◇ q75) ◇ q76) q75 q76)).symm).trans (apc88 (((q75 ◇ q75) ◇ q76) ◇ ((q75 ◇ q75) ◇ q76)) q76 q75 q75)).trans (rfl))
  have apc97 : forall (q77 q78 q79 : G), ((q77 ◇ (q79 ◇ ((q78 ◇ q78) ◇ q77))) ◇ (q79 ◇ (q79 ◇ q79))) = q78 := by
    intro q77 q78 q79
    exact ((rfl).symm).trans ((((cg (fun t => (q77 ◇ (q79 ◇ ((q78 ◇ q78) ◇ q77))) ◇ t) (cg (fun t => q79 ◇ t) (apc90 q79 q77 (q78 ◇ q78)))).symm).trans ((h q78 (q77 ◇ (q79 ◇ ((q78 ◇ q78) ◇ q77))) q79).symm)).trans (rfl))
  have apc98 : forall (q80 q81 q82 : G), (q80 ◇ (q82 ◇ ((q81 ◇ q81) ◇ q80))) = (q81 ◇ q82) := by
    intro q80 q81 q82
    exact (((rfl).symm).trans ((((cg (fun t => t ◇ q82) (apc97 q80 q81 q82)).symm).trans (apc88 q82 (q80 ◇ (q82 ◇ ((q81 ◇ q81) ◇ q80))) q80 q80)).trans (rfl))).symm
  have apc99 : forall (q83 q84 q85 : G), ((q84 ◇ (q83 ◇ q83)) ◇ (q85 ◇ q83)) = (q84 ◇ q85) := by
    intro q83 q84 q85
    exact ((rfl).symm).trans ((((cg (fun t => (q84 ◇ (q83 ◇ q83)) ◇ t) (cg (fun t => q85 ◇ t) (apc26 q83 q84))).symm).trans (apc98 (q84 ◇ (q83 ◇ q83)) q84 q85)).trans (rfl))
  have apc100 : forall (q86 q87 q88 : G), (q88 ◇ (((q86 ◇ q86) ◇ (q87 ◇ q87)) ◇ (q86 ◇ q88))) = q87 := by
    intro q86 q87 q88
    exact ((rfl).symm).trans ((((cg (fun t => q88 ◇ t) (cg (fun t => ((q86 ◇ q86) ◇ (q87 ◇ q87)) ◇ t) (apc98 (q87 ◇ q87) q86 q88))).symm).trans ((h q87 q88 ((q86 ◇ q86) ◇ (q87 ◇ q87))).symm)).trans (rfl))
  have apc101 : forall (q89 q90 : G), ((q89 ◇ q90) ◇ q89) = ((q89 ◇ q89) ◇ q90) := by
    intro q89 q90
    exact ((rfl).symm).trans ((((cg (fun t => (q89 ◇ q90) ◇ t) (apc100 q89 q89 q90)).symm).trans (apc98 (q89 ◇ q90) (q89 ◇ q89) q90)).trans (rfl))
  have apc103 : forall (q91 q92 q93 : G), (((q91 ◇ q91) ◇ q91) ◇ (q93 ◇ (q92 ◇ q92))) = (q92 ◇ q93) := by
    intro q91 q92 q93
    exact ((rfl).symm).trans ((((cg (fun t => ((q91 ◇ q91) ◇ q91) ◇ t) (cg (fun t => q93 ◇ t) (apc24 q91 (q92 ◇ q92)))).symm).trans (apc98 ((q91 ◇ q91) ◇ q91) q92 q93)).trans (rfl))
  have apc105 : forall (q94 q95 q96 : G), (((q94 ◇ q94) ◇ q96) ◇ (q94 ◇ (q95 ◇ q95))) = (q95 ◇ q96) := by
    intro q94 q95 q96
    exact ((rfl).symm).trans ((((cg (fun t => ((q94 ◇ q94) ◇ q96) ◇ t) (apc98 q96 q94 (q95 ◇ q95))).symm).trans (apc98 ((q94 ◇ q94) ◇ q96) q95 q96)).trans (rfl))
  have apc106 : forall (q97 q98 q99 : G), (((q97 ◇ q97) ◇ (q99 ◇ (q98 ◇ q98))) ◇ q97) = (q98 ◇ q99) := by
    intro q97 q98 q99
    exact ((rfl).symm).trans ((((cg (fun t => ((q97 ◇ q97) ◇ (q99 ◇ (q98 ◇ q98))) ◇ t) ((h q97 q99 (q98 ◇ q98)).symm)).symm).trans (apc98 ((q97 ◇ q97) ◇ (q99 ◇ (q98 ◇ q98))) q98 q99)).trans (rfl))
  have apc107 : forall (q100 q101 : G), (q101 ◇ ((q100 ◇ q100) ◇ (q100 ◇ (q101 ◇ q100)))) = (q100 ◇ q100) := by
    intro q100 q101
    exact ((rfl).symm).trans ((((cg (fun t => q101 ◇ t) (apc101 q100 (q100 ◇ (q101 ◇ q100)))).symm).trans (apc90 q100 q100 q101)).trans (rfl))
  have apc108 : forall (q102 q103 : G), ((q102 ◇ (q103 ◇ q102)) ◇ (q102 ◇ q102)) = (q102 ◇ q103) := by
    intro q102 q103
    exact ((rfl).symm).trans ((((cg (fun t => (q102 ◇ (q103 ◇ q102)) ◇ t) (apc107 q102 q103)).symm).trans (apc98 (q102 ◇ (q103 ◇ q102)) q102 q103)).trans (rfl))
  have apc115 : forall (q104 q105 q106 : G), (q106 ◇ (q104 ◇ (q105 ◇ q105))) = (q105 ◇ (q104 ◇ (q106 ◇ q106))) := by
    intro q104 q105 q106
    exact (((rfl).symm).trans ((((cg (fun t => q105 ◇ t) (apc99 q105 q104 (q106 ◇ q106))).symm).trans (apc98 q105 q106 (q104 ◇ (q105 ◇ q105)))).trans (rfl))).symm
  have apc119 : forall (q107 q108 : G), (q107 ◇ ((q108 ◇ q108) ◇ (q108 ◇ q108))) = ((q107 ◇ q108) ◇ q108) := by
    intro q107 q108
    exact (((rfl).symm).trans ((((cg (fun t => t ◇ q108) (apc99 (q108 ◇ q108) q107 q108)).symm).trans (apc88 q108 (q107 ◇ ((q108 ◇ q108) ◇ (q108 ◇ q108))) q107 q107)).trans (rfl))).symm
  have apc121 : forall (q109 q110 : G), ((q109 ◇ q109) ◇ ((q110 ◇ q109) ◇ q109)) = (q109 ◇ q110) := by
    intro q109 q110
    exact ((rfl).symm).trans ((((cg (fun t => (q109 ◇ q109) ◇ t) (apc119 q110 q109)).symm).trans (apc98 (q109 ◇ q109) q109 q110)).trans (rfl))
  have apc122 : forall (q111 q112 : G), ((q111 ◇ q112) ◇ (q112 ◇ (q112 ◇ q111))) = q112 := by
    intro q111 q112
    exact ((rfl).symm).trans ((((cg (fun t => (q111 ◇ q112) ◇ t) (cg (fun t => q112 ◇ t) (apc121 q112 q111))).symm).trans ((h q112 (q111 ◇ q112) q112).symm)).trans (rfl))
  have apc127 : forall (q113 q114 q115 : G), (((q113 ◇ q114) ◇ q114) ◇ (q115 ◇ (q114 ◇ q113))) = (q114 ◇ q115) := by
    intro q113 q114 q115
    exact ((rfl).symm).trans ((((cg (fun t => ((q113 ◇ q114) ◇ q114) ◇ t) (cg (fun t => q115 ◇ t) (apc121 q114 q113))).symm).trans (apc98 ((q113 ◇ q114) ◇ q114) q114 q115)).trans (rfl))
  have apc129 : forall (q116 q117 q118 : G), ((((q116 ◇ q116) ◇ q116) ◇ q117) ◇ q118) = (q117 ◇ (q118 ◇ q117)) := by
    intro q116 q117 q118
    exact (((rfl).symm).trans ((((cg (fun t => t ◇ (q118 ◇ q117)) (apc78 q116 q117)).symm).trans (apc99 q117 (((q116 ◇ q116) ◇ q116) ◇ q117) q118)).trans (rfl))).symm
  have apc132 : forall (q107 q108 q40 q41 q42 : G), ((q42 ◇ (q40 ◇ q40)) ◇ (((q41 ◇ q40) ◇ q41) ◇ q41)) = q42 := by
    intro q107 q108 q40 q41 q42
    exact ((rfl).symm).trans ((((cg (fun t => (q42 ◇ (q40 ◇ q40)) ◇ t) (apc119 (q41 ◇ q40) q41)).symm).trans ((apc60 q40 q41 q42).trans (rfl))).trans (rfl))
  have apc133 : forall (q119 q120 : G), (q120 ◇ (((q120 ◇ q119) ◇ q120) ◇ ((q120 ◇ q119) ◇ q120))) = q119 := by
    intro q119 q120
    exact ((rfl).symm).trans ((((cg (fun t => q120 ◇ t) (apc132 q119 q119 q119 q120 (((q120 ◇ q119) ◇ q120) ◇ ((q120 ◇ q119) ◇ q120)))).symm).trans (apc100 ((q120 ◇ q119) ◇ q120) q119 q120)).trans (rfl))
  have apc134 : forall (q121 q122 q123 : G), (q121 ◇ (q123 ◇ ((q122 ◇ q121) ◇ q122))) = (q122 ◇ q123) := by
    intro q121 q122 q123
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (q123 ◇ ((q122 ◇ q121) ◇ q122))) (apc133 q121 q122)).symm).trans (apc99 ((q122 ◇ q121) ◇ q122) q122 q123)).trans (rfl))
  have apc143 : forall (q124 q125 : G), (q124 ◇ ((q124 ◇ q124) ◇ (q125 ◇ q125))) = ((q125 ◇ q124) ◇ q124) := by
    intro q124 q125
    exact (((rfl).symm).trans ((((apc119 q125 q124).symm).trans (apc115 (q124 ◇ q124) q124 q125)).trans (rfl))).symm
  have apc146 : forall (q126 q127 q128 : G), (((q127 ◇ q127) ◇ q128) ◇ q126) = (((q127 ◇ q127) ◇ q126) ◇ q128) := by
    intro q126 q127 q128
    exact ((rfl).symm).trans ((((cg (fun t => ((q127 ◇ q127) ◇ q128) ◇ t) (apc92 q127 q126)).symm).trans (apc105 q127 ((q127 ◇ q127) ◇ q126) q128)).trans (rfl))
  have apc151 : forall (q129 q130 q131 : G), (((q131 ◇ q129) ◇ q131) ◇ q131) = (((q130 ◇ q130) ◇ q129) ◇ q130) := by
    intro q129 q130 q131
    exact (((apc146 q129 q130 q130).symm).trans ((((cg (fun t => ((q130 ◇ q130) ◇ q130) ◇ t) (apc133 q129 q131)).symm).trans (apc103 q130 ((q131 ◇ q129) ◇ q131) q131)).trans (rfl))).symm
  have apc153 : forall (q132 q133 : G), ((((q133 ◇ q132) ◇ q133) ◇ q133) ◇ q133) = (q133 ◇ (q132 ◇ q133)) := by
    intro q132 q133
    exact ((rfl).symm).trans ((((cg (fun t => (((q133 ◇ q132) ◇ q133) ◇ q133) ◇ t) (apc122 q132 q133)).symm).trans (apc127 (q133 ◇ q132) q133 (q132 ◇ q133))).trans (rfl))
  have apc154 : forall (q134 q135 q136 : G), (q136 ◇ (q134 ◇ (q136 ◇ q136))) = (q135 ◇ (q134 ◇ (q136 ◇ q135))) := by
    intro q134 q135 q136
    exact (((rfl).symm).trans ((((cg (fun t => q135 ◇ t) (apc99 q136 q134 (q136 ◇ q135))).symm).trans (apc134 q135 q136 (q134 ◇ (q136 ◇ q136)))).trans (rfl))).symm
  have apc155 : forall (q129 q130 q131 : G), (((q131 ◇ q129) ◇ q131) ◇ q131) = (((q129 ◇ q129) ◇ q129) ◇ q129) := by
    intro q129 q130 q131
    exact ((rfl).symm).trans (((apc151 q129 q130 q131).trans ((apc151 q129 q130 q129).symm)).trans (rfl))
  have apc160 : forall (q134 q135 q136 : G), (q135 ◇ (q134 ◇ (q136 ◇ q135))) = (q134 ◇ (q134 ◇ (q136 ◇ q134))) := by
    intro q134 q135 q136
    exact ((rfl).symm).trans (((apc154 q134 q135 q136).symm.trans (apc154 q134 q134 q136)).trans (rfl))
  have apc162 : forall (q132 q133 q129 q130 q131 : G), (q133 ◇ (q132 ◇ q133)) = (q132 ◇ (q133 ◇ q132)) := by
    intro q132 q133 q129 q130 q131
    exact (((apc129 q132 q132 q133).symm).trans ((((cg (fun t => t ◇ q133) (apc155 q132 (((q133 ◇ q132) ◇ q133) ◇ q133) q133)).symm).trans ((apc153 q132 q133).trans (rfl))).trans (rfl))).symm
  have apc168 : forall (q137 q138 q139 : G), ((q138 ◇ q137) ◇ ((q139 ◇ q137) ◇ q137)) = (q138 ◇ q139) := by
    intro q137 q138 q139
    exact (((cg (fun t => (q138 ◇ q137) ◇ t) (apc115 (q137 ◇ q137) q137 q139)).trans (cg (fun t => (q138 ◇ q137) ◇ t) (apc143 q137 q139))).symm).trans ((((cg (fun t => (q138 ◇ q137) ◇ t) (cg (fun t => q139 ◇ t) (apc39 q137 q138))).symm).trans (apc98 (q138 ◇ q137) q138 q139)).trans (rfl))
  have apc177 : forall (q140 q141 q142 : G), ((q141 ◇ ((q142 ◇ q140) ◇ q140)) ◇ q140) = (q141 ◇ q142) := by
    intro q140 q141 q142
    exact (((cg (fun t => t ◇ q140) (cg (fun t => q141 ◇ t) (apc115 (q140 ◇ q140) q140 q142))).trans (cg (fun t => t ◇ q140) (cg (fun t => q141 ◇ t) (apc143 q140 q142)))).symm).trans ((((cg (fun t => t ◇ q140) (apc115 q142 q141 (q140 ◇ q140))).symm).trans (apc106 q140 q141 q142)).trans (rfl))
  have apc218 : forall (q143 q144 : G), (((q144 ◇ q144) ◇ (q144 ◇ q144)) ◇ q143) = (q143 ◇ (q143 ◇ (q144 ◇ q143))) := by
    intro q143 q144
    exact ((rfl).symm).trans ((((cg (fun t => ((q144 ◇ q144) ◇ (q144 ◇ q144)) ◇ t) (apc62 (q144 ◇ q144) q143)).symm).trans (apc98 ((q144 ◇ q144) ◇ (q144 ◇ q144)) q144 (q143 ◇ (q144 ◇ q144)))).trans (apc160 q143 q144 q144))
  have apc222 : forall (q145 q146 q147 : G), (q147 ◇ (q145 ◇ (q147 ◇ q145))) = (q146 ◇ (q147 ◇ (q145 ◇ q146))) := by
    intro q145 q146 q147
    exact (((rfl).symm).trans ((((cg (fun t => q146 ◇ t) (cg (fun t => q147 ◇ t) (cg (fun t => t ◇ q146) (apc68 q145 q145 q145)))).symm).trans (apc98 q146 ((q145 ◇ (q145 ◇ q145)) ◇ q145) q147)).trans (((cg (fun t => t ◇ q147) (apc101 q145 (q145 ◇ q145))).trans (apc218 q147 q145)).trans (cg (fun t => q147 ◇ t) (apc162 q145 q147 (q147 ◇ (q145 ◇ q147)) (q147 ◇ (q145 ◇ q147)) (q147 ◇ (q145 ◇ q147))))))).symm
  have apc247 : forall (q148 q149 q150 : G), ((q148 ◇ q150) ◇ q149) = ((q148 ◇ q149) ◇ q150) := by
    intro q148 q149 q150
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q149) (apc168 q149 q148 q150)).symm).trans (apc177 q149 (q148 ◇ q149) q150)).trans (rfl))
  have apc251 : forall (q151 q152 q153 : G), ((q152 ◇ q151) ◇ (q153 ◇ q152)) = ((q151 ◇ q153) ◇ (q152 ◇ q151)) := by
    intro q151 q152 q153
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (q153 ◇ q152)) (apc108 q152 q151)).symm).trans (apc99 q152 (q152 ◇ (q151 ◇ q152)) q153)).trans ((cg (fun t => t ◇ q153) (apc162 q151 q152 (q152 ◇ (q151 ◇ q152)) (q152 ◇ (q151 ◇ q152)) (q152 ◇ (q151 ◇ q152)))).trans (apc247 q151 q153 (q152 ◇ q151))))
  have apc252 : forall (q145 q146 q147 : G), (q146 ◇ (q147 ◇ (q145 ◇ q146))) = (q145 ◇ (q147 ◇ (q145 ◇ q145))) := by
    intro q145 q146 q147
    exact ((rfl).symm).trans (((apc222 q145 q146 q147).symm.trans (apc222 q145 q145 q147)).trans (rfl))
  have apc255 : forall (q154 q155 q156 : G), ((q154 ◇ q156) ◇ (q155 ◇ q154)) = ((q154 ◇ q155) ◇ (q156 ◇ q154)) := by
    intro q154 q155 q156
    exact (((apc251 q154 q156 q155).symm).trans ((((apc251 q156 q155 q154).symm).trans (apc247 q155 (q154 ◇ q155) q156)).trans ((cg (fun t => t ◇ q156) (apc162 q154 q155 (q155 ◇ (q154 ◇ q155)) (q155 ◇ (q154 ◇ q155)) (q155 ◇ (q154 ◇ q155)))).trans (apc247 q154 q156 (q155 ◇ q154))))).symm
  have apc270 : forall (q157 q158 : G), (q158 ◇ (q157 ◇ ((q157 ◇ q157) ◇ (q158 ◇ q157)))) = q157 := by
    intro q157 q158
    exact (((rfl).symm).trans ((((apc62 q158 q157).symm).trans (apc115 q158 q158 (q157 ◇ q158))).trans ((cg (fun t => q158 ◇ t) (apc252 q157 q158 (q157 ◇ q158))).trans (cg (fun t => q158 ◇ t) (cg (fun t => q157 ◇ t) (apc255 q157 q157 q158)))))).symm
  exact (calc
    x = x := rfl
    _ = (y ◇ (z ◇ ((x ◇ (x ◇ z)) ◇ y))) := ((((cg (fun t => y ◇ t) (cg (fun t => z ◇ t) (apc247 x y (x ◇ z)))).trans (cg (fun t => y ◇ t) (apc252 x z (x ◇ y)))).trans (cg (fun t => y ◇ t) (cg (fun t => x ◇ t) (apc255 x x y)))).trans (apc270 x y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_6960_to_7840 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_6960_to_7840
