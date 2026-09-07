-- Equation42483 → Equation42520
-- Recorded verdict: true
-- Premise: x ◇ x = y ◇ (x ◇ ((z ◇ y) ◇ y))
-- Conclusion: x ◇ x = y ◇ (y ◇ ((z ◇ y) ◇ y))
-- Original submission SHA-256: cb96822519f384344e4b76f541c49a455e46ce9bd3666f87e72f35dfa2ad1f63
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = y ◇ (x ◇ ((z ◇ y) ◇ y))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = y ◇ (y ◇ ((z ◇ y) ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   

def submission : Goal := by
  intro G _ h
  intro x y z
  have l0 : forall (x y : G), (x ◇ x) = (y ◇ y) := by
    intro x y
    have cg : ∀ (f : G → G) {a b : G}, a = b → f a = f b := by
      intro f a b p
      exact congrArg f p
    have apc2 : forall (q0 q1 q2 : G), (((q0 ◇ q1) ◇ q1) ◇ ((q2 ◇ ((q0 ◇ q1) ◇ q1)) ◇ (q2 ◇ ((q0 ◇ q1) ◇ q1)))) = (q1 ◇ q1) := by
      intro q0 q1 q2
      exact ((rfl).symm).trans ((((cg (fun t => ((q0 ◇ q1) ◇ q1) ◇ t) ((h (q2 ◇ ((q0 ◇ q1) ◇ q1)) q1 q0).symm)).symm).trans ((h q1 ((q0 ◇ q1) ◇ q1) q2).symm)).trans (rfl))
    have apc3 : forall (q3 q0 q1 q2 : G), ((q3 ◇ ((q0 ◇ q2) ◇ q2)) ◇ (q1 ◇ ((q3 ◇ q3) ◇ (q3 ◇ ((q0 ◇ q2) ◇ q2))))) = (q1 ◇ q1) := by
      intro q3 q0 q1 q2
      exact ((rfl).symm).trans ((((cg (fun t => (q3 ◇ ((q0 ◇ q2) ◇ q2)) ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => t ◇ (q3 ◇ ((q0 ◇ q2) ◇ q2))) ((h q3 q2 q0).symm)))).symm).trans ((h q1 (q3 ◇ ((q0 ◇ q2) ◇ q2)) q2).symm)).trans (rfl))
    have apc4 : forall (q4 q5 q6 : G), ((q4 ◇ ((q5 ◇ (q4 ◇ q4)) ◇ (q4 ◇ q4))) ◇ (q6 ◇ (q4 ◇ q4))) = (q6 ◇ q6) := by
      intro q4 q5 q6
      exact ((rfl).symm).trans ((((cg (fun t => (q4 ◇ ((q5 ◇ (q4 ◇ q4)) ◇ (q4 ◇ q4))) ◇ t) (cg (fun t => q6 ◇ t) ((h q4 (q4 ◇ q4) q5).symm))).symm).trans (apc3 q4 q5 q6 (q4 ◇ q4))).trans (rfl))
    have apc5 : forall (q7 q8 q9 : G), ((q8 ◇ (q7 ◇ q7)) ◇ (q9 ◇ ((q8 ◇ q8) ◇ (q8 ◇ (q7 ◇ q7))))) = (q9 ◇ q9) := by
      intro q7 q8 q9
      exact ((rfl).symm).trans ((((cg (fun t => (q8 ◇ (q7 ◇ q7)) ◇ t) (cg (fun t => q9 ◇ t) (cg (fun t => t ◇ (q8 ◇ (q7 ◇ q7))) (apc4 q7 q7 q8)))).symm).trans ((h q9 (q8 ◇ (q7 ◇ q7)) (q7 ◇ ((q7 ◇ (q7 ◇ q7)) ◇ (q7 ◇ q7)))).symm)).trans (rfl))
    have apc6 : forall (q10 q9 q11 : G), (((q10 ◇ (q11 ◇ q11)) ◇ (q11 ◇ q11)) ◇ (q9 ◇ ((q10 ◇ (q11 ◇ q11)) ◇ (q10 ◇ (q11 ◇ q11))))) = (q9 ◇ q9) := by
      intro q10 q9 q11
      exact ((rfl).symm).trans ((((cg (fun t => ((q10 ◇ (q11 ◇ q11)) ◇ (q11 ◇ q11)) ◇ t) (cg (fun t => q9 ◇ t) (apc4 q11 q10 (q10 ◇ (q11 ◇ q11))))).symm).trans ((h q9 ((q10 ◇ (q11 ◇ q11)) ◇ (q11 ◇ q11)) q11).symm)).trans (rfl))
    have apc7 : forall (q12 q13 : G), ((((q12 ◇ q13) ◇ q13) ◇ ((q12 ◇ q13) ◇ q13)) ◇ (q13 ◇ q13)) = (((q12 ◇ q13) ◇ q13) ◇ ((q12 ◇ q13) ◇ q13)) := by
      intro q12 q13
      exact ((rfl).symm).trans ((((cg (fun t => (((q12 ◇ q13) ◇ q13) ◇ ((q12 ◇ q13) ◇ q13)) ◇ t) (apc2 q12 q13 ((q12 ◇ q13) ◇ q13))).symm).trans (apc3 ((q12 ◇ q13) ◇ q13) q12 ((q12 ◇ q13) ◇ q13) q13)).trans (rfl))
    have apc8 : forall (q14 q15 q16 : G), ((q15 ◇ q15) ◇ (q16 ◇ (((q14 ◇ q15) ◇ q15) ◇ ((q14 ◇ q15) ◇ q15)))) = (q16 ◇ q16) := by
      intro q14 q15 q16
      exact ((cg (fun t => (q15 ◇ q15) ◇ t) (cg (fun t => q16 ◇ t) (apc7 q14 q15))).symm).trans ((((cg (fun t => (q15 ◇ q15) ◇ t) (cg (fun t => q16 ◇ t) (cg (fun t => t ◇ (q15 ◇ q15)) (apc7 q14 q15)))).symm).trans ((h q16 (q15 ◇ q15) (((q14 ◇ q15) ◇ q15) ◇ ((q14 ◇ q15) ◇ q15))).symm)).trans (rfl))
    have apc9 : forall (q17 q18 : G), ((q18 ◇ q18) ◇ (((q17 ◇ q18) ◇ q18) ◇ ((q17 ◇ q18) ◇ q18))) = (q18 ◇ q18) := by
      intro q17 q18
      exact ((rfl).symm).trans ((((cg (fun t => (q18 ◇ q18) ◇ t) ((h ((q17 ◇ q18) ◇ q18) q18 q17).symm)).symm).trans (apc8 q17 q18 q18)).trans (rfl))
    have apc10 : forall (q19 q20 q21 : G), ((q20 ◇ (((q19 ◇ q20) ◇ q20) ◇ ((q19 ◇ q20) ◇ q20))) ◇ (q21 ◇ (q20 ◇ q20))) = (q21 ◇ q21) := by
      intro q19 q20 q21
      exact ((rfl).symm).trans ((((cg (fun t => (q20 ◇ (((q19 ◇ q20) ◇ q20) ◇ ((q19 ◇ q20) ◇ q20))) ◇ t) (cg (fun t => q21 ◇ t) (apc8 q19 q20 q20))).symm).trans (apc5 ((q19 ◇ q20) ◇ q20) q20 q21)).trans (rfl))
    have apc11 : forall (q22 q23 q24 : G), ((((q22 ◇ q23) ◇ q23) ◇ ((q22 ◇ q23) ◇ q23)) ◇ (q24 ◇ (q23 ◇ q23))) = (q24 ◇ q24) := by
      intro q22 q23 q24
      exact ((rfl).symm).trans ((((cg (fun t => t ◇ (q24 ◇ (q23 ◇ q23))) ((h ((q22 ◇ q23) ◇ q23) q23 q22).symm)).symm).trans (apc10 q22 q23 q24)).trans (rfl))
    have apc12 : forall (q25 q26 q27 : G), ((((q25 ◇ q26) ◇ q26) ◇ (q26 ◇ q26)) ◇ (q27 ◇ (((q25 ◇ q26) ◇ q26) ◇ ((q25 ◇ q26) ◇ q26)))) = (q27 ◇ q27) := by
      intro q25 q26 q27
      exact ((rfl).symm).trans ((((cg (fun t => (((q25 ◇ q26) ◇ q26) ◇ (q26 ◇ q26)) ◇ t) (cg (fun t => q27 ◇ t) (apc11 q25 q26 ((q25 ◇ q26) ◇ q26)))).symm).trans (apc5 q26 ((q25 ◇ q26) ◇ q26) q27)).trans (rfl))
    have apc13 : forall (q28 q29 : G), ((((q28 ◇ q29) ◇ q29) ◇ (q29 ◇ q29)) ◇ (q29 ◇ q29)) = ((q29 ◇ q29) ◇ (q29 ◇ q29)) := by
      intro q28 q29
      exact ((rfl).symm).trans ((((cg (fun t => (((q28 ◇ q29) ◇ q29) ◇ (q29 ◇ q29)) ◇ t) (apc9 q28 q29)).symm).trans (apc12 q28 q29 (q29 ◇ q29))).trans (rfl))
    have apc14 : forall (q30 q31 : G), ((q30 ◇ q30) ◇ (q31 ◇ ((q30 ◇ q30) ◇ (q30 ◇ q30)))) = (q31 ◇ q31) := by
      intro q30 q31
      exact ((rfl).symm).trans ((((cg (fun t => (q30 ◇ q30) ◇ t) (cg (fun t => q31 ◇ t) (apc13 q30 q30))).symm).trans ((h q31 (q30 ◇ q30) ((q30 ◇ q30) ◇ q30)).symm)).trans (rfl))
    have apc15 : forall (q32 q33 : G), ((q32 ◇ ((q32 ◇ q32) ◇ (q32 ◇ q32))) ◇ (q33 ◇ (q32 ◇ q32))) = (q33 ◇ q33) := by
      intro q32 q33
      exact ((rfl).symm).trans ((((cg (fun t => t ◇ (q33 ◇ (q32 ◇ q32))) (cg (fun t => q32 ◇ t) (apc13 q32 q32))).symm).trans (apc4 q32 ((q32 ◇ q32) ◇ q32) q33)).trans (rfl))
    have apc17 : forall (q34 q35 : G), (((q35 ◇ q35) ◇ (q35 ◇ q35)) ◇ (q34 ◇ ((q35 ◇ q35) ◇ (q35 ◇ q35)))) = (q34 ◇ q34) := by
      intro q34 q35
      exact ((rfl).symm).trans ((((cg (fun t => ((q35 ◇ q35) ◇ (q35 ◇ q35)) ◇ t) (cg (fun t => q34 ◇ t) (apc15 q35 (q35 ◇ q35)))).symm).trans ((h q34 ((q35 ◇ q35) ◇ (q35 ◇ q35)) q35).symm)).trans (rfl))
    have apc22 : forall (q36 : G), (((q36 ◇ q36) ◇ (q36 ◇ q36)) ◇ ((q36 ◇ q36) ◇ (q36 ◇ q36))) = ((q36 ◇ q36) ◇ (q36 ◇ q36)) := by
      intro q36
      exact ((apc17 ((q36 ◇ q36) ◇ (q36 ◇ q36)) q36).symm).trans ((((cg (fun t => ((q36 ◇ q36) ◇ (q36 ◇ q36)) ◇ t) (apc14 q36 ((q36 ◇ q36) ◇ (q36 ◇ q36)))).symm).trans (apc14 (q36 ◇ q36) (q36 ◇ q36))).trans (rfl))
    have apc25 : forall (q37 : G), ((q37 ◇ q37) ◇ ((q37 ◇ q37) ◇ (q37 ◇ q37))) = ((q37 ◇ q37) ◇ (q37 ◇ q37)) := by
      intro q37
      exact ((rfl).symm).trans ((((cg (fun t => (q37 ◇ q37) ◇ t) (apc22 q37)).symm).trans (apc14 q37 ((q37 ◇ q37) ◇ (q37 ◇ q37)))).trans (apc22 q37))
    have apc35 : forall (q38 q39 : G), (((q38 ◇ (q39 ◇ q39)) ◇ (q38 ◇ (q39 ◇ q39))) ◇ ((q38 ◇ (q39 ◇ q39)) ◇ (q38 ◇ (q39 ◇ q39)))) = ((q39 ◇ q39) ◇ (q39 ◇ q39)) := by
      intro q38 q39
      exact ((apc6 q38 ((q38 ◇ (q39 ◇ q39)) ◇ (q38 ◇ (q39 ◇ q39))) q39).symm).trans ((((cg (fun t => ((q38 ◇ (q39 ◇ q39)) ◇ (q39 ◇ q39)) ◇ t) ((h ((q38 ◇ (q39 ◇ q39)) ◇ (q38 ◇ (q39 ◇ q39))) (q39 ◇ q39) q38).symm)).symm).trans (apc5 q39 (q38 ◇ (q39 ◇ q39)) (q39 ◇ q39))).trans (rfl))
    have apc42 : forall (q40 q41 : G), ((((q40 ◇ q41) ◇ q41) ◇ ((q40 ◇ q41) ◇ q41)) ◇ (((q40 ◇ q41) ◇ q41) ◇ ((q40 ◇ q41) ◇ q41))) = ((q41 ◇ q41) ◇ (q41 ◇ q41)) := by
      intro q40 q41
      exact (((apc25 q41).symm).trans ((((cg (fun t => (q41 ◇ q41) ◇ t) (apc11 q40 q41 (q41 ◇ q41))).symm).trans (apc14 q41 (((q40 ◇ q41) ◇ q41) ◇ ((q40 ◇ q41) ◇ q41)))).trans (rfl))).symm
    have apc43 : forall (q42 q43 : G), (((q42 ◇ q43) ◇ q43) ◇ ((q43 ◇ q43) ◇ (q43 ◇ q43))) = (q43 ◇ q43) := by
      intro q42 q43
      exact ((rfl).symm).trans ((((cg (fun t => ((q42 ◇ q43) ◇ q43) ◇ t) (apc42 q42 q43)).symm).trans (apc2 q42 q43 ((q42 ◇ q43) ◇ q43))).trans (rfl))
    have apc44 : forall (q44 q45 : G), (((q44 ◇ q45) ◇ q45) ◇ ((q44 ◇ q45) ◇ q45)) = ((q45 ◇ q45) ◇ (q45 ◇ q45)) := by
      intro q44 q45
      exact (((rfl).symm).trans ((((cg (fun t => (q45 ◇ q45) ◇ t) (apc43 q44 q45)).symm).trans (apc14 q45 ((q44 ◇ q45) ◇ q45))).trans (rfl))).symm
    have apc45 : forall (q17 q18 q44 q45 : G), ((q18 ◇ q18) ◇ (q18 ◇ q18)) = (q18 ◇ q18) := by
      intro q17 q18 q44 q45
      exact ((apc25 q18).symm).trans ((((cg (fun t => (q18 ◇ q18) ◇ t) (apc44 q17 q18)).symm).trans ((apc9 q17 q18).trans (rfl))).trans (rfl))
    have apc46 : forall (q17 q18 q30 q31 q44 q45 : G), ((q30 ◇ q30) ◇ (q31 ◇ (q30 ◇ q30))) = (q31 ◇ q31) := by
      intro q17 q18 q30 q31 q44 q45
      exact ((rfl).symm).trans ((((cg (fun t => (q30 ◇ q30) ◇ t) (cg (fun t => q31 ◇ t) (apc45 ((q30 ◇ q30) ◇ (q30 ◇ q30)) q30 ((q30 ◇ q30) ◇ (q30 ◇ q30)) ((q30 ◇ q30) ◇ (q30 ◇ q30))))).symm).trans ((apc14 q30 q31).trans (rfl))).trans (rfl))
    have apc49 : forall (q38 q39 q17 q18 q44 q45 : G), ((q38 ◇ (q39 ◇ q39)) ◇ (q38 ◇ (q39 ◇ q39))) = (q39 ◇ q39) := by
      intro q38 q39 q17 q18 q44 q45
      exact ((rfl).symm).trans ((((apc45 (((q38 ◇ (q39 ◇ q39)) ◇ (q38 ◇ (q39 ◇ q39))) ◇ ((q38 ◇ (q39 ◇ q39)) ◇ (q38 ◇ (q39 ◇ q39)))) (q38 ◇ (q39 ◇ q39)) (((q38 ◇ (q39 ◇ q39)) ◇ (q38 ◇ (q39 ◇ q39))) ◇ ((q38 ◇ (q39 ◇ q39)) ◇ (q38 ◇ (q39 ◇ q39)))) (((q38 ◇ (q39 ◇ q39)) ◇ (q38 ◇ (q39 ◇ q39))) ◇ ((q38 ◇ (q39 ◇ q39)) ◇ (q38 ◇ (q39 ◇ q39))))).symm).trans ((apc35 q38 q39).trans (apc45 ((q39 ◇ q39) ◇ (q39 ◇ q39)) q39 ((q39 ◇ q39) ◇ (q39 ◇ q39)) ((q39 ◇ q39) ◇ (q39 ◇ q39))))).trans (rfl))
    have apc50 : forall (q46 q47 q48 : G), (((q46 ◇ q47) ◇ q47) ◇ ((q46 ◇ q47) ◇ q47)) = (q47 ◇ q47) := by
      intro q46 q47 q48
      exact ((((cg (fun t => (q47 ◇ q47) ◇ t) (apc49 q48 q47 ((q48 ◇ (q47 ◇ q47)) ◇ (q48 ◇ (q47 ◇ q47))) ((q48 ◇ (q47 ◇ q47)) ◇ (q48 ◇ (q47 ◇ q47))) ((q48 ◇ (q47 ◇ q47)) ◇ (q48 ◇ (q47 ◇ q47))) ((q48 ◇ (q47 ◇ q47)) ◇ (q48 ◇ (q47 ◇ q47))))).trans (apc45 ((q47 ◇ q47) ◇ (q47 ◇ q47)) q47 ((q47 ◇ q47) ◇ (q47 ◇ q47)) ((q47 ◇ q47) ◇ (q47 ◇ q47)))).symm).trans ((((cg (fun t => (q47 ◇ q47) ◇ t) (apc11 q46 q47 (q48 ◇ (q47 ◇ q47)))).symm).trans ((h (((q46 ◇ q47) ◇ q47) ◇ ((q46 ◇ q47) ◇ q47)) (q47 ◇ q47) q48).symm)).trans (apc45 ((((q46 ◇ q47) ◇ q47) ◇ ((q46 ◇ q47) ◇ q47)) ◇ (((q46 ◇ q47) ◇ q47) ◇ ((q46 ◇ q47) ◇ q47))) ((q46 ◇ q47) ◇ q47) ((((q46 ◇ q47) ◇ q47) ◇ ((q46 ◇ q47) ◇ q47)) ◇ (((q46 ◇ q47) ◇ q47) ◇ ((q46 ◇ q47) ◇ q47))) ((((q46 ◇ q47) ◇ q47) ◇ ((q46 ◇ q47) ◇ q47)) ◇ (((q46 ◇ q47) ◇ q47) ◇ ((q46 ◇ q47) ◇ q47)))))).symm
    have apc52 : forall (q49 q50 : G), (q49 ◇ (q49 ◇ q49)) = (q49 ◇ q49) := by
      intro q49 q50
      exact ((rfl).symm).trans ((((cg (fun t => q49 ◇ t) (apc50 q50 q49 q49)).symm).trans ((h ((q50 ◇ q49) ◇ q49) q49 q50).symm)).trans (apc50 q50 q49 (((q50 ◇ q49) ◇ q49) ◇ ((q50 ◇ q49) ◇ q49))))
    have apc56 : forall (q51 q52 q53 : G), ((q51 ◇ (q52 ◇ q52)) ◇ (q53 ◇ (q51 ◇ q51))) = (q53 ◇ q53) := by
      intro q51 q52 q53
      exact ((cg (fun t => (q51 ◇ (q52 ◇ q52)) ◇ t) (cg (fun t => q53 ◇ t) (apc46 ((q52 ◇ q52) ◇ (q51 ◇ (q52 ◇ q52))) ((q52 ◇ q52) ◇ (q51 ◇ (q52 ◇ q52))) q52 q51 ((q52 ◇ q52) ◇ (q51 ◇ (q52 ◇ q52))) ((q52 ◇ q52) ◇ (q51 ◇ (q52 ◇ q52)))))).symm).trans ((((cg (fun t => (q51 ◇ (q52 ◇ q52)) ◇ t) (cg (fun t => q53 ◇ t) (cg (fun t => t ◇ (q51 ◇ (q52 ◇ q52))) (apc49 q51 q52 q51 q51 q51 q51)))).symm).trans ((h q53 (q51 ◇ (q52 ◇ q52)) (q51 ◇ (q52 ◇ q52))).symm)).trans (rfl))
    have apc57 : forall (q54 q55 : G), ((q54 ◇ (q55 ◇ q55)) ◇ (q54 ◇ q54)) = (q54 ◇ q54) := by
      intro q54 q55
      exact ((rfl).symm).trans ((((cg (fun t => (q54 ◇ (q55 ◇ q55)) ◇ t) (apc52 q54 q54)).symm).trans (apc56 q54 q55 q54)).trans (rfl))
    have apc63 : forall (q56 q57 q58 q59 : G), (((q56 ◇ (q57 ◇ q57)) ◇ (q58 ◇ q58)) ◇ (q59 ◇ (q57 ◇ q57))) = (q59 ◇ q59) := by
      intro q56 q57 q58 q59
      exact ((rfl).symm).trans ((((cg (fun t => ((q56 ◇ (q57 ◇ q57)) ◇ (q58 ◇ q58)) ◇ t) (cg (fun t => q59 ◇ t) (apc49 q56 q57 q56 q56 q56 q56))).symm).trans (apc56 (q56 ◇ (q57 ◇ q57)) q58 q59)).trans (rfl))
    have apc64 : forall (q60 q61 q62 : G), ((q61 ◇ q61) ◇ (q62 ◇ (q60 ◇ q60))) = (q62 ◇ q62) := by
      intro q60 q61 q62
      exact ((rfl).symm).trans ((((cg (fun t => t ◇ (q62 ◇ (q60 ◇ q60))) (apc57 q61 q60)).symm).trans (apc63 q61 q60 q61 q62)).trans (rfl))
    have apc65 : forall (q63 q64 : G), ((q64 ◇ q64) ◇ (q63 ◇ q63)) = (q63 ◇ q63) := by
      intro q63 q64
      exact ((rfl).symm).trans ((((cg (fun t => (q64 ◇ q64) ◇ t) (apc52 q63 q63)).symm).trans (apc64 q63 q64 q63)).trans (rfl))
    have apc67 : forall (q65 q66 q67 : G), (q66 ◇ q66) = (q65 ◇ q65) := by
      intro q65 q66 q67
      exact ((apc65 q66 q67).symm).trans ((((cg (fun t => (q67 ◇ q67) ◇ t) (apc65 q66 q65)).symm).trans (apc64 q66 q67 (q65 ◇ q65))).trans (apc65 q65 q65))
    exact (apc67 (x ◇ x) x (x ◇ x)).trans ((apc67 (x ◇ x) y (x ◇ x)).symm)
  have reduced_goal : (x ◇ x) = (x ◇ x) := by
    rfl
  exact (calc
    (x ◇ x) = (x ◇ x) := rfl
    _ = (x ◇ x) := reduced_goal
    _ = (y ◇ (y ◇ ((z ◇ y) ◇ y))) := (((h y y z).symm).trans ((l0 x y).symm)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_42483_to_42520 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_42483_to_42520
