-- Equation40706 → Equation40686
-- Recorded verdict: true
-- Premise: x = ((((x ◇ y) ◇ x) ◇ x) ◇ x) ◇ z
-- Conclusion: x = ((((x ◇ x) ◇ y) ◇ y) ◇ z) ◇ w
-- Original submission SHA-256: ea976ef8aff2cbf28d13cc35757a8944720cfcc08e991261d144c35acf0b723e
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((((x ◇ y) ◇ x) ◇ x) ◇ x) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = ((((x ◇ x) ◇ y) ◇ y) ◇ z) ◇ w
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   

def submission : Goal := by
  intro G _ h
  intro x y z w
  have cg : ∀ (f : G → G) {a b : G}, a = b → f a = f b := by
    intro f a b p
    exact congrArg f p
  have apc1 : forall (q0 q1 q2 : G), (((q1 ◇ (((q1 ◇ q0) ◇ q1) ◇ q1)) ◇ (((q1 ◇ q0) ◇ q1) ◇ q1)) ◇ q2) = (((q1 ◇ q0) ◇ q1) ◇ q1) := by
    intro q0 q1 q2
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q2) (cg (fun t => t ◇ (((q1 ◇ q0) ◇ q1) ◇ q1)) (cg (fun t => t ◇ (((q1 ◇ q0) ◇ q1) ◇ q1)) ((h q1 q0 (((q1 ◇ q0) ◇ q1) ◇ q1)).symm)))).symm).trans ((h (((q1 ◇ q0) ◇ q1) ◇ q1) q1 q2).symm)).trans (rfl))
  have apc3 : forall (q3 q0 q2 : G), ((((q3 ◇ ((((q3 ◇ q0) ◇ q3) ◇ q3) ◇ q3)) ◇ ((((q3 ◇ q0) ◇ q3) ◇ q3) ◇ q3)) ◇ ((((q3 ◇ q0) ◇ q3) ◇ q3) ◇ q3)) ◇ q2) = ((((q3 ◇ q0) ◇ q3) ◇ q3) ◇ q3) := by
    intro q3 q0 q2
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q2) (cg (fun t => t ◇ ((((q3 ◇ q0) ◇ q3) ◇ q3) ◇ q3)) (cg (fun t => t ◇ ((((q3 ◇ q0) ◇ q3) ◇ q3) ◇ q3)) (cg (fun t => t ◇ ((((q3 ◇ q0) ◇ q3) ◇ q3) ◇ q3)) ((h q3 q0 q3).symm))))).symm).trans ((h ((((q3 ◇ q0) ◇ q3) ◇ q3) ◇ q3) q3 q2).symm)).trans (rfl))
  have apc5 : forall (q4 q5 q6 q7 : G), ((q4 ◇ (((((((q4 ◇ q5) ◇ q4) ◇ q4) ◇ q4) ◇ q6) ◇ ((((q4 ◇ q5) ◇ q4) ◇ q4) ◇ q4)) ◇ ((((q4 ◇ q5) ◇ q4) ◇ q4) ◇ q4))) ◇ q7) = (((((((q4 ◇ q5) ◇ q4) ◇ q4) ◇ q4) ◇ q6) ◇ ((((q4 ◇ q5) ◇ q4) ◇ q4) ◇ q4)) ◇ ((((q4 ◇ q5) ◇ q4) ◇ q4) ◇ q4)) := by
    intro q4 q5 q6 q7
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q7) (cg (fun t => t ◇ (((((((q4 ◇ q5) ◇ q4) ◇ q4) ◇ q4) ◇ q6) ◇ ((((q4 ◇ q5) ◇ q4) ◇ q4) ◇ q4)) ◇ ((((q4 ◇ q5) ◇ q4) ◇ q4) ◇ q4))) ((h q4 q5 (((((((q4 ◇ q5) ◇ q4) ◇ q4) ◇ q4) ◇ q6) ◇ ((((q4 ◇ q5) ◇ q4) ◇ q4) ◇ q4)) ◇ ((((q4 ◇ q5) ◇ q4) ◇ q4) ◇ q4))).symm))).symm).trans (apc1 q6 ((((q4 ◇ q5) ◇ q4) ◇ q4) ◇ q4) q7)).trans (rfl))
  have apc6 : forall (q8 q9 q10 q11 : G), (((((((q8 ◇ q9) ◇ q8) ◇ q8) ◇ q8) ◇ q10) ◇ ((((q8 ◇ q9) ◇ q8) ◇ q8) ◇ q8)) ◇ ((((q8 ◇ q9) ◇ q8) ◇ q8) ◇ q8)) = ((q8 ◇ ((q8 ◇ ((((q8 ◇ q9) ◇ q8) ◇ q8) ◇ q8)) ◇ ((((q8 ◇ q9) ◇ q8) ◇ q8) ◇ q8))) ◇ q11) := by
    intro q8 q9 q10 q11
    exact (((rfl).symm).trans ((((cg (fun t => t ◇ q11) (cg (fun t => q8 ◇ t) (cg (fun t => t ◇ ((((q8 ◇ q9) ◇ q8) ◇ q8) ◇ q8)) (cg (fun t => t ◇ ((((q8 ◇ q9) ◇ q8) ◇ q8) ◇ q8)) ((h q8 q9 q10).symm))))).symm).trans (apc5 q8 q9 q10 q11)).trans (rfl))).symm
  have apc7 : forall (q12 q13 q14 q15 : G), (((((((q13 ◇ q14) ◇ q13) ◇ q13) ◇ q13) ◇ q15) ◇ ((((q13 ◇ q14) ◇ q13) ◇ q13) ◇ q13)) ◇ ((((q13 ◇ q14) ◇ q13) ◇ q13) ◇ q13)) = (((((((q13 ◇ q14) ◇ q13) ◇ q13) ◇ q13) ◇ q12) ◇ ((((q13 ◇ q14) ◇ q13) ◇ q13) ◇ q13)) ◇ ((((q13 ◇ q14) ◇ q13) ◇ q13) ◇ q13)) := by
    intro q12 q13 q14 q15
    exact (((rfl).symm).trans (((((apc6 q13 q14 q12 q12).symm).symm).trans ((apc6 q13 q14 q15 q12).symm)).trans (rfl))).symm
  have apc8 : forall (q16 q17 q18 : G), (((((((q17 ◇ q18) ◇ q17) ◇ q17) ◇ q17) ◇ q16) ◇ ((((q17 ◇ q18) ◇ q17) ◇ q17) ◇ q17)) ◇ ((((q17 ◇ q18) ◇ q17) ◇ q17) ◇ q17)) = ((q17 ◇ ((((q17 ◇ q18) ◇ q17) ◇ q17) ◇ q17)) ◇ ((((q17 ◇ q18) ◇ q17) ◇ q17) ◇ q17)) := by
    intro q16 q17 q18
    exact (((rfl).symm).trans ((((cg (fun t => t ◇ ((((q17 ◇ q18) ◇ q17) ◇ q17) ◇ q17)) (cg (fun t => t ◇ ((((q17 ◇ q18) ◇ q17) ◇ q17) ◇ q17)) ((h q17 q18 q16).symm))).symm).trans (apc7 q16 q17 q18 q16)).trans (rfl))).symm
  have apc9 : forall (q4 q5 q6 q7 : G), ((q4 ◇ ((q4 ◇ ((((q4 ◇ q5) ◇ q4) ◇ q4) ◇ q4)) ◇ ((((q4 ◇ q5) ◇ q4) ◇ q4) ◇ q4))) ◇ q7) = ((q4 ◇ ((q4 ◇ ((((q4 ◇ q5) ◇ q4) ◇ q4) ◇ q4)) ◇ ((((q4 ◇ q5) ◇ q4) ◇ q4) ◇ q4))) ◇ q4) := by
    intro q4 q5 q6 q7
    exact ((cg (fun t => t ◇ q7) (cg (fun t => q4 ◇ t) (apc8 q6 q4 q5))).symm).trans (((apc5 q4 q5 q6 q7).trans ((apc5 q4 q5 q6 q4).symm)).trans (cg (fun t => t ◇ q4) (cg (fun t => q4 ◇ t) (apc8 q6 q4 q5))))
  have apc10 : forall (q19 q20 q21 q22 : G), (((((q21 ◇ ((((q21 ◇ q19) ◇ q21) ◇ q21) ◇ q21)) ◇ ((((q21 ◇ q19) ◇ q21) ◇ q21) ◇ q21)) ◇ q21) ◇ q21) ◇ q22) = q21 := by
    intro q19 q20 q21 q22
    exact ((cg (fun t => t ◇ q22) (cg (fun t => t ◇ q21) (cg (fun t => t ◇ q21) (apc8 q20 q21 q19)))).symm).trans ((((cg (fun t => t ◇ q22) (cg (fun t => t ◇ q21) (cg (fun t => t ◇ q21) (apc5 q21 q19 q20 q21)))).symm).trans ((h q21 (((((((q21 ◇ q19) ◇ q21) ◇ q21) ◇ q21) ◇ q20) ◇ ((((q21 ◇ q19) ◇ q21) ◇ q21) ◇ q21)) ◇ ((((q21 ◇ q19) ◇ q21) ◇ q21) ◇ q21)) q22).symm)).trans (rfl))
  have apc12 : forall (q23 q24 q25 : G), ((q23 ◇ ((q23 ◇ ((((q23 ◇ q24) ◇ q23) ◇ q23) ◇ q23)) ◇ ((((q23 ◇ q24) ◇ q23) ◇ q23) ◇ q23))) ◇ q23) = ((q23 ◇ ((((q23 ◇ q24) ◇ q23) ◇ q23) ◇ q23)) ◇ ((((q23 ◇ q24) ◇ q23) ◇ q23) ◇ q23)) := by
    intro q23 q24 q25
    exact (((rfl).symm).trans ((((cg (fun t => t ◇ ((((q23 ◇ q24) ◇ q23) ◇ q23) ◇ q23)) (cg (fun t => t ◇ ((((q23 ◇ q24) ◇ q23) ◇ q23) ◇ q23)) ((h q23 q24 q23).symm))).symm).trans (apc6 q23 q24 q23 q25)).trans (apc9 q23 q24 ((q23 ◇ ((q23 ◇ ((((q23 ◇ q24) ◇ q23) ◇ q23) ◇ q23)) ◇ ((((q23 ◇ q24) ◇ q23) ◇ q23) ◇ q23))) ◇ q25) q25))).symm
  have apc13 : forall (q26 q27 q28 q29 : G), ((((q26 ◇ ((q26 ◇ ((((q26 ◇ q27) ◇ q26) ◇ q26) ◇ q26)) ◇ ((((q26 ◇ q27) ◇ q26) ◇ q26) ◇ q26))) ◇ q28) ◇ ((((q26 ◇ q27) ◇ q26) ◇ q26) ◇ q26)) ◇ q29) = ((((q26 ◇ q27) ◇ q26) ◇ q26) ◇ q26) := by
    intro q26 q27 q28 q29
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q29) (cg (fun t => t ◇ ((((q26 ◇ q27) ◇ q26) ◇ q26) ◇ q26)) (apc6 q26 q27 q26 q28))).symm).trans ((h ((((q26 ◇ q27) ◇ q26) ◇ q26) ◇ q26) q26 q29).symm)).trans (rfl))
  have apc17 : forall (q4 q5 q7 q6 : G), ((q4 ◇ ((q4 ◇ ((((q4 ◇ q5) ◇ q4) ◇ q4) ◇ q4)) ◇ ((((q4 ◇ q5) ◇ q4) ◇ q4) ◇ q4))) ◇ q7) = ((q4 ◇ ((((q4 ◇ q5) ◇ q4) ◇ q4) ◇ q4)) ◇ ((((q4 ◇ q5) ◇ q4) ◇ q4) ◇ q4)) := by
    intro q4 q5 q7 q6
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc9 q4 q5 q6 q7).trans (apc12 q4 q5 ((q4 ◇ ((q4 ◇ ((((q4 ◇ q5) ◇ q4) ◇ q4) ◇ q4)) ◇ ((((q4 ◇ q5) ◇ q4) ◇ q4) ◇ q4))) ◇ q4)))).trans (rfl))
  have apc18 : forall (q30 q31 q32 q33 q34 : G), (((q30 ◇ q33) ◇ (((q30 ◇ ((((q30 ◇ q31) ◇ q30) ◇ q30) ◇ q30)) ◇ ((((q30 ◇ q31) ◇ q30) ◇ q30) ◇ q30)) ◇ ((((q30 ◇ q31) ◇ q30) ◇ q30) ◇ q30))) ◇ q34) = (((q30 ◇ ((((q30 ◇ q31) ◇ q30) ◇ q30) ◇ q30)) ◇ ((((q30 ◇ q31) ◇ q30) ◇ q30) ◇ q30)) ◇ ((((q30 ◇ q31) ◇ q30) ◇ q30) ◇ q30)) := by
    intro q30 q31 q32 q33 q34
    exact ((cg (fun t => t ◇ q34) (cg (fun t => (q30 ◇ q33) ◇ t) (cg (fun t => t ◇ ((((q30 ◇ q31) ◇ q30) ◇ q30) ◇ q30)) (apc8 q32 q30 q31)))).symm).trans ((((cg (fun t => t ◇ q34) (cg (fun t => t ◇ ((((((((q30 ◇ q31) ◇ q30) ◇ q30) ◇ q30) ◇ q32) ◇ ((((q30 ◇ q31) ◇ q30) ◇ q30) ◇ q30)) ◇ ((((q30 ◇ q31) ◇ q30) ◇ q30) ◇ q30)) ◇ ((((q30 ◇ q31) ◇ q30) ◇ q30) ◇ q30))) (cg (fun t => t ◇ q33) ((h q30 q31 ((((((q30 ◇ q31) ◇ q30) ◇ q30) ◇ q30) ◇ ((((((((q30 ◇ q31) ◇ q30) ◇ q30) ◇ q30) ◇ q32) ◇ ((((q30 ◇ q31) ◇ q30) ◇ q30) ◇ q30)) ◇ ((((q30 ◇ q31) ◇ q30) ◇ q30) ◇ q30)) ◇ ((((q30 ◇ q31) ◇ q30) ◇ q30) ◇ q30))) ◇ ((((((((q30 ◇ q31) ◇ q30) ◇ q30) ◇ q30) ◇ q32) ◇ ((((q30 ◇ q31) ◇ q30) ◇ q30) ◇ q30)) ◇ ((((q30 ◇ q31) ◇ q30) ◇ q30) ◇ q30)) ◇ ((((q30 ◇ q31) ◇ q30) ◇ q30) ◇ q30)))).symm)))).symm).trans (apc13 ((((q30 ◇ q31) ◇ q30) ◇ q30) ◇ q30) q32 q33 q34)).trans (cg (fun t => t ◇ ((((q30 ◇ q31) ◇ q30) ◇ q30) ◇ q30)) (apc8 q32 q30 q31)))
  have apc19 : forall (q35 q36 q37 q38 : G), (((q36 ◇ ((((q36 ◇ q37) ◇ q36) ◇ q36) ◇ q36)) ◇ ((((q36 ◇ q37) ◇ q36) ◇ q36) ◇ q36)) ◇ ((((q36 ◇ q37) ◇ q36) ◇ q36) ◇ q36)) = (((q36 ◇ ((((q36 ◇ q35) ◇ q36) ◇ q36) ◇ q36)) ◇ ((((q36 ◇ q35) ◇ q36) ◇ q36) ◇ q36)) ◇ q38) := by
    intro q35 q36 q37 q38
    exact (((rfl).symm).trans ((((cg (fun t => t ◇ q38) (apc17 q36 q35 (((q36 ◇ ((((q36 ◇ q37) ◇ q36) ◇ q36) ◇ q36)) ◇ ((((q36 ◇ q37) ◇ q36) ◇ q36) ◇ q36)) ◇ ((((q36 ◇ q37) ◇ q36) ◇ q36) ◇ q36)) q35)).symm).trans (apc18 q36 q37 q35 ((q36 ◇ ((((q36 ◇ q35) ◇ q36) ◇ q36) ◇ q36)) ◇ ((((q36 ◇ q35) ◇ q36) ◇ q36) ◇ q36)) q38)).trans (rfl))).symm
  have apc20 : forall (q39 q40 q41 q42 q43 : G), (((q42 ◇ ((((q42 ◇ q41) ◇ q42) ◇ q42) ◇ q42)) ◇ ((((q42 ◇ q41) ◇ q42) ◇ q42) ◇ q42)) ◇ q43) = (((q42 ◇ ((((q42 ◇ q39) ◇ q42) ◇ q42) ◇ q42)) ◇ ((((q42 ◇ q39) ◇ q42) ◇ q42) ◇ q42)) ◇ q40) := by
    intro q39 q40 q41 q42 q43
    exact (((rfl).symm).trans ((((apc19 q39 q42 q39 q40).symm).trans (apc19 q41 q42 q39 q43)).trans (rfl))).symm
  have apc21 : forall (q44 q45 q46 q47 : G), ((((((q44 ◇ q45) ◇ q44) ◇ q44) ◇ q44) ◇ (q44 ◇ q46)) ◇ q47) = (q44 ◇ q46) := by
    intro q44 q45 q46 q47
    exact ((cg (fun t => t ◇ q47) (cg (fun t => t ◇ (q44 ◇ q46)) (apc3 q44 q45 (q44 ◇ q46)))).symm).trans ((((cg (fun t => t ◇ q47) (cg (fun t => t ◇ (q44 ◇ q46)) (cg (fun t => t ◇ (q44 ◇ q46)) (apc18 q44 q45 q44 q46 (q44 ◇ q46))))).symm).trans ((h (q44 ◇ q46) (((q44 ◇ ((((q44 ◇ q45) ◇ q44) ◇ q44) ◇ q44)) ◇ ((((q44 ◇ q45) ◇ q44) ◇ q44) ◇ q44)) ◇ ((((q44 ◇ q45) ◇ q44) ◇ q44) ◇ q44)) q47).symm)).trans (rfl))
  have apc22 : forall (q48 q49 q50 : G), (q48 ◇ q50) = (q48 ◇ q49) := by
    intro q48 q49 q50
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q50) ((h q48 q48 (q48 ◇ q49)).symm)).symm).trans (apc21 q48 q48 q49 q50)).trans (rfl))
  have apc24 : forall (q48 q49 q50 : G), (q48 ◇ q49) = (q48 ◇ q48) := by
    intro q48 q49 q50
    exact ((rfl).symm).trans (((apc22 q48 q49 q50).symm.trans (apc22 q48 q48 q50)).trans (rfl))
  have apc25 : forall (q4 q7 q5 q6 : G), ((q4 ◇ q4) ◇ (q4 ◇ q4)) = ((q4 ◇ q4) ◇ q7) := by
    intro q4 q7 q5 q6
    exact (((rfl).symm).trans ((((((((cg (fun t => t ◇ q7) (cg (fun t => q4 ◇ t) (cg (fun t => t ◇ ((((q4 ◇ q5) ◇ q4) ◇ q4) ◇ q4)) (cg (fun t => q4 ◇ t) (cg (fun t => t ◇ q4) (cg (fun t => t ◇ q4) (cg (fun t => t ◇ q4) (apc24 q4 q5 (q4 ◇ q5))))))))).trans (cg (fun t => t ◇ q7) (cg (fun t => q4 ◇ t) (cg (fun t => (q4 ◇ ((((q4 ◇ q4) ◇ q4) ◇ q4) ◇ q4)) ◇ t) (cg (fun t => t ◇ q4) (cg (fun t => t ◇ q4) (cg (fun t => t ◇ q4) (apc24 q4 q5 (q4 ◇ q5))))))))).trans (cg (fun t => t ◇ q7) (cg (fun t => q4 ◇ t) (cg (fun t => t ◇ ((((q4 ◇ q4) ◇ q4) ◇ q4) ◇ q4)) (apc24 q4 ((((q4 ◇ q4) ◇ q4) ◇ q4) ◇ q4) (q4 ◇ ((((q4 ◇ q4) ◇ q4) ◇ q4) ◇ q4))))))).trans (cg (fun t => t ◇ q7) (cg (fun t => q4 ◇ t) (apc24 (q4 ◇ q4) ((((q4 ◇ q4) ◇ q4) ◇ q4) ◇ q4) ((q4 ◇ q4) ◇ ((((q4 ◇ q4) ◇ q4) ◇ q4) ◇ q4)))))).trans (cg (fun t => t ◇ q7) (apc24 q4 ((q4 ◇ q4) ◇ (q4 ◇ q4)) (q4 ◇ ((q4 ◇ q4) ◇ (q4 ◇ q4)))))).symm).trans ((apc17 q4 q5 q7 q6).trans ((((cg (fun t => t ◇ ((((q4 ◇ q5) ◇ q4) ◇ q4) ◇ q4)) (cg (fun t => q4 ◇ t) (cg (fun t => t ◇ q4) (cg (fun t => t ◇ q4) (cg (fun t => t ◇ q4) (apc24 q4 q5 (q4 ◇ q5))))))).trans (cg (fun t => (q4 ◇ ((((q4 ◇ q4) ◇ q4) ◇ q4) ◇ q4)) ◇ t) (cg (fun t => t ◇ q4) (cg (fun t => t ◇ q4) (cg (fun t => t ◇ q4) (apc24 q4 q5 (q4 ◇ q5))))))).trans (cg (fun t => t ◇ ((((q4 ◇ q4) ◇ q4) ◇ q4) ◇ q4)) (apc24 q4 ((((q4 ◇ q4) ◇ q4) ◇ q4) ◇ q4) (q4 ◇ ((((q4 ◇ q4) ◇ q4) ◇ q4) ◇ q4))))).trans (apc24 (q4 ◇ q4) ((((q4 ◇ q4) ◇ q4) ◇ q4) ◇ q4) ((q4 ◇ q4) ◇ ((((q4 ◇ q4) ◇ q4) ◇ q4) ◇ q4)))))).trans (rfl))).symm
  have apc29 : forall (q4 q7 q5 q6 : G), ((q4 ◇ q4) ◇ q7) = ((q4 ◇ q4) ◇ q4) := by
    intro q4 q7 q5 q6
    exact ((rfl).symm).trans (((apc25 q4 q7 q5 q6).symm.trans (apc25 q4 q4 q5 q6)).trans (rfl))
  have apc31 : forall (q51 q52 q53 q54 q55 q56 : G), (((q53 ◇ q53) ◇ q53) ◇ ((q53 ◇ q53) ◇ q53)) = (((q53 ◇ q53) ◇ q53) ◇ q56) := by
    intro q51 q52 q53 q54 q55 q56
    exact ((((((((cg (fun t => t ◇ q56) (cg (fun t => (q53 ◇ q55) ◇ t) (cg (fun t => t ◇ q52) (cg (fun t => t ◇ ((((q53 ◇ q51) ◇ q53) ◇ q53) ◇ q53)) (apc24 q53 ((((q53 ◇ q51) ◇ q53) ◇ q53) ◇ q53) (q53 ◇ ((((q53 ◇ q51) ◇ q53) ◇ q53) ◇ q53))))))).trans (cg (fun t => t ◇ q56) (cg (fun t => (q53 ◇ q55) ◇ t) (cg (fun t => t ◇ q52) (apc24 (q53 ◇ q53) ((((q53 ◇ q51) ◇ q53) ◇ q53) ◇ q53) ((q53 ◇ q53) ◇ ((((q53 ◇ q51) ◇ q53) ◇ q53) ◇ q53))))))).trans (cg (fun t => t ◇ q56) (cg (fun t => (q53 ◇ q55) ◇ t) (cg (fun t => t ◇ q52) (apc29 q53 (q53 ◇ q53) ((q53 ◇ q53) ◇ (q53 ◇ q53)) ((q53 ◇ q53) ◇ (q53 ◇ q53))))))).trans (cg (fun t => t ◇ q56) (cg (fun t => t ◇ (((q53 ◇ q53) ◇ q53) ◇ q52)) (apc24 q53 q55 (q53 ◇ q55))))).trans (cg (fun t => t ◇ q56) (apc24 (q53 ◇ q53) (((q53 ◇ q53) ◇ q53) ◇ q52) ((q53 ◇ q53) ◇ (((q53 ◇ q53) ◇ q53) ◇ q52))))).trans (cg (fun t => t ◇ q56) (apc29 q53 (q53 ◇ q53) ((q53 ◇ q53) ◇ (q53 ◇ q53)) ((q53 ◇ q53) ◇ (q53 ◇ q53))))).symm).trans ((((cg (fun t => t ◇ q56) (cg (fun t => (q53 ◇ q55) ◇ t) (apc19 q51 q53 q54 q52))).symm).trans (apc18 q53 q54 q51 q55 q56)).trans (((((((cg (fun t => t ◇ ((((q53 ◇ q54) ◇ q53) ◇ q53) ◇ q53)) (cg (fun t => t ◇ ((((q53 ◇ q54) ◇ q53) ◇ q53) ◇ q53)) (cg (fun t => q53 ◇ t) (cg (fun t => t ◇ q53) (cg (fun t => t ◇ q53) (cg (fun t => t ◇ q53) (apc24 q53 q54 (q53 ◇ q54)))))))).trans (cg (fun t => t ◇ ((((q53 ◇ q54) ◇ q53) ◇ q53) ◇ q53)) (cg (fun t => (q53 ◇ ((((q53 ◇ q53) ◇ q53) ◇ q53) ◇ q53)) ◇ t) (cg (fun t => t ◇ q53) (cg (fun t => t ◇ q53) (cg (fun t => t ◇ q53) (apc24 q53 q54 (q53 ◇ q54)))))))).trans (cg (fun t => ((q53 ◇ ((((q53 ◇ q53) ◇ q53) ◇ q53) ◇ q53)) ◇ ((((q53 ◇ q53) ◇ q53) ◇ q53) ◇ q53)) ◇ t) (cg (fun t => t ◇ q53) (cg (fun t => t ◇ q53) (cg (fun t => t ◇ q53) (apc24 q53 q54 (q53 ◇ q54))))))).trans (cg (fun t => t ◇ ((((q53 ◇ q53) ◇ q53) ◇ q53) ◇ q53)) (cg (fun t => t ◇ ((((q53 ◇ q53) ◇ q53) ◇ q53) ◇ q53)) (apc24 q53 ((((q53 ◇ q53) ◇ q53) ◇ q53) ◇ q53) (q53 ◇ ((((q53 ◇ q53) ◇ q53) ◇ q53) ◇ q53)))))).trans (cg (fun t => t ◇ ((((q53 ◇ q53) ◇ q53) ◇ q53) ◇ q53)) (apc24 (q53 ◇ q53) ((((q53 ◇ q53) ◇ q53) ◇ q53) ◇ q53) ((q53 ◇ q53) ◇ ((((q53 ◇ q53) ◇ q53) ◇ q53) ◇ q53))))).trans (cg (fun t => t ◇ ((((q53 ◇ q53) ◇ q53) ◇ q53) ◇ q53)) (apc29 q53 (q53 ◇ q53) ((q53 ◇ q53) ◇ (q53 ◇ q53)) ((q53 ◇ q53) ◇ (q53 ◇ q53))))).trans (apc24 ((q53 ◇ q53) ◇ q53) ((((q53 ◇ q53) ◇ q53) ◇ q53) ◇ q53) (((q53 ◇ q53) ◇ q53) ◇ ((((q53 ◇ q53) ◇ q53) ◇ q53) ◇ q53)))))).symm
  have apc33 : forall (q53 q56 q51 q52 q54 q55 : G), (((q53 ◇ q53) ◇ q53) ◇ q56) = (((q53 ◇ q53) ◇ q53) ◇ q53) := by
    intro q53 q56 q51 q52 q54 q55
    exact ((rfl).symm).trans (((apc31 q51 q52 q53 q54 q55 q56).symm.trans (apc31 q51 q52 q53 q54 q55 q53)).trans (rfl))
  have apc36 : forall (q57 q58 q59 q60 : G), (((((q59 ◇ q59) ◇ q59) ◇ q58) ◇ q59) ◇ q60) = q59 := by
    intro q57 q58 q59 q60
    exact ((((cg (fun t => t ◇ q60) (cg (fun t => t ◇ q59) (cg (fun t => t ◇ q58) (cg (fun t => t ◇ ((((q59 ◇ q57) ◇ q59) ◇ q59) ◇ q59)) (apc24 q59 ((((q59 ◇ q57) ◇ q59) ◇ q59) ◇ q59) (q59 ◇ ((((q59 ◇ q57) ◇ q59) ◇ q59) ◇ q59))))))).trans (cg (fun t => t ◇ q60) (cg (fun t => t ◇ q59) (cg (fun t => t ◇ q58) (apc24 (q59 ◇ q59) ((((q59 ◇ q57) ◇ q59) ◇ q59) ◇ q59) ((q59 ◇ q59) ◇ ((((q59 ◇ q57) ◇ q59) ◇ q59) ◇ q59))))))).trans (cg (fun t => t ◇ q60) (cg (fun t => t ◇ q59) (cg (fun t => t ◇ q58) (apc29 q59 (q59 ◇ q59) ((q59 ◇ q59) ◇ (q59 ◇ q59)) ((q59 ◇ q59) ◇ (q59 ◇ q59))))))).symm).trans ((((cg (fun t => t ◇ q60) (cg (fun t => t ◇ q59) (apc20 q57 q58 q57 q59 q59))).symm).trans (apc10 q57 q57 q59 q60)).trans (rfl))
  have apc37 : forall (q61 q62 q63 q64 : G), ((((q61 ◇ q61) ◇ q61) ◇ q61) ◇ q64) = ((((q61 ◇ q61) ◇ q61) ◇ q61) ◇ q61) := by
    intro q61 q62 q63 q64
    exact ((((((((cg (fun t => t ◇ q64) (cg (fun t => t ◇ ((((q61 ◇ q62) ◇ q61) ◇ q61) ◇ q61)) (cg (fun t => (q61 ◇ q63) ◇ t) (cg (fun t => t ◇ q61) (cg (fun t => t ◇ q61) (cg (fun t => t ◇ q61) (apc24 q61 q62 (q61 ◇ q62)))))))).trans (cg (fun t => t ◇ q64) (cg (fun t => ((q61 ◇ q63) ◇ ((((q61 ◇ q61) ◇ q61) ◇ q61) ◇ q61)) ◇ t) (cg (fun t => t ◇ q61) (cg (fun t => t ◇ q61) (cg (fun t => t ◇ q61) (apc24 q61 q62 (q61 ◇ q62)))))))).trans (cg (fun t => t ◇ q64) (cg (fun t => t ◇ ((((q61 ◇ q61) ◇ q61) ◇ q61) ◇ q61)) (cg (fun t => t ◇ ((((q61 ◇ q61) ◇ q61) ◇ q61) ◇ q61)) (apc24 q61 q63 (q61 ◇ q63)))))).trans (cg (fun t => t ◇ q64) (cg (fun t => t ◇ ((((q61 ◇ q61) ◇ q61) ◇ q61) ◇ q61)) (apc24 (q61 ◇ q61) ((((q61 ◇ q61) ◇ q61) ◇ q61) ◇ q61) ((q61 ◇ q61) ◇ ((((q61 ◇ q61) ◇ q61) ◇ q61) ◇ q61)))))).trans (cg (fun t => t ◇ q64) (cg (fun t => t ◇ ((((q61 ◇ q61) ◇ q61) ◇ q61) ◇ q61)) (apc29 q61 (q61 ◇ q61) ((q61 ◇ q61) ◇ (q61 ◇ q61)) ((q61 ◇ q61) ◇ (q61 ◇ q61)))))).trans (cg (fun t => t ◇ q64) (apc24 ((q61 ◇ q61) ◇ q61) ((((q61 ◇ q61) ◇ q61) ◇ q61) ◇ q61) (((q61 ◇ q61) ◇ q61) ◇ ((((q61 ◇ q61) ◇ q61) ◇ q61) ◇ q61))))).trans (cg (fun t => t ◇ q64) (apc33 q61 ((q61 ◇ q61) ◇ q61) (((q61 ◇ q61) ◇ q61) ◇ ((q61 ◇ q61) ◇ q61)) (((q61 ◇ q61) ◇ q61) ◇ ((q61 ◇ q61) ◇ q61)) (((q61 ◇ q61) ◇ q61) ◇ ((q61 ◇ q61) ◇ q61)) (((q61 ◇ q61) ◇ q61) ◇ ((q61 ◇ q61) ◇ q61))))).symm).trans ((((cg (fun t => t ◇ q64) (cg (fun t => t ◇ ((((q61 ◇ q62) ◇ q61) ◇ q61) ◇ q61)) (cg (fun t => t ◇ ((((q61 ◇ q62) ◇ q61) ◇ q61) ◇ q61)) (apc21 q61 q62 q63 ((((q61 ◇ q62) ◇ q61) ◇ q61) ◇ q61))))).symm).trans ((h ((((q61 ◇ q62) ◇ q61) ◇ q61) ◇ q61) (q61 ◇ q63) q64).symm)).trans (cg (fun t => t ◇ q61) (cg (fun t => t ◇ q61) (cg (fun t => t ◇ q61) (apc24 q61 q62 (q61 ◇ q62))))))
  exact (calc
    x = x := rfl
    _ = (((((x ◇ x) ◇ y) ◇ y) ◇ z) ◇ w) := ((((cg (fun t => t ◇ w) (cg (fun t => t ◇ z) (cg (fun t => t ◇ y) (apc29 x y ((x ◇ x) ◇ y) ((x ◇ x) ◇ y))))).trans (cg (fun t => t ◇ w) (cg (fun t => t ◇ z) (apc33 x y (((x ◇ x) ◇ x) ◇ y) (((x ◇ x) ◇ x) ◇ y) (((x ◇ x) ◇ x) ◇ y) (((x ◇ x) ◇ x) ◇ y))))).trans (cg (fun t => t ◇ w) (apc37 x ((((x ◇ x) ◇ x) ◇ x) ◇ z) ((((x ◇ x) ◇ x) ◇ x) ◇ z) z))).trans (apc36 (((((x ◇ x) ◇ x) ◇ x) ◇ x) ◇ w) x x w)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_40706_to_40686 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_40706_to_40686
