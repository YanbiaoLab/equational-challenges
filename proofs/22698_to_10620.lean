-- Equation22698 → Equation10620
-- Recorded verdict: true
-- Premise: x = (y ◇ (y ◇ z)) ◇ ((z ◇ x) ◇ y)
-- Conclusion: x = y ◇ ((z ◇ z) ◇ ((x ◇ y) ◇ x))
-- Original submission SHA-256: 663a3d053affa0153f7f84dcf8b0485a54431d9b96ab121961be8051106dd8c3
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ (y ◇ z)) ◇ ((z ◇ x) ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ ((z ◇ z) ◇ ((x ◇ y) ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f : G → G) {a b : G}, a = b → f a = f b := by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1 : G), ((q1 ◇ q1) ◇ ((q1 ◇ q0) ◇ (q1 ◇ (q1 ◇ q1)))) = q0 := by
    intro q0 q1
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ ((q1 ◇ q0) ◇ (q1 ◇ (q1 ◇ q1)))) ((h (q1 ◇ q1) q1 q1).symm)).symm).trans ((h q0 (q1 ◇ (q1 ◇ q1)) q1).symm)).trans (rfl))
  have apc1 : forall (q2 q3 : G), (q2 ◇ (((q2 ◇ (q2 ◇ q2)) ◇ q3) ◇ (q2 ◇ q2))) = q3 := by
    intro q2 q3
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (((q2 ◇ (q2 ◇ q2)) ◇ q3) ◇ (q2 ◇ q2))) (apc0 q2 q2)).symm).trans ((h q3 (q2 ◇ q2) (q2 ◇ (q2 ◇ q2))).symm)).trans (rfl))
  have apc2 : forall (q4 q5 : G), (q5 ◇ (q4 ◇ (q5 ◇ q5))) = ((q5 ◇ q4) ◇ q5) := by
    intro q4 q5
    exact ((rfl).symm).trans ((((cg (fun t => q5 ◇ t) (cg (fun t => t ◇ (q5 ◇ q5)) ((h q4 q5 q5).symm))).symm).trans (apc1 q5 ((q5 ◇ q4) ◇ q5))).trans (rfl))
  have apc3 : forall (q6 q7 : G), (((q7 ◇ q7) ◇ q7) ◇ (((q7 ◇ q7) ◇ q6) ◇ q7)) = q6 := by
    intro q6 q7
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (((q7 ◇ q7) ◇ q6) ◇ q7)) (apc2 q7 q7)).symm).trans ((h q6 q7 (q7 ◇ q7)).symm)).trans (rfl))
  have apc4 : forall (q8 q9 : G), (q9 ◇ ((q9 ◇ q8) ◇ ((q9 ◇ q9) ◇ q9))) = q8 := by
    intro q8 q9
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ ((q9 ◇ q8) ◇ ((q9 ◇ q9) ◇ q9))) (apc3 q9 q9)).symm).trans ((h q8 ((q9 ◇ q9) ◇ q9) q9).symm)).trans (rfl))
  have apc9 : forall (q10 q11 : G), (q11 ◇ (q10 ◇ ((q11 ◇ q11) ◇ q11))) = ((q11 ◇ q10) ◇ ((q11 ◇ q11) ◇ q11)) := by
    intro q10 q11
    exact ((rfl).symm).trans ((((cg (fun t => q11 ◇ t) (cg (fun t => t ◇ ((q11 ◇ q11) ◇ q11)) (apc4 q10 q11))).symm).trans (apc4 ((q11 ◇ q10) ◇ ((q11 ◇ q11) ◇ q11)) q11)).trans (rfl))
  have apc10 : forall (q8 q9 q10 q11 : G), ((q9 ◇ (q9 ◇ q8)) ◇ ((q9 ◇ q9) ◇ q9)) = q8 := by
    intro q8 q9 q10 q11
    exact ((rfl).symm).trans ((((apc9 (q9 ◇ q8) q9).symm).trans ((apc4 q8 q9).trans (rfl))).trans (rfl))
  have apc18 : forall (q12 q13 q14 q15 : G), ((q15 ◇ (q15 ◇ (q13 ◇ (q13 ◇ q14)))) ◇ (q12 ◇ q15)) = ((q14 ◇ q12) ◇ q13) := by
    intro q12 q13 q14 q15
    exact ((rfl).symm).trans ((((cg (fun t => (q15 ◇ (q15 ◇ (q13 ◇ (q13 ◇ q14)))) ◇ t) (cg (fun t => t ◇ q15) ((h q12 q13 q14).symm))).symm).trans ((h ((q14 ◇ q12) ◇ q13) q15 (q13 ◇ (q13 ◇ q14))).symm)).trans (rfl))
  have apc19 : forall (q16 q17 q18 : G), ((q17 ◇ (q18 ◇ q18)) ◇ q16) = (q16 ◇ (q16 ◇ q17)) := by
    intro q16 q17 q18
    exact ((rfl).symm).trans ((((apc18 (q18 ◇ q18) q16 q17 q18).symm).trans (apc10 (q16 ◇ (q16 ◇ q17)) q18 q16 q16)).trans (rfl))
  have apc20 : forall (q19 q20 : G), (q20 ◇ (q20 ◇ (q19 ◇ q19))) = ((q19 ◇ q19) ◇ q20) := by
    intro q19 q20
    exact (((rfl).symm).trans ((((cg (fun t => t ◇ q20) (apc0 (q19 ◇ q19) q19)).symm).trans (apc19 q20 (q19 ◇ q19) (q19 ◇ (q19 ◇ q19)))).trans (rfl))).symm
  have apc21 : forall (q21 q22 q23 : G), (q23 ◇ ((q23 ◇ q23) ◇ ((q23 ◇ q23) ◇ q21))) = ((q23 ◇ (q21 ◇ (q22 ◇ q22))) ◇ q23) := by
    intro q21 q22 q23
    exact ((rfl).symm).trans ((((cg (fun t => q23 ◇ t) (apc19 (q23 ◇ q23) q21 q22)).symm).trans (apc2 (q21 ◇ (q22 ◇ q22)) q23)).trans (rfl))
  have apc23 : forall (q24 q25 : G), (((q25 ◇ q25) ◇ q24) ◇ q24) = q24 := by
    intro q24 q25
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q24) (apc20 q25 q24)).symm).trans ((apc21 q24 q25 q24).symm)).trans ((apc9 (q24 ◇ q24) q24).trans (apc10 q24 q24 ((q24 ◇ (q24 ◇ q24)) ◇ ((q24 ◇ q24) ◇ q24)) ((q24 ◇ (q24 ◇ q24)) ◇ ((q24 ◇ q24) ◇ q24)))))
  have apc24 : forall (q26 q27 q28 : G), (q28 ◇ ((q28 ◇ q27) ◇ ((q26 ◇ q26) ◇ q28))) = q27 := by
    intro q26 q27 q28
    exact ((cg (fun t => t ◇ ((q28 ◇ q27) ◇ ((q26 ◇ q26) ◇ q28))) (apc23 q28 q26)).symm).trans ((((cg (fun t => t ◇ ((q28 ◇ q27) ◇ ((q26 ◇ q26) ◇ q28))) (cg (fun t => ((q26 ◇ q26) ◇ q28) ◇ t) (apc23 q28 q26))).symm).trans ((h q27 ((q26 ◇ q26) ◇ q28) q28).symm)).trans (rfl))
  have apc29 : forall (q29 q30 q31 : G), (q31 ◇ q31) = (q29 ◇ q29) := by
    intro q29 q30 q31
    exact (((cg (fun t => q31 ◇ t) (cg (fun t => ((q30 ◇ q30) ◇ q31) ◇ t) (apc23 q31 q30))).trans (cg (fun t => q31 ◇ t) (apc23 q31 q30))).symm).trans ((((cg (fun t => q31 ◇ t) (apc19 ((q30 ◇ q30) ◇ q31) q31 q29)).symm).trans (apc24 q30 (q29 ◇ q29) q31)).trans (rfl))
  have apc48 : forall (q32 q33 q34 : G), ((q34 ◇ q32) ◇ ((q33 ◇ (q33 ◇ (q32 ◇ (q32 ◇ q34)))) ◇ q34)) = q33 := by
    intro q32 q33 q34
    exact (((cg (fun t => (q34 ◇ q32) ◇ t) (cg (fun t => t ◇ q34) (cg (fun t => t ◇ q33) (cg (fun t => t ◇ (q34 ◇ q34)) (apc19 q32 q34 q34))))).trans (cg (fun t => (q34 ◇ q32) ◇ t) (cg (fun t => t ◇ q34) (apc19 q33 (q32 ◇ (q32 ◇ q34)) q34)))).symm).trans ((((cg (fun t => t ◇ (((((q34 ◇ (q34 ◇ q34)) ◇ q32) ◇ (q34 ◇ q34)) ◇ q33) ◇ q34)) (cg (fun t => q34 ◇ t) (apc1 q34 q32))).symm).trans ((h q33 q34 (((q34 ◇ (q34 ◇ q34)) ◇ q32) ◇ (q34 ◇ q34))).symm)).trans (rfl))
  have apc74 : forall (q35 q36 q37 : G), ((q37 ◇ (q37 ◇ q36)) ◇ ((q35 ◇ q35) ◇ q37)) = q36 := by
    intro q35 q36 q37
    exact ((rfl).symm).trans ((((cg (fun t => (q37 ◇ (q37 ◇ q36)) ◇ t) (cg (fun t => t ◇ q37) (apc29 q35 q35 q36))).symm).trans ((h q36 q37 q36).symm)).trans (rfl))
  have apc136 : forall (q38 q39 q40 : G), (((q38 ◇ q40) ◇ q39) ◇ (((q38 ◇ q40) ◇ q38) ◇ q39)) = q40 := by
    intro q38 q39 q40
    exact ((rfl).symm).trans ((((cg (fun t => ((q38 ◇ q40) ◇ q39) ◇ t) (apc18 q38 q39 (q38 ◇ q40) q40)).symm).trans (apc48 q39 q40 (q38 ◇ q40))).trans (rfl))
  have apc138 : forall (q41 q42 q43 : G), (q41 ◇ ((q42 ◇ q42) ◇ ((q43 ◇ q41) ◇ q43))) = q43 := by
    intro q41 q42 q43
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ ((q42 ◇ q42) ◇ ((q43 ◇ q41) ◇ q43))) (apc136 q43 q43 q41)).symm).trans (apc74 q42 q43 ((q43 ◇ q41) ◇ q43))).trans (rfl))
  exact (calc
    x = x := rfl
    _ = (y ◇ ((z ◇ z) ◇ ((x ◇ y) ◇ x))) := (apc138 y z x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_22698_to_10620 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_22698_to_10620
