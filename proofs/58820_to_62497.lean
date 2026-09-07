-- Equation58820 → Equation62497
-- Recorded verdict: true
-- Premise: (x * y) * z = y * (z * (w * x))
-- Conclusion: (x * y) * z = ((w * z) * y) * u
-- Original submission SHA-256: fa3d0f7dd6025f0917cb79350134c8b16138971e86e1df593ab75a52261d75c2
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ z = y ◇ (z ◇ (w ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), (x ◇ y) ◇ z = ((w ◇ z) ◇ y) ◇ u
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (x y z w:G), (y ◇ (z ◇ (x ◇ x))) = (y ◇ (z ◇ (w ◇ x))):=by
    intro x y z w
    exact (((h x y z w).symm).trans (h x y z x)).symm
  have apc1 : forall (q0 q1 q2 q3 q4:G), (q3 ◇ ((q1 ◇ q4) ◇ q2)) = (((q0 ◇ q1) ◇ q3) ◇ q4):=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => q3 ◇ t) ((h q1 q4 q2 q0).symm)).symm).trans ((h (q0 ◇ q1) q3 q4 q2).symm)
  have apc2 : forall (q5 q6 q7:G), (q6 ◇ (q7 ◇ (q5 ◇ q5))) = ((q5 ◇ q6) ◇ q7):=by
    intro q5 q6 q7
    exact (apc0 q5 q6 q7 q5).trans ((h q5 q6 q7 q5).symm)
  have apc4 : forall (q0 q1 q2 q3 q4:G), (((q1 ◇ q1) ◇ q3) ◇ q4) = (((q0 ◇ q1) ◇ q3) ◇ q4):=by
    intro q0 q1 q2 q3 q4
    exact (((apc1 q0 q1 q0 q3 q4).symm).trans (apc1 q1 q1 q0 q3 q4)).symm
  have apc9 : forall (q8 q9 q10 q11:G), (q10 ◇ ((q8 ◇ q11) ◇ q9)) = (((q8 ◇ q8) ◇ q10) ◇ q11):=by
    intro q8 q9 q10 q11
    exact ((congrArg (fun t => q10 ◇ t) (apc2 q8 q11 q9)).symm).trans ((h (q8 ◇ q8) q10 q11 q9).symm)
  have apc10 : forall (q12 q13 q14:G), (((q12 ◇ q12) ◇ q13) ◇ q14) = ((q12 ◇ q13) ◇ (q12 ◇ q14)):=by
    intro q12 q13 q14
    exact (((apc2 q12 q13 (q12 ◇ q14)).symm).trans (((congrArg (fun t => q13 ◇ t) (apc2 q12 q14 (q12 ◇ q12))).symm).trans (apc2 (q12 ◇ q12) q13 q14))).symm
  have apc18 : forall (q0 q1 q2 q3 q4 q12 q13 q14:G), (((q0 ◇ q1) ◇ q3) ◇ q4) = ((q1 ◇ q3) ◇ (q1 ◇ q4)):=by
    intro q0 q1 q2 q3 q4 q12 q13 q14
    exact (((apc10 q1 q3 q4).symm).trans (apc4 q0 q1 q0 q3 q4)).symm
  have apc19 : forall (q8 q9 q10 q11 q12 q13 q14:G), (q10 ◇ ((q8 ◇ q11) ◇ q9)) = ((q8 ◇ q10) ◇ (q8 ◇ q11)):=by
    intro q8 q9 q10 q11 q12 q13 q14
    exact (apc9 q8 q9 q10 q11).trans (apc10 q8 q10 q11)
  have apc21 : forall (q15 q16 q17 q18:G), ((q15 ◇ q17) ◇ (q15 ◇ q18)) = ((q16 ◇ q17) ◇ q18):=by
    intro q15 q16 q17 q18
    exact ((apc19 q15 (q15 ◇ q15) q17 q18 (q17 ◇ ((q15 ◇ q18) ◇ (q15 ◇ q15))) (q17 ◇ ((q15 ◇ q18) ◇ (q15 ◇ q15))) (q17 ◇ ((q15 ◇ q18) ◇ (q15 ◇ q15)))).symm).trans (((congrArg (fun t => q17 ◇ t) (apc19 q15 q16 q18 q15 q15 q15 q15)).symm).trans ((h q16 q17 q18 (q15 ◇ q15)).symm))
  have apc49 : forall (q19 q20 q21 q22:G), ((q19 ◇ q21) ◇ (q19 ◇ (q20 ◇ q22))) = ((q20 ◇ q21) ◇ (q20 ◇ q22)):=by
    intro q19 q20 q21 q22
    exact ((apc19 q19 q19 q21 (q20 ◇ q22) (q21 ◇ ((q19 ◇ (q20 ◇ q22)) ◇ q19)) (q21 ◇ ((q19 ◇ (q20 ◇ q22)) ◇ q19)) (q21 ◇ ((q19 ◇ (q20 ◇ q22)) ◇ q19))).symm).trans ((((congrArg (fun t => q21 ◇ t) ((h q19 (q20 ◇ q22) q19 q19).symm)).symm).trans (apc1 q19 q20 (q19 ◇ (q19 ◇ q19)) q21 q22)).trans (apc18 q19 q20 (((q19 ◇ q20) ◇ q21) ◇ q22) q21 q22 (((q19 ◇ q20) ◇ q21) ◇ q22) (((q19 ◇ q20) ◇ q21) ◇ q22) (((q19 ◇ q20) ◇ q21) ◇ q22)))
  have apc50 : forall (q23 q24 q25 q26:G), (((q23 ◇ q24) ◇ (q23 ◇ q25)) ◇ q26) = ((q24 ◇ q25) ◇ (q24 ◇ q26)):=by
    intro q23 q24 q25 q26
    exact ((congrArg (fun t => t ◇ q26) (apc19 q23 q23 q24 q25 (q24 ◇ ((q23 ◇ q25) ◇ q23)) (q24 ◇ ((q23 ◇ q25) ◇ q23)) (q24 ◇ ((q23 ◇ q25) ◇ q23)))).symm).trans ((((congrArg (fun t => t ◇ q26) ((apc1 q23 q23 q23 q24 q25).symm)).symm).trans ((apc1 (q23 ◇ q23) q24 q23 q25 q26).symm)).trans (apc19 q24 q23 q25 q26 (q25 ◇ ((q24 ◇ q26) ◇ q23)) (q25 ◇ ((q24 ◇ q26) ◇ q23)) (q25 ◇ ((q24 ◇ q26) ◇ q23))))
  have apc56 : forall (q27 q28 q29 q30 q31:G), ((q27 ◇ q28) ◇ (q27 ◇ q28)) = ((q29 ◇ q30) ◇ q31):=by
    intro q27 q28 q29 q30 q31
    exact ((((((congrArg (fun t => ((q27 ◇ q28) ◇ (q27 ◇ q30)) ◇ t) (apc50 q27 q27 q28 q31)).trans (apc19 q27 (q27 ◇ q31) ((q27 ◇ q28) ◇ (q27 ◇ q30)) q28 (((q27 ◇ q28) ◇ (q27 ◇ q30)) ◇ ((q27 ◇ q28) ◇ (q27 ◇ q31))) (((q27 ◇ q28) ◇ (q27 ◇ q30)) ◇ ((q27 ◇ q28) ◇ (q27 ◇ q31))) (((q27 ◇ q28) ◇ (q27 ◇ q30)) ◇ ((q27 ◇ q28) ◇ (q27 ◇ q31))))).trans (congrArg (fun t => t ◇ (q27 ◇ q28)) (apc19 q27 (q27 ◇ q30) q27 q28 (q27 ◇ ((q27 ◇ q28) ◇ (q27 ◇ q30))) (q27 ◇ ((q27 ◇ q28) ◇ (q27 ◇ q30))) (q27 ◇ ((q27 ◇ q28) ◇ (q27 ◇ q30)))))).trans (apc50 q27 q27 q28 (q27 ◇ q28))).trans (apc49 q27 q27 q28 q28)).symm).trans (((congrArg (fun t => t ◇ (((q27 ◇ q27) ◇ (q27 ◇ q28)) ◇ q31)) (apc50 q27 q27 q28 q30)).symm).trans (apc21 ((q27 ◇ q27) ◇ (q27 ◇ q28)) q29 q30 q31))
  exact ((apc56 ((x ◇ y) ◇ z) (((w ◇ z) ◇ y) ◇ u) x y z).symm).trans (apc56 ((x ◇ y) ◇ z) (((w ◇ z) ◇ y) ◇ u) (w ◇ z) y u)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_58820_to_62497 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_58820_to_62497
