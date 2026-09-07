-- Equation42823 → Equation47151
-- Recorded verdict: true
-- Premise: x * y = y * (y * ((z * y) * z))
-- Conclusion: x * y = (y * x) * ((x * z) * x)
-- Original submission SHA-256: f708b80f43e6475dfbe3377f4bd79f4ffb7efd78dc055e5bcbd9b9dc93fecadf
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = y ◇ (y ◇ ((z ◇ y) ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (y ◇ x) ◇ ((x ◇ z) ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (x y z:G), (y ◇ y) = (x ◇ y):=by
    intro x y z
    exact ((h x y z).trans ((h y y z).symm)).symm
  have apc1 : forall (q0 q1 q2:G), (q1 ◇ q2) = (q0 ◇ q2):=by
    intro q0 q1 q2
    exact ((h q0 q2 q0).trans ((h q1 q2 q0).symm)).symm
  have apc2 : forall (q3 q4 q5:G), (q4 ◇ (q4 ◇ (q5 ◇ q5))) = (q3 ◇ q4):=by
    intro q3 q4 q5
    exact ((congrArg (fun t => q4 ◇ t) (congrArg (fun t => q4 ◇ t) ((apc0 (q5 ◇ q4) q5 q3).symm))).symm).trans ((h q3 q4 q5).symm)
  have apc3 : forall (q6 q7 q8:G), (q7 ◇ ((q8 ◇ q8) ◇ (q8 ◇ q8))) = (q6 ◇ q7):=by
    intro q6 q7 q8
    exact ((congrArg (fun t => q7 ◇ t) ((apc0 q7 (q8 ◇ q8) q6).symm)).symm).trans (apc2 q6 q7 q8)
  have apc4 : forall (q9 q10 q11:G), (q11 ◇ (q9 ◇ q11)) = (q10 ◇ q11):=by
    intro q9 q10 q11
    exact ((congrArg (fun t => q11 ◇ t) (apc3 q9 q11 q9)).symm).trans (apc2 q10 q11 (q9 ◇ q9))
  have apc6 : forall (q12 q13 q14:G), ((q12 ◇ q14) ◇ (q12 ◇ q14)) = (q13 ◇ q14):=by
    intro q12 q13 q14
    exact (((apc4 q12 q13 q14).symm).trans ((apc0 q14 (q12 ◇ q14) q12).symm)).symm
  have apc7 : forall (q15 q16 q17:G), ((q15 ◇ q17) ◇ (q17 ◇ q17)) = (q16 ◇ q17):=by
    intro q15 q16 q17
    exact ((congrArg (fun t => t ◇ (q17 ◇ q17)) (apc0 q15 q17 q15)).symm).trans (apc6 q17 q16 q17)
  have apc8 : forall (q18 q19 q20 q21:G), ((q18 ◇ q21) ◇ (q19 ◇ q21)) = (q20 ◇ q21):=by
    intro q18 q19 q20 q21
    exact ((congrArg (fun t => t ◇ (q19 ◇ q21)) (apc1 q18 q19 q21)).symm).trans (apc6 q19 q20 q21)
  have apc10 : forall (q22 q23:G), ((q22 ◇ q23) ◇ (q23 ◇ q23)) = (q23 ◇ q23):=by
    intro q22 q23
    exact (apc7 q22 q22 q23).trans ((apc0 q22 q23 q22).symm)
  have apc12 : forall (q24 q25 q26:G), ((q24 ◇ q26) ◇ (q25 ◇ q26)) = (q26 ◇ q26):=by
    intro q24 q25 q26
    exact (apc8 q24 q25 q24 q26).trans ((apc0 q24 q26 q24).symm)
  have apc13 : forall (q27 q28 q29:G), ((q27 ◇ q29) ◇ (q28 ◇ q28)) = (q28 ◇ q28):=by
    intro q27 q28 q29
    exact (((congrArg (fun t => (q27 ◇ q29) ◇ t) (apc12 q29 q29 (q28 ◇ q28))).trans (congrArg (fun t => (q27 ◇ q29) ◇ t) (apc12 q28 q28 q28))).symm).trans ((((congrArg (fun t => t ◇ ((q29 ◇ (q28 ◇ q28)) ◇ (q29 ◇ (q28 ◇ q28)))) (apc2 q27 q29 q28)).symm).trans (apc10 q29 (q29 ◇ (q28 ◇ q28)))).trans ((apc12 q29 q29 (q28 ◇ q28)).trans (apc12 q28 q28 q28)))
  have apc14 : forall (q30 q31 q32 q33:G), ((q31 ◇ q33) ◇ (q30 ◇ q32)) = (q32 ◇ q32):=by
    intro q30 q31 q32 q33
    exact ((congrArg (fun t => (q31 ◇ q33) ◇ t) (apc0 q30 q32 q30)).symm).trans (apc13 q31 q32 q33)
  have apc17 : forall (q0 q1 q34 q35:G), (q34 ◇ q34) = (q0 ◇ q1):=by
    intro q0 q1 q34 q35
    exact (((h q0 q1 q35).trans (h q1 (q1 ◇ ((q35 ◇ q1) ◇ q35)) q34)).trans ((congrArg (fun t => (q1 ◇ ((q35 ◇ q1) ◇ q35)) ◇ t) (apc14 (q34 ◇ (q1 ◇ ((q35 ◇ q1) ◇ q35))) q1 q34 ((q35 ◇ q1) ◇ q35))).trans (apc14 q34 q1 q34 ((q35 ◇ q1) ◇ q35)))).symm
  exact ((apc17 x y (x ◇ y) (x ◇ y)).symm).trans (apc17 (y ◇ x) ((x ◇ z) ◇ x) (x ◇ y) (x ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_42823_to_47151 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_42823_to_47151
