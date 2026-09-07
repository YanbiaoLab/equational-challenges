-- Equation46590 → Equation55921
-- Recorded verdict: true
-- Premise: x * y = (z * z) * (y * (x * x))
-- Conclusion: x * (y * y) = (x * x) * (z * x)
-- Original submission SHA-256: 49015690d8f261703e3c906384af68dc9612479a0e53da190f8dfb07cba40a7c
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (z ◇ z) ◇ (y ◇ (x ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ y) = (x ◇ x) ◇ (z ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2:G), ((q2 ◇ q2) ◇ (q0 ◇ (q0 ◇ q0))) = ((q0 ◇ q0) ◇ (q1 ◇ q1)):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => (q2 ◇ q2) ◇ t) ((h q0 (q0 ◇ q0) q1).symm)).symm).trans ((h (q0 ◇ q0) (q1 ◇ q1) q2).symm)
  have apc1 : forall (q3 q4:G), ((q4 ◇ q4) ◇ (q3 ◇ q3)) = (q4 ◇ q4):=by
    intro q3 q4
    exact ((apc0 q4 q3 q3).symm).trans ((h q4 q4 q3).symm)
  have apc2 : forall (q5 q4 q6:G), ((q5 ◇ q5) ◇ (q6 ◇ (q6 ◇ q6))) = (q4 ◇ (q4 ◇ q4)):=by
    intro q5 q4 q6
    exact (apc0 q6 (q4 ◇ q4) q5).trans ((h q4 (q4 ◇ q4) q6).symm)
  have apc3 : forall (q5 q4 q6:G), (q4 ◇ (q4 ◇ q4)) = (q5 ◇ (q5 ◇ q5)):=by
    intro q5 q4 q6
    exact ((apc2 q5 q4 q6).symm).trans (apc2 q5 q5 q6)
  have apc11 : forall (q0 q7 q8:G), ((q0 ◇ (q0 ◇ q0)) ◇ (q8 ◇ (q7 ◇ q7))) = (q7 ◇ q8):=by
    intro q0 q7 q8
    exact ((congrArg (fun t => t ◇ (q8 ◇ (q7 ◇ q7))) ((h q0 (q0 ◇ q0) (q0 ◇ q0)).symm)).symm).trans ((h q7 q8 ((q0 ◇ q0) ◇ (q0 ◇ q0))).symm)
  have apc12 : forall (q9 q10 q11:G), ((q10 ◇ (q10 ◇ q10)) ◇ (q9 ◇ q9)) = (q11 ◇ (q9 ◇ q9)):=by
    intro q9 q10 q11
    exact ((congrArg (fun t => (q10 ◇ (q10 ◇ q10)) ◇ t) (apc1 q11 q9)).symm).trans (apc11 q10 q11 (q9 ◇ q9))
  have apc13 : forall (q9 q10 q11:G), (q11 ◇ (q9 ◇ q9)) = (q9 ◇ (q9 ◇ q9)):=by
    intro q9 q10 q11
    exact ((apc12 q9 q10 q11).symm).trans (apc12 q9 q10 q9)
  have apc15 : forall (q12 q13:G), ((q12 ◇ (q12 ◇ q12)) ◇ (q13 ◇ (q13 ◇ q13))) = (q13 ◇ (q13 ◇ q13)):=by
    intro q12 q13
    exact ((congrArg (fun t => (q12 ◇ (q12 ◇ q12)) ◇ t) (apc13 q13 ((q13 ◇ q13) ◇ (q13 ◇ q13)) (q13 ◇ q13))).symm).trans ((apc12 (q13 ◇ q13) q12 (q12 ◇ q12)).trans ((h q13 (q13 ◇ q13) q12).symm))
  have apc16 : forall (q14:G), ((q14 ◇ q14) ◇ (q14 ◇ (q14 ◇ q14))) = (q14 ◇ (q14 ◇ q14)):=by
    intro q14
    exact ((congrArg (fun t => (q14 ◇ q14) ◇ t) (apc13 q14 ((q14 ◇ q14) ◇ (q14 ◇ q14)) (q14 ◇ q14))).symm).trans (((apc13 (q14 ◇ q14) q14 (q14 ◇ q14)).symm).trans ((h q14 (q14 ◇ q14) q14).symm))
  have apc17 : forall (q15 q16:G), ((q16 ◇ q16) ◇ (q15 ◇ (q15 ◇ q15))) = (q16 ◇ (q16 ◇ q16)):=by
    intro q15 q16
    exact ((congrArg (fun t => (q16 ◇ q16) ◇ t) (apc3 q15 q16 q15)).symm).trans (apc16 q16)
  have apc19 : forall (q9 q17 q10:G), (q9 ◇ (q9 ◇ q9)) = ((q9 ◇ q9) ◇ q17):=by
    intro q9 q17 q10
    exact (((congrArg (fun t => (q10 ◇ (q10 ◇ q10)) ◇ t) (apc13 q9 (q17 ◇ (q9 ◇ q9)) q17)).trans (apc15 q10 q9)).symm).trans (((congrArg (fun t => (q10 ◇ (q10 ◇ q10)) ◇ t) (congrArg (fun t => q17 ◇ t) (apc1 q9 q9))).symm).trans (apc11 q10 (q9 ◇ q9) q17))
  have apc21 : forall (q4 q18 q5 q19:G), (q4 ◇ (q4 ◇ q4)) = (q4 ◇ q18):=by
    intro q4 q18 q5 q19
    exact ((((congrArg (fun t => ((q5 ◇ q5) ◇ (q19 ◇ (q19 ◇ q19))) ◇ t) (apc13 q4 (q18 ◇ (q4 ◇ q4)) q18)).trans (congrArg (fun t => t ◇ (q4 ◇ (q4 ◇ q4))) (apc17 q19 q5))).trans (apc15 q5 q4)).symm).trans (((congrArg (fun t => t ◇ (q18 ◇ (q4 ◇ q4))) ((apc0 q19 q19 q5).symm)).symm).trans ((h q4 q18 (q19 ◇ q19)).symm))
  have apc23 : forall (q20 q21 q22:G), ((q21 ◇ (q21 ◇ q21)) ◇ (q22 ◇ q20)) = (q22 ◇ (q22 ◇ q22)):=by
    intro q20 q21 q22
    exact ((congrArg (fun t => (q21 ◇ (q21 ◇ q21)) ◇ t) (apc21 q22 q20 q20 q20)).symm).trans (apc15 q21 q22)
  have apc24 : forall (q23 q24 q25 q26:G), ((q25 ◇ q23) ◇ (q26 ◇ q24)) = (q26 ◇ (q26 ◇ q26)):=by
    intro q23 q24 q25 q26
    exact ((congrArg (fun t => t ◇ (q26 ◇ q24)) (apc21 q25 q23 q23 q23)).symm).trans (apc23 q24 q25 q26)
  have apc25 : forall (q27 q28 q29 q30:G), (q29 ◇ (q29 ◇ q29)) = (q29 ◇ (q28 ◇ q27)):=by
    intro q27 q28 q29 q30
    exact ((apc24 q30 (q29 ◇ q29) q30 q29).symm).trans (((congrArg (fun t => (q30 ◇ q30) ◇ t) (apc24 q27 q29 q28 q29)).symm).trans ((h q29 (q28 ◇ q27) q30).symm))
  have apc26 : forall (q31 q32 q33 q34:G), (q33 ◇ (q32 ◇ q31)) = ((q33 ◇ q33) ◇ q34):=by
    intro q31 q32 q33 q34
    exact ((apc25 q31 q32 q33 q31).symm).trans (apc19 q33 q34 q31)
  exact apc26 y y x (z ◇ x)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_46590_to_55921 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_46590_to_55921
