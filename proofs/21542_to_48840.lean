-- Equation21542 → Equation48840
-- Recorded verdict: true
-- Premise: x = (x * (y * z)) * (w * (y * z))
-- Conclusion: x * y = ((x * z) * y) * (x * y)
-- Original submission SHA-256: 8a509413d1bdd6a4177981f0d59612ffa68ef85ab16ff127634b67183240990e
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (x ◇ (y ◇ z)) ◇ (w ◇ (y ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = ((x ◇ z) ◇ y) ◇ (x ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3 q4:G), (q0 ◇ (q3 ◇ (q4 ◇ (q1 ◇ q2)))) = (q0 ◇ (q1 ◇ q2)):=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => t ◇ (q3 ◇ (q4 ◇ (q1 ◇ q2)))) ((h q0 q1 q2 q4).symm)).symm).trans ((h (q0 ◇ (q1 ◇ q2)) q4 (q1 ◇ q2) q3).symm)
  have apc1 : forall (q5 q6 q7 q8:G), (q6 ◇ (q7 ◇ q8)) = (q6 ◇ q5):=by
    intro q5 q6 q7 q8
    exact (((congrArg (fun t => q6 ◇ t) ((h q5 q7 q8 q5).symm)).symm).trans (apc0 q6 q7 q8 (q5 ◇ (q7 ◇ q8)) q5)).symm
  have apc2 : forall (q5 q6 q7 q8:G), (q6 ◇ q6) = (q6 ◇ q5):=by
    intro q5 q6 q7 q8
    exact (((apc1 q5 q6 q7 q8).symm).trans (apc1 q6 q6 q7 q8)).symm
  have apc3 : forall (q9 q10 q11 q12:G), (((q11 ◇ q12) ◇ q9) ◇ (q10 ◇ (q11 ◇ q12))) = (q11 ◇ q12):=by
    intro q9 q10 q11 q12
    exact ((congrArg (fun t => t ◇ (q10 ◇ (q11 ◇ q12))) (apc2 q9 (q11 ◇ q12) q9 q9)).symm).trans ((h (q11 ◇ q12) q11 q12 q10).symm)
  have apc6 : forall (q13 q14 q15 q16:G), (((q14 ◇ q15) ◇ q13) ◇ q16) = (q14 ◇ q15):=by
    intro q13 q14 q15 q16
    exact (((apc3 q13 q13 q14 q15).symm).trans (apc1 q16 ((q14 ◇ q15) ◇ q13) q13 (q14 ◇ q15))).symm
  have apc7 : forall (q17 q18 q19:G), (q17 ◇ (q18 ◇ q19)) = (q17 ◇ q17):=by
    intro q17 q18 q19
    exact ((apc2 q17 q17 q17 q17).trans ((apc1 q17 q17 q18 q19).symm)).symm
  have apc10 : forall (q0 q3 q20 q1 q2 q21:G), ((q20 ◇ q0) ◇ (q3 ◇ q3)) = q20:=by
    intro q0 q3 q20 q1 q2 q21
    exact ((((congrArg (fun t => (q20 ◇ q0) ◇ t) (congrArg (fun t => q3 ◇ t) (congrArg (fun t => (q0 ◇ (q1 ◇ q2)) ◇ t) (apc7 q21 q1 q2)))).trans (congrArg (fun t => (q20 ◇ q0) ◇ t) (congrArg (fun t => q3 ◇ t) (congrArg (fun t => t ◇ (q21 ◇ q21)) (apc7 q0 q1 q2))))).trans (congrArg (fun t => (q20 ◇ q0) ◇ t) (apc7 q3 (q0 ◇ q0) (q21 ◇ q21)))).symm).trans (((congrArg (fun t => t ◇ (q3 ◇ ((q0 ◇ (q1 ◇ q2)) ◇ (q21 ◇ (q1 ◇ q2))))) (congrArg (fun t => q20 ◇ t) ((h q0 q1 q2 q21).symm))).symm).trans ((h q20 (q0 ◇ (q1 ◇ q2)) (q21 ◇ (q1 ◇ q2)) q3).symm))
  have apc12 : forall (q22 q23 q24:G), (q24 ◇ q23) = (q24 ◇ q22):=by
    intro q22 q23 q24
    exact (((apc1 q22 q24 q22 q22).symm).trans (apc1 q23 q24 q22 q22)).symm
  have apc18 : forall (q25 q26 q27 q28:G), ((q28 ◇ q27) ◇ (q25 ◇ q26)) = q28:=by
    intro q25 q26 q27 q28
    exact ((congrArg (fun t => (q28 ◇ q27) ◇ t) (apc6 q25 q25 q26 ((q25 ◇ q26) ◇ q25))).symm).trans (apc10 q27 ((q25 ◇ q26) ◇ q25) q28 q25 q25 q25)
  have apc19 : forall (q29 q30 q31 q32 q33:G), ((q30 ◇ q31) ◇ q29) = q30:=by
    intro q29 q30 q31 q32 q33
    exact ((((((congrArg (fun t => (q30 ◇ q31) ◇ t) (congrArg (fun t => q32 ◇ t) (apc7 q33 q30 q31))).trans (congrArg (fun t => (q30 ◇ q31) ◇ t) (apc7 q32 q33 q33))).trans (apc7 (q30 ◇ q31) q32 q32)).trans (apc18 q30 q31 q31 q30)).symm).trans (((congrArg (fun t => t ◇ (q32 ◇ (q33 ◇ (q30 ◇ q31)))) (apc3 q29 q33 q30 q31)).symm).trans ((h ((q30 ◇ q31) ◇ q29) q33 (q30 ◇ q31) q32).symm))).symm
  exact (calc
    (x ◇ y) = (x ◇ z):=apc12 z y x
    _ = (((x ◇ z) ◇ y) ◇ (x ◇ y)):=(apc19 (x ◇ y) (x ◇ z) y x x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_21542_to_48840 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_21542_to_48840
