-- Equation44591 → Equation60283
-- Recorded verdict: true
-- Premise: x * y = y * ((z * (x * x)) * w)
-- Conclusion: (x * y) * x = (z * w) * (y * u)
-- Original submission SHA-256: c009807b22ae0c1d5b8caabcf9d9e06b5f96136cfe4dda7cdc972c1d70ec5d8e
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = y ◇ ((z ◇ (x ◇ x)) ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), (x ◇ y) ◇ x = (z ◇ w) ◇ (y ◇ u)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (q0 q1 q2 q3 q4:G), (q3 ◇ ((q0 ◇ q4) ◇ q2)) = ((q1 ◇ (q0 ◇ q0)) ◇ q3):=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => q3 ◇ t) (congrArg (fun t => t ◇ q2) ((h q0 q4 q1 (q1 ◇ (q0 ◇ q0))).symm))).symm).trans ((h (q1 ◇ (q0 ◇ q0)) q3 q4 q2).symm)
  have apc1 : forall (q5 q6 q7 q8:G), ((q5 ◇ (q8 ◇ q8)) ◇ q7) = (q6 ◇ q7):=by
    intro q5 q6 q7 q8
    exact ((apc0 q8 q5 q5 q7 (q6 ◇ q6)).symm).trans ((h q6 q7 q8 q5).symm)
  have apc2 : forall (q9 q10 q11 q12:G), ((q9 ◇ q10) ◇ q12) = (q11 ◇ q12):=by
    intro q9 q10 q11 q12
    exact ((congrArg (fun t => t ◇ q12) ((h q9 q10 q9 (q9 ◇ (q9 ◇ q9))).symm)).symm).trans (apc1 q10 q11 q12 (q9 ◇ (q9 ◇ q9)))
  have apc3 : forall (q13 q14 q15 q16 q17:G), ((q15 ◇ q16) ◇ q17) = ((q13 ◇ q14) ◇ q17):=by
    intro q13 q14 q15 q16 q17
    exact ((apc2 q13 q14 q13 q17).trans ((apc2 q15 q16 q13 q17).symm)).symm
  have apc7 : forall (q18 q19 q20 q21:G), (q21 ◇ (q18 ◇ q19)) = (q20 ◇ q21):=by
    intro q18 q19 q20 q21
    exact ((congrArg (fun t => q21 ◇ t) (apc1 q18 q18 q19 q20)).symm).trans ((h q20 q21 q18 q19).symm)
  have apc8 : forall (q22 q23 q24 q25 q26 q27:G), ((q25 ◇ q26) ◇ (q22 ◇ q23)) = (q24 ◇ q27):=by
    intro q22 q23 q24 q25 q26 q27
    exact (((apc7 q22 q23 q24 q27).symm).trans ((apc2 q25 q26 q27 (q22 ◇ q23)).symm)).symm
  have apc9 : forall (q28 q29 q30 q31 q32 q33 q34:G), ((q30 ◇ q31) ◇ (q28 ◇ q29)) = ((q32 ◇ q33) ◇ q34):=by
    intro q28 q29 q30 q31 q32 q33 q34
    exact (apc8 q28 q29 (q28 ◇ q28) q30 q31 q34).trans (apc3 q32 q33 q28 q28 q34)
  have apc14 : forall (q28 q29 q30 q31 q32 q33 q34:G), ((q32 ◇ q33) ◇ q34) = ((q28 ◇ q28) ◇ q28):=by
    intro q28 q29 q30 q31 q32 q33 q34
    exact ((apc9 q28 q29 q30 q31 q32 q33 q34).symm).trans (apc9 q28 q29 q30 q31 q28 q28 q28)
  exact (apc14 ((x ◇ y) ◇ x) ((x ◇ y) ◇ x) ((x ◇ y) ◇ x) ((x ◇ y) ◇ x) x y x).trans ((apc14 ((x ◇ y) ◇ x) ((x ◇ y) ◇ x) ((x ◇ y) ◇ x) ((x ◇ y) ◇ x) z w (y ◇ u)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_44591_to_60283 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_44591_to_60283
