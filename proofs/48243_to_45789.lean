-- Equation48243 → Equation45789
-- Recorded verdict: true
-- Premise: x * y = (z * (x * w)) * (w * u)
-- Conclusion: x * y = z * (((w * x) * w) * y)
-- Original submission SHA-256: a869425d0a4bef4dbd387e05b2ee1feb03243ebe440d534292c9904b17f47c12
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = (z ◇ (x ◇ w)) ◇ (w ◇ u)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ (((w ◇ x) ◇ w) ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z w u:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w u
    exact (h x y x x x).trans ((h x x x x x).symm)
  have apc1 : forall (q0 q1:G), ((q0 ◇ q0) ◇ (q0 ◇ q0)) = (q1 ◇ q1):=by
    intro q0 q1
    exact (((congrArg (fun t => t ◇ (q0 ◇ q0)) (apc0 q0 q0 (q0 ◇ q0) (q0 ◇ q0) (q0 ◇ q0))).trans (apc0 (q0 ◇ q0) (q0 ◇ q0) ((q0 ◇ q0) ◇ (q0 ◇ q0)) ((q0 ◇ q0) ◇ (q0 ◇ q0)) ((q0 ◇ q0) ◇ (q0 ◇ q0)))).symm).trans ((((congrArg (fun t => t ◇ (q0 ◇ q0)) ((h q0 q0 q0 q1 q0).symm)).symm).trans ((h q1 q0 (q0 ◇ (q0 ◇ q1)) q0 q0).symm)).trans (apc0 q1 q0 (q1 ◇ q0) (q1 ◇ q0) (q1 ◇ q0)))
  have apc5 : forall (q2 q3 q4:G), ((q4 ◇ q4) ◇ (q3 ◇ q2)) = (q3 ◇ q3):=by
    intro q2 q3 q4
    exact ((congrArg (fun t => t ◇ (q3 ◇ q2)) (apc0 q4 ((q2 ◇ q2) ◇ (q2 ◇ q2)) (q4 ◇ ((q2 ◇ q2) ◇ (q2 ◇ q2))) (q4 ◇ ((q2 ◇ q2) ◇ (q2 ◇ q2))) (q4 ◇ ((q2 ◇ q2) ◇ (q2 ◇ q2))))).symm).trans ((((congrArg (fun t => t ◇ (q3 ◇ q2)) (congrArg (fun t => q4 ◇ t) ((apc1 q2 q3).symm))).symm).trans ((h q3 q2 q4 q3 q2).symm)).trans (apc0 q3 q2 (q3 ◇ q2) (q3 ◇ q2) (q3 ◇ q2)))
  have apc6 : forall (q5 q6 q7:G), ((q5 ◇ q5) ◇ q6) = (q7 ◇ q7):=by
    intro q5 q6 q7
    exact (((((congrArg (fun t => t ◇ ((q5 ◇ q5) ◇ q5)) (apc0 q7 (q5 ◇ q5) (q7 ◇ (q5 ◇ q5)) (q7 ◇ (q5 ◇ q5)) (q7 ◇ (q5 ◇ q5)))).trans (apc0 (q7 ◇ q7) ((q5 ◇ q5) ◇ q5) ((q7 ◇ q7) ◇ ((q5 ◇ q5) ◇ q5)) ((q7 ◇ q7) ◇ ((q5 ◇ q5) ◇ q5)) ((q7 ◇ q7) ◇ ((q5 ◇ q5) ◇ q5)))).trans (apc5 q7 q7 q7)).symm).trans (((congrArg (fun t => t ◇ ((q5 ◇ q5) ◇ q5)) (congrArg (fun t => q7 ◇ t) (apc5 q5 q5 q5))).symm).trans ((h (q5 ◇ q5) q6 q7 (q5 ◇ q5) q5).symm))).symm
  have apc7 : forall (q5 q6 q7:G), ((q7 ◇ q7) ◇ q7) = ((q5 ◇ q5) ◇ q6):=by
    intro q5 q6 q7
    exact ((apc6 q5 q6 q7).trans ((apc6 q7 q7 q7).symm)).symm
  have apc10 : forall (q8 q9:G), ((q8 ◇ q8) ◇ q9) = (q8 ◇ q8):=by
    intro q8 q9
    exact ((((congrArg (fun t => t ◇ (q8 ◇ q8)) (apc0 q8 ((q8 ◇ q8) ◇ q8) (q8 ◇ ((q8 ◇ q8) ◇ q8)) (q8 ◇ ((q8 ◇ q8) ◇ q8)) (q8 ◇ ((q8 ◇ q8) ◇ q8)))).trans (apc5 q8 q8 q8)).symm).trans (((congrArg (fun t => t ◇ (q8 ◇ q8)) (congrArg (fun t => q8 ◇ t) (apc7 q8 q8 q8))).symm).trans ((h (q8 ◇ q8) q9 q8 q8 q8).symm))).symm
  have apc11 : forall (q10 q11:G), ((q11 ◇ q10) ◇ (q11 ◇ q10)) = (q11 ◇ q11):=by
    intro q10 q11
    exact (((apc10 (q11 ◇ q10) (q10 ◇ q10)).symm).trans ((h q11 q10 (q11 ◇ q10) q10 q10).symm)).trans (apc0 q11 q10 (q11 ◇ q10) (q11 ◇ q10) (q11 ◇ q10))
  have apc12 : forall (q12 q13 q14 q15:G), ((q13 ◇ q12) ◇ q14) = (q15 ◇ q15):=by
    intro q12 q13 q14 q15
    exact (((((congrArg (fun t => t ◇ ((q13 ◇ q12) ◇ q12)) (apc0 q15 (q13 ◇ q13) (q15 ◇ (q13 ◇ q13)) (q15 ◇ (q13 ◇ q13)) (q15 ◇ (q13 ◇ q13)))).trans (apc0 (q15 ◇ q15) ((q13 ◇ q12) ◇ q12) ((q15 ◇ q15) ◇ ((q13 ◇ q12) ◇ q12)) ((q15 ◇ q15) ◇ ((q13 ◇ q12) ◇ q12)) ((q15 ◇ q15) ◇ ((q13 ◇ q12) ◇ q12)))).trans (apc10 q15 (q15 ◇ q15))).symm).trans (((congrArg (fun t => t ◇ ((q13 ◇ q12) ◇ q12)) (congrArg (fun t => q15 ◇ t) (apc11 q12 q13))).symm).trans ((h (q13 ◇ q12) q14 q15 (q13 ◇ q12) q12).symm))).symm
  have apc18 : forall (q16 q17 q18 q19 q20 q21:G), (((q17 ◇ q16) ◇ q18) ◇ (q20 ◇ q19)) = (q21 ◇ q21):=by
    intro q16 q17 q18 q19 q20 q21
    exact (((congrArg (fun t => t ◇ (q20 ◇ q19)) ((apc12 q16 q17 q18 (q21 ◇ q20)).symm)).symm).trans ((h q21 q16 (q21 ◇ q20) q20 q19).symm)).trans (apc0 q21 q16 (q21 ◇ q16) (q21 ◇ q16) (q21 ◇ q16))
  have apc27 : forall (q22 q23 q24 q25 q26 q27 q28:G), ((((q23 ◇ q22) ◇ q24) ◇ (q26 ◇ q25)) ◇ q28) = (q27 ◇ q27):=by
    intro q22 q23 q24 q25 q26 q27 q28
    exact ((congrArg (fun t => t ◇ q28) ((apc18 q22 q23 q24 q25 q26 q27).symm)).symm).trans (apc10 q27 q28)
  have apc28 : forall (q29 q30 q31:G), (q31 ◇ q31) = (q30 ◇ q29):=by
    intro q29 q30 q31
    exact ((h q30 q29 ((q29 ◇ q29) ◇ q29) q29 q29).trans (apc27 q29 q29 q29 q29 q30 q31 (q29 ◇ q29))).symm
  exact ((apc28 y x (x ◇ y)).symm).trans (apc28 (((w ◇ x) ◇ w) ◇ y) z (x ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_48243_to_45789 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_48243_to_45789
