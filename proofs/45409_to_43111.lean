-- Equation45409 → Equation43111
-- Recorded verdict: true
-- Premise: x * y = y * (((x * y) * z) * z)
-- Conclusion: x * y = z * (z * ((z * w) * x))
-- Original submission SHA-256: 82eb5c8a8f3e8e6b127139ae19b8a1dc2ab74e99214a7daf16aee6a515ccc3bf
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = y ◇ (((x ◇ y) ◇ z) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ (z ◇ ((z ◇ w) ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3:G), (q3 ◇ ((q0 ◇ (q2 ◇ q3)) ◇ (((q0 ◇ (q2 ◇ q3)) ◇ q1) ◇ q1))) = (q2 ◇ q3):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => q3 ◇ t) (congrArg (fun t => t ◇ (((q0 ◇ (q2 ◇ q3)) ◇ q1) ◇ q1)) ((h q0 (q2 ◇ q3) q1).symm))).symm).trans ((h q2 q3 (((q0 ◇ (q2 ◇ q3)) ◇ q1) ◇ q1)).symm)
  have apc1 : forall (x y z:G), (y ◇ (((x ◇ y) ◇ z) ◇ z)) = (y ◇ (((x ◇ y) ◇ x) ◇ x)):=by
    intro x y z
    exact ((h x y z).symm).trans (h x y x)
  have apc2 : forall (q4 q5:G), (q5 ◇ (((q4 ◇ q5) ◇ q4) ◇ q4)) = (q4 ◇ q5):=by
    intro q4 q5
    exact ((apc1 q4 q5 q4).symm).trans ((h q4 q5 q4).symm)
  have apc3 : forall (q6 q7 q8:G), (q8 ◇ ((q8 ◇ q6) ◇ (((q8 ◇ q6) ◇ q7) ◇ q7))) = (((q8 ◇ q6) ◇ q8) ◇ q8):=by
    intro q6 q7 q8
    exact ((congrArg (fun t => q8 ◇ t) (congrArg (fun t => (q8 ◇ q6) ◇ t) (congrArg (fun t => t ◇ q7) (congrArg (fun t => t ◇ q7) (apc2 q8 q6))))).symm).trans (((congrArg (fun t => q8 ◇ t) (congrArg (fun t => t ◇ (((q6 ◇ (((q8 ◇ q6) ◇ q8) ◇ q8)) ◇ q7) ◇ q7)) (apc2 q8 q6))).symm).trans (apc0 q6 q7 ((q8 ◇ q6) ◇ q8) q8))
  have apc4 : forall (q9 q10:G), (((q9 ◇ (q10 ◇ q9)) ◇ q9) ◇ q9) = (q10 ◇ q9):=by
    intro q9 q10
    exact ((apc3 (q10 ◇ q9) q9 q9).symm).trans (apc0 q9 q9 q10 q9)
  have apc6 : forall (q11 q12:G), (q11 ◇ ((q11 ◇ (q12 ◇ q11)) ◇ (q12 ◇ q11))) = (q12 ◇ q11):=by
    intro q11 q12
    exact ((congrArg (fun t => q11 ◇ t) (congrArg (fun t => (q11 ◇ (q12 ◇ q11)) ◇ t) (apc4 q11 q12))).symm).trans (apc0 q11 q11 q12 q11)
  have apc7 : forall (q13 q14 q15 q16:G), (q16 ◇ (q13 ◇ (q14 ◇ (q15 ◇ q16)))) = (q15 ◇ q16):=by
    intro q13 q14 q15 q16
    exact ((congrArg (fun t => q16 ◇ t) (apc6 (q14 ◇ (q15 ◇ q16)) q13)).symm).trans (apc0 q14 (q13 ◇ (q14 ◇ (q15 ◇ q16))) q15 q16)
  have apc8 : forall (q17 q18 q19 q20:G), (q20 ◇ (q17 ◇ q18)) = (q19 ◇ q20):=by
    intro q17 q18 q19 q20
    exact ((congrArg (fun t => q20 ◇ t) ((h q17 q18 (q19 ◇ q20)).symm)).symm).trans (apc7 q18 ((q17 ◇ q18) ◇ (q19 ◇ q20)) q19 q20)
  have apc10 : forall (q21 q22 q23 q24:G), (q24 ◇ (q23 ◇ (q21 ◇ q22))) = (q23 ◇ q24):=by
    intro q21 q22 q23 q24
    exact ((congrArg (fun t => q24 ◇ t) ((apc8 q21 q22 ((q23 ◇ q24) ◇ q23) q23).symm)).symm).trans (apc2 q23 q24)
  have apc13 : forall (q25 q26 q27:G), (q27 ◇ (q25 ◇ q26)) = (q26 ◇ q27):=by
    intro q25 q26 q27
    exact ((congrArg (fun t => q27 ◇ t) (apc10 q25 q25 q25 q26)).symm).trans (apc10 q25 (q25 ◇ q25) q26 q27)
  have apc14 : forall (q28 q29 q30:G), (q29 ◇ q30) = (q28 ◇ q30):=by
    intro q28 q29 q30
    exact (((apc7 ((q29 ◇ q30) ◇ (q28 ◇ (q28 ◇ q30))) q28 q28 q30).symm).trans ((h q29 q30 (q28 ◇ (q28 ◇ q30))).symm)).symm
  have apc16 : forall (q31 q32 q33 q34:G), (q34 ◇ q31) = (q32 ◇ q33):=by
    intro q31 q32 q33 q34
    exact ((apc13 ((q32 ◇ q33) ◇ q34) q34 q31).symm).trans (((apc14 q31 q33 (((q32 ◇ q33) ◇ q34) ◇ q34)).symm).trans ((h q32 q33 q34).symm))
  exact (apc16 y (x ◇ y) (z ◇ (z ◇ ((z ◇ w) ◇ x))) x).trans ((apc16 (z ◇ ((z ◇ w) ◇ x)) (x ◇ y) (z ◇ (z ◇ ((z ◇ w) ◇ x))) z).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_45409_to_43111 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_45409_to_43111
