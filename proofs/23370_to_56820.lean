-- Equation23370 → Equation56820
-- Recorded verdict: true
-- Premise: x = ((y ◇ x) ◇ y) ◇ (y ◇ (z ◇ z))
-- Conclusion: x ◇ (y ◇ y) = (x ◇ (z ◇ z)) ◇ x
-- Original submission SHA-256: 577266745b64b462c803cec6e01058461b7b6c1ee5e831dad7d42d858d8d1f98
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ x) ◇ y) ◇ (y ◇ (z ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ y) = (x ◇ (z ◇ z)) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2:G), ((q0 ◇ q0) ◇ ((q1 ◇ (q0 ◇ q0)) ◇ (q2 ◇ q2))) = q1:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ ((q1 ◇ (q0 ◇ q0)) ◇ (q2 ◇ q2))) ((h (q0 ◇ q0) q1 q0).symm)).symm).trans ((h q1 (q1 ◇ (q0 ◇ q0)) q2).symm)
  have apc4 : forall (q3 q4:G), ((((q3 ◇ q3) ◇ q4) ◇ (q3 ◇ q3)) ◇ (q3 ◇ q3)) = q4:=by
    intro q3 q4
    exact ((congrArg (fun t => (((q3 ◇ q3) ◇ q4) ◇ (q3 ◇ q3)) ◇ t) (apc0 q3 (q3 ◇ q3) (q3 ◇ q3))).symm).trans ((h q4 (q3 ◇ q3) ((q3 ◇ q3) ◇ (q3 ◇ q3))).symm)
  have apc5 : forall (q5 q6 q7:G), ((q6 ◇ q6) ◇ (q5 ◇ (q7 ◇ q7))) = (((q6 ◇ q6) ◇ q5) ◇ (q6 ◇ q6)):=by
    intro q5 q6 q7
    exact ((congrArg (fun t => (q6 ◇ q6) ◇ t) (congrArg (fun t => t ◇ (q7 ◇ q7)) (apc4 q6 q5))).symm).trans (apc0 q6 (((q6 ◇ q6) ◇ q5) ◇ (q6 ◇ q6)) q7)
  have apc6 : forall (q8 q9 q10:G), ((q10 ◇ q10) ◇ q8) = ((q9 ◇ q9) ◇ q8):=by
    intro q8 q9 q10
    exact (((congrArg (fun t => (q10 ◇ q10) ◇ t) ((h q8 (q9 ◇ q9) q9).symm)).symm).trans (apc5 (((q9 ◇ q9) ◇ q8) ◇ (q9 ◇ q9)) q10 (q9 ◇ q9))).trans ((congrArg (fun t => t ◇ (q10 ◇ q10)) (apc5 ((q9 ◇ q9) ◇ q8) q10 q9)).trans (apc4 q10 ((q9 ◇ q9) ◇ q8)))
  have apc7 : forall (q11 q12 q13:G), (q11 ◇ (q13 ◇ q13)) = (q11 ◇ (q12 ◇ q12)):=by
    intro q11 q12 q13
    exact ((congrArg (fun t => t ◇ (q13 ◇ q13)) (apc4 q13 q11)).symm).trans (((congrArg (fun t => t ◇ (q13 ◇ q13)) (congrArg (fun t => t ◇ (q13 ◇ q13)) (apc5 q11 q13 q12))).symm).trans (apc4 q13 (q11 ◇ (q12 ◇ q12))))
  have apc8 : forall (q14 q15:G), (q15 ◇ q15) = (q14 ◇ q14):=by
    intro q14 q15
    exact (((apc4 q14 (q14 ◇ q14)).symm).trans (((congrArg (fun t => t ◇ (q14 ◇ q14)) (congrArg (fun t => t ◇ (q14 ◇ q14)) (apc7 (q14 ◇ q14) q14 q15))).symm).trans (apc4 q14 (q15 ◇ q15)))).symm
  have apc9 : forall (q8 q9 q10:G), ((q9 ◇ q9) ◇ q8) = ((q8 ◇ q8) ◇ q8):=by
    intro q8 q9 q10
    exact ((apc6 q8 q9 q8).symm).trans (apc6 q8 q8 q8)
  have apc10 : forall (q11 q12 q13:G), (q11 ◇ (q12 ◇ q12)) = (q11 ◇ (q11 ◇ q11)):=by
    intro q11 q12 q13
    exact ((apc7 q11 q12 q11).symm).trans (apc7 q11 q11 q11)
  have apc18 : forall (q16 q17:G), (((q16 ◇ q16) ◇ q17) ◇ (q17 ◇ (q17 ◇ q17))) = q17:=by
    intro q16 q17
    exact ((congrArg (fun t => ((q16 ◇ q16) ◇ q17) ◇ t) (apc10 q17 q16 (q17 ◇ (q16 ◇ q16)))).symm).trans (((congrArg (fun t => t ◇ (q17 ◇ (q16 ◇ q16))) (apc6 q17 q16 q17)).symm).trans ((h q17 q17 q16).symm))
  have apc22 : forall (q18 q19 q20:G), (((q19 ◇ q19) ◇ q20) ◇ (q20 ◇ (q18 ◇ q18))) = q20:=by
    intro q18 q19 q20
    exact ((congrArg (fun t => ((q19 ◇ q19) ◇ q20) ◇ t) (congrArg (fun t => q20 ◇ t) (apc8 q18 q20))).symm).trans (apc18 q19 q20)
  have apc37 : forall (q21 q22 q2:G), ((q21 ◇ ((q22 ◇ q21) ◇ q22)) ◇ (((q22 ◇ q21) ◇ q22) ◇ (q2 ◇ q2))) = (q22 ◇ (q22 ◇ q22)):=by
    intro q21 q22 q2
    exact (((congrArg (fun t => t ◇ (((q22 ◇ q21) ◇ q22) ◇ (q2 ◇ q2))) (congrArg (fun t => t ◇ ((q22 ◇ q21) ◇ q22)) ((h q21 q22 q21).symm))).symm).trans ((h (q22 ◇ (q21 ◇ q21)) ((q22 ◇ q21) ◇ q22) q2).symm)).trans (apc10 q22 q21 (q22 ◇ (q21 ◇ q21)))
  have apc38 : forall (q23 q24:G), ((q24 ◇ (q23 ◇ q23)) ◇ q24) = (q24 ◇ (q24 ◇ q24)):=by
    intro q23 q24
    exact ((apc22 q23 ((q24 ◇ (q23 ◇ q23)) ◇ q24) ((q24 ◇ (q23 ◇ q23)) ◇ q24)).symm).trans (((congrArg (fun t => t ◇ (((q24 ◇ (q23 ◇ q23)) ◇ q24) ◇ (q23 ◇ q23))) (apc9 ((q24 ◇ (q23 ◇ q23)) ◇ q24) q23 q23)).symm).trans (apc37 (q23 ◇ q23) q24 q23))
  exact (calc
    (x ◇ (y ◇ y)) = (x ◇ (x ◇ x)):=apc10 x y (x ◇ (y ◇ y))
    _ = ((x ◇ (z ◇ z)) ◇ x):=((congrArg (fun t => t ◇ x) (apc10 x z (x ◇ (z ◇ z)))).trans (apc38 x x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_23370_to_56820 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_23370_to_56820
