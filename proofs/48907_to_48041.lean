-- Equation48907 → Equation48041
-- Recorded verdict: true
-- Premise: x * y = ((y * x) * x) * (z * z)
-- Conclusion: x * y = (y * (x * y)) * (z * w)
-- Original submission SHA-256: 1a7f9f986a9091f8eae5267c764f68c5f23f7e6cd3bb5c98ac227f267308f89b
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = ((y ◇ x) ◇ x) ◇ (z ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (y ◇ (x ◇ y)) ◇ (z ◇ w)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2:G), ((q1 ◇ q1) ◇ (q0 ◇ (q1 ◇ q1))) = (((q1 ◇ q1) ◇ q0) ◇ (q2 ◇ q2)):=by
    intro q0 q1 q2
    exact (((congrArg (fun t => t ◇ (q2 ◇ q2)) ((h (q1 ◇ q1) q0 q1).symm)).symm).trans ((h (q1 ◇ q1) (q0 ◇ (q1 ◇ q1)) q2).symm)).symm
  have apc1 : forall (q3:G), ((q3 ◇ q3) ◇ (q3 ◇ (q3 ◇ q3))) = (q3 ◇ q3):=by
    intro q3
    exact (apc0 q3 q3 q3).trans ((h q3 q3 q3).symm)
  have apc2 : forall (q4 q5:G), ((q4 ◇ (q4 ◇ q4)) ◇ (q4 ◇ q4)) = ((q4 ◇ q4) ◇ (q5 ◇ q5)):=by
    intro q4 q5
    exact (((congrArg (fun t => t ◇ (q5 ◇ q5)) (apc1 q4)).symm).trans (((congrArg (fun t => t ◇ (q5 ◇ q5)) (congrArg (fun t => t ◇ (q4 ◇ (q4 ◇ q4))) (apc1 q4))).symm).trans ((h (q4 ◇ (q4 ◇ q4)) (q4 ◇ q4) q5).symm))).symm
  have apc3 : forall (q4 q5:G), ((q4 ◇ q4) ◇ (q5 ◇ q5)) = ((q4 ◇ q4) ◇ (q4 ◇ q4)):=by
    intro q4 q5
    exact ((apc2 q4 q5).symm).trans (apc2 q4 q4)
  have apc4 : forall (x y z:G), (((y ◇ x) ◇ x) ◇ (z ◇ z)) = (((y ◇ x) ◇ x) ◇ (x ◇ x)):=by
    intro x y z
    exact ((h x y z).symm).trans (h x y x)
  have apc6 : forall (q4 q5:G), ((q4 ◇ (q4 ◇ q4)) ◇ (q4 ◇ q4)) = ((q4 ◇ q4) ◇ (q4 ◇ q4)):=by
    intro q4 q5
    exact (apc2 q4 q5).trans (apc3 q4 q5)
  have apc8 : forall (q6 q7:G), (((q7 ◇ q6) ◇ q6) ◇ (q6 ◇ q6)) = (q6 ◇ q7):=by
    intro q6 q7
    exact ((apc4 q6 q7 q6).symm).trans ((h q6 q7 q6).symm)
  have apc9 : forall (q8:G), ((q8 ◇ q8) ◇ (q8 ◇ q8)) = (q8 ◇ q8):=by
    intro q8
    exact ((apc8 (q8 ◇ q8) (q8 ◇ q8)).symm).trans ((((congrArg (fun t => t ◇ ((q8 ◇ q8) ◇ (q8 ◇ q8))) (congrArg (fun t => t ◇ (q8 ◇ q8)) (apc6 q8 q8))).symm).trans (apc8 (q8 ◇ q8) (q8 ◇ (q8 ◇ q8)))).trans (apc1 q8))
  have apc11 : forall (q9:G), ((q9 ◇ q9) ◇ q9) = (q9 ◇ q9):=by
    intro q9
    exact (((((congrArg (fun t => t ◇ ((q9 ◇ q9) ◇ (q9 ◇ q9))) (apc9 q9)).trans (congrArg (fun t => (q9 ◇ q9) ◇ t) (apc9 q9))).trans (apc9 q9)).symm).trans (((congrArg (fun t => t ◇ ((q9 ◇ q9) ◇ (q9 ◇ q9))) (apc6 q9 q9)).symm).trans (apc8 (q9 ◇ q9) q9))).symm
  have apc12 : forall (q10:G), (q10 ◇ (q10 ◇ q10)) = (q10 ◇ q10):=by
    intro q10
    exact ((((congrArg (fun t => t ◇ (q10 ◇ q10)) (apc11 q10)).trans (apc9 q10)).symm).trans (((congrArg (fun t => t ◇ (q10 ◇ q10)) (congrArg (fun t => t ◇ q10) (apc11 q10))).symm).trans (apc8 q10 (q10 ◇ q10)))).symm
  have apc13 : forall (q4 q5:G), ((q4 ◇ q4) ◇ (q5 ◇ q5)) = (q4 ◇ q4):=by
    intro q4 q5
    exact (apc3 q4 q5).trans (apc9 q4)
  have apc14 : forall (q11 q12 q13:G), (q12 ◇ q12) = (q11 ◇ q11):=by
    intro q11 q12 q13
    exact ((((congrArg (fun t => t ◇ (q13 ◇ q13)) (apc13 q11 q12)).trans (apc13 q11 q13)).symm).trans ((((congrArg (fun t => t ◇ (q13 ◇ q13)) (congrArg (fun t => t ◇ (q12 ◇ q12)) (apc13 q11 q12))).symm).trans ((h (q12 ◇ q12) (q11 ◇ q11) q13).symm)).trans (apc13 q12 q11))).symm
  have apc21 : forall (q14 q15:G), (((q15 ◇ q14) ◇ q14) ◇ ((q15 ◇ q14) ◇ q14)) = (q14 ◇ q15):=by
    intro q14 q15
    exact ((apc12 ((q15 ◇ q14) ◇ q14)).symm).trans ((h q14 q15 ((q15 ◇ q14) ◇ q14)).symm)
  have apc22 : forall (q16 q17 q18:G), (q18 ◇ q18) = (q16 ◇ q17):=by
    intro q16 q17 q18
    exact (((apc21 q16 q17).symm).trans (apc14 q18 ((q17 ◇ q16) ◇ q16) q16)).symm
  exact ((apc22 x y (x ◇ y)).symm).trans (apc22 (y ◇ (x ◇ y)) (z ◇ w) (x ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_48907_to_48041 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_48907_to_48041
