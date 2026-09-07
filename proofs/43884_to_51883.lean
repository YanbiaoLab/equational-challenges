-- Equation43884 → Equation51883
-- Recorded verdict: true
-- Premise: x * y = z * ((y * y) * (x * z))
-- Conclusion: x * y = ((z * z) * (z * w)) * z
-- Original submission SHA-256: f374e4471f9e4d5259fdc1b12944c68a8d16fb03b814a68d8f2368bf8c1eee9b
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = z ◇ ((y ◇ y) ◇ (x ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((z ◇ z) ◇ (z ◇ w)) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3:G), (((q1 ◇ q1) ◇ (q0 ◇ q2)) ◇ ((q3 ◇ q3) ◇ (q0 ◇ q1))) = (q2 ◇ q3):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => ((q1 ◇ q1) ◇ (q0 ◇ q2)) ◇ t) (congrArg (fun t => (q3 ◇ q3) ◇ t) ((h q0 q1 q2).symm))).symm).trans ((h q2 q3 ((q1 ◇ q1) ◇ (q0 ◇ q2))).symm)
  have apc1 : forall (q0 q1 q3:G), ((q0 ◇ (q3 ◇ q3)) ◇ (q0 ◇ q1)) = ((q1 ◇ q1) ◇ q3):=by
    intro q0 q1 q3
    exact ((congrArg (fun t => (q0 ◇ (q3 ◇ q3)) ◇ t) ((h q0 q1 (q3 ◇ q3)).symm)).symm).trans ((h (q1 ◇ q1) q3 (q0 ◇ (q3 ◇ q3))).symm)
  have apc2 : forall (q4 q5:G), (((q4 ◇ q5) ◇ (q4 ◇ q5)) ◇ q4) = (q4 ◇ q5):=by
    intro q4 q5
    exact ((apc1 (q5 ◇ q5) (q4 ◇ q5) q4).symm).trans (apc0 q4 q5 q4 q5)
  have apc3 : forall (q6 q7:G), (((q7 ◇ q6) ◇ (q7 ◇ q6)) ◇ ((q7 ◇ q6) ◇ (q7 ◇ q6))) = (q7 ◇ q6):=by
    intro q6 q7
    exact ((congrArg (fun t => t ◇ ((q7 ◇ q6) ◇ (q7 ◇ q6))) (congrArg (fun t => (q7 ◇ q6) ◇ t) (apc2 q7 q6))).symm).trans ((((congrArg (fun t => t ◇ ((q7 ◇ q6) ◇ (q7 ◇ q6))) (congrArg (fun t => t ◇ (((q7 ◇ q6) ◇ (q7 ◇ q6)) ◇ q7)) (apc2 q7 q6))).symm).trans (apc2 ((q7 ◇ q6) ◇ (q7 ◇ q6)) q7)).trans (apc2 q7 q6))
  have apc4 : forall (q8 q9 q10 q11:G), (((q10 ◇ q11) ◇ (q10 ◇ q11)) ◇ ((q9 ◇ q9) ◇ (q8 ◇ q10))) = (q10 ◇ q11):=by
    intro q8 q9 q10 q11
    exact ((congrArg (fun t => t ◇ ((q9 ◇ q9) ◇ (q8 ◇ q10))) (congrArg (fun t => (q10 ◇ q11) ◇ t) (apc0 q8 q9 q10 q11))).symm).trans ((((congrArg (fun t => t ◇ ((q9 ◇ q9) ◇ (q8 ◇ q10))) (congrArg (fun t => t ◇ (((q9 ◇ q9) ◇ (q8 ◇ q10)) ◇ ((q11 ◇ q11) ◇ (q8 ◇ q9)))) (apc0 q8 q9 q10 q11))).symm).trans (apc2 ((q9 ◇ q9) ◇ (q8 ◇ q10)) ((q11 ◇ q11) ◇ (q8 ◇ q9)))).trans (apc0 q8 q9 q10 q11))
  have apc6 : forall (q12 q13:G), (((q12 ◇ q13) ◇ (q12 ◇ q13)) ◇ q13) = (q13 ◇ q13):=by
    intro q12 q13
    exact (((apc4 q12 q13 q13 q13).symm).trans (apc1 (q13 ◇ q13) (q12 ◇ q13) q13)).symm
  have apc7 : forall (q14 q15:G), (q14 ◇ q15) = (q14 ◇ q14):=by
    intro q14 q15
    exact (((apc4 q14 q15 q14 q14).symm).trans (apc0 q14 q14 q14 q15)).symm
  have apc9 : forall (q14 q15 q12 q13:G), (((q12 ◇ q12) ◇ (q12 ◇ q12)) ◇ q13) = (q13 ◇ q13):=by
    intro q14 q15 q12 q13
    exact (((congrArg (fun t => t ◇ q13) (congrArg (fun t => t ◇ (q12 ◇ q13)) (apc7 q12 q13))).trans (congrArg (fun t => t ◇ q13) (congrArg (fun t => (q12 ◇ q12) ◇ t) (apc7 q12 q13)))).symm).trans (apc6 q12 q13)
  have apc10 : forall (q16 q17 q18:G), (((q17 ◇ q16) ◇ (q17 ◇ q16)) ◇ q18) = (q18 ◇ q18):=by
    intro q16 q17 q18
    exact ((congrArg (fun t => t ◇ q18) (congrArg (fun t => (q17 ◇ q16) ◇ t) (apc3 q16 q17))).symm).trans (((congrArg (fun t => t ◇ q18) (congrArg (fun t => t ◇ (((q17 ◇ q16) ◇ (q17 ◇ q16)) ◇ ((q17 ◇ q16) ◇ (q17 ◇ q16)))) (apc3 q16 q17))).symm).trans (apc9 q16 q16 ((q17 ◇ q16) ◇ (q17 ◇ q16)) q18))
  have apc16 : forall (q19 q20 q21:G), (q21 ◇ q21) = (q20 ◇ q19):=by
    intro q19 q20 q21
    exact (((apc10 q19 q20 q21).symm).trans (apc7 ((q20 ◇ q19) ◇ (q20 ◇ q19)) q21)).trans (apc3 q19 q20)
  exact ((apc16 y x (x ◇ y)).symm).trans (apc16 z ((z ◇ z) ◇ (z ◇ w)) (x ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_43884_to_51883 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_43884_to_51883
