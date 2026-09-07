-- Equation4191 → Equation42907
-- Recorded verdict: true
-- Premise: x * y = ((z * x) * x) * x
-- Conclusion: x * y = y * (z * ((w * u) * z))
-- Original submission SHA-256: 0d9f05a0a40c664f1f4ca3e5e8543d863acf393be758157fb9dd03be90b6047b
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = ((z ◇ x) ◇ x) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = y ◇ (z ◇ ((w ◇ u) ◇ z))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (x y z:G), (x ◇ y) = (x ◇ x):=by
    intro x y z
    exact (h x y z).trans ((h x x z).symm)
  have apc1 : forall (q0 q1 q2:G), ((q1 ◇ q0) ◇ q1) = (q1 ◇ q1):=by
    intro q0 q1 q2
    exact (((congrArg (fun t => t ◇ q1) ((h q1 q0 q0).symm)).symm).trans ((h q1 q2 (q0 ◇ q1)).symm)).trans (apc0 q1 q2 (q1 ◇ q2))
  have apc2 : forall (q3 q4:G), ((q4 ◇ q3) ◇ (q4 ◇ q3)) = (q4 ◇ q4):=by
    intro q3 q4
    exact (((apc1 q3 q4 q3).symm).trans (apc0 (q4 ◇ q3) q4 q3)).symm
  have apc3 : forall (q5 q6 q7:G), (q6 ◇ q6) = (q5 ◇ q5):=by
    intro q5 q6 q7
    exact ((((congrArg (fun t => (q6 ◇ q7) ◇ t) (congrArg (fun t => t ◇ q6) (congrArg (fun t => t ◇ q6) (apc0 q5 q6 (q5 ◇ q6))))).trans (apc0 (q6 ◇ q7) (((q5 ◇ q5) ◇ q6) ◇ q6) ((q6 ◇ q7) ◇ (((q5 ◇ q5) ◇ q6) ◇ q6)))).trans (apc2 q7 q6)).symm).trans ((((congrArg (fun t => t ◇ (((q5 ◇ q6) ◇ q6) ◇ q6)) ((h q6 q7 q5).symm)).symm).trans (apc2 q6 ((q5 ◇ q6) ◇ q6))).trans ((((congrArg (fun t => t ◇ ((q5 ◇ q6) ◇ q6)) (congrArg (fun t => t ◇ q6) (apc0 q5 q6 (q5 ◇ q6)))).trans (congrArg (fun t => ((q5 ◇ q5) ◇ q6) ◇ t) (congrArg (fun t => t ◇ q6) (apc0 q5 q6 (q5 ◇ q6))))).trans (apc2 q6 (q5 ◇ q5))).trans (apc2 q5 q5)))
  have apc6 : forall (q8 q9:G), ((q9 ◇ q9) ◇ (q9 ◇ q8)) = (q9 ◇ q9):=by
    intro q8 q9
    exact ((congrArg (fun t => t ◇ (q9 ◇ q8)) (apc0 q9 q8 q8)).symm).trans (apc2 q8 q9)
  have apc7 : forall (q10 q11:G), ((q10 ◇ q10) ◇ q11) = (q11 ◇ q11):=by
    intro q10 q11
    exact ((congrArg (fun t => t ◇ q11) (apc3 q10 q11 q10)).symm).trans (apc1 q11 q11 q10)
  have apc8 : forall (q12 q13 q14:G), ((q13 ◇ q12) ◇ q14) = (q13 ◇ q13):=by
    intro q12 q13 q14
    exact ((((((congrArg (fun t => t ◇ (q13 ◇ q12)) (apc7 q13 (q13 ◇ q12))).trans (congrArg (fun t => t ◇ (q13 ◇ q12)) (apc2 q12 q13))).trans (apc7 q13 (q13 ◇ q12))).trans (apc2 q12 q13)).symm).trans (((congrArg (fun t => t ◇ (q13 ◇ q12)) (congrArg (fun t => t ◇ (q13 ◇ q12)) (apc6 q12 q13))).symm).trans ((h (q13 ◇ q12) q14 (q13 ◇ q13)).symm))).symm
  have apc9 : forall (q15 q16 q17:G), (q17 ◇ q15) = (q16 ◇ q16):=by
    intro q15 q16 q17
    exact ((h q17 q15 q16).trans (apc8 q17 (q16 ◇ q17) q17)).trans (((congrArg (fun t => t ◇ (q16 ◇ q17)) (apc0 q16 q17 (q16 ◇ q17))).trans (congrArg (fun t => (q16 ◇ q16) ◇ t) (apc0 q16 q17 (q16 ◇ q17)))).trans (apc8 q16 q16 (q16 ◇ q16)))
  exact (apc9 y (x ◇ y) x).trans ((apc9 (z ◇ ((w ◇ u) ◇ z)) (x ◇ y) y).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_4191_to_42907 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_4191_to_42907
