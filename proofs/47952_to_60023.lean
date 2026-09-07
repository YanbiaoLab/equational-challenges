-- Equation47952 → Equation60023
-- Recorded verdict: true
-- Premise: x * y = (x * (z * x)) * (y * w)
-- Conclusion: (x * x) * y = (x * z) * (y * y)
-- Original submission SHA-256: f3ec8166925cd836cf1fda192ff743909a7d909a4ad1f6c8d9aee3608c018d21
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (x ◇ (z ◇ x)) ◇ (y ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ x) ◇ y = (x ◇ z) ◇ (y ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3 q4:G), ((q0 ◇ (q1 ◇ q0)) ◇ q3) = ((q0 ◇ q4) ◇ (q3 ◇ q2)):=by
    intro q0 q1 q2 q3 q4
    exact (((congrArg (fun t => t ◇ (q3 ◇ q2)) ((h q0 q4 q1 (q0 ◇ (q1 ◇ q0))).symm)).symm).trans ((h (q0 ◇ (q1 ◇ q0)) q3 q4 q2).symm)).symm
  have apc1 : forall (q0 q1 q2 q3 q4:G), ((q0 ◇ q4) ◇ (q3 ◇ q2)) = ((q0 ◇ q0) ◇ (q3 ◇ q0)):=by
    intro q0 q1 q2 q3 q4
    exact ((apc0 q0 q1 q2 q3 q4).symm).trans (apc0 q0 q1 q0 q3 q0)
  have apc2 : forall (q5 q6:G), ((q5 ◇ q5) ◇ (q6 ◇ q5)) = (q5 ◇ q6):=by
    intro q5 q6
    exact ((apc1 q5 q5 q5 q6 (q5 ◇ q5)).symm).trans ((h q5 q6 q5 q5).symm)
  have apc3 : forall (q0 q1 q2 q3 q4 q5 q6:G), ((q0 ◇ q4) ◇ (q3 ◇ q2)) = (q0 ◇ q3):=by
    intro q0 q1 q2 q3 q4 q5 q6
    exact (apc1 q0 q1 q2 q3 q4).trans (apc2 q0 q3)
  have apc5 : forall (q7 q8 q9 q10 q11:G), ((q7 ◇ q8) ◇ q9) = (q7 ◇ q9):=by
    intro q7 q8 q9 q10 q11
    exact (((apc3 q7 ((q7 ◇ q10) ◇ (q9 ◇ q11)) q11 q9 q10 ((q7 ◇ q10) ◇ (q9 ◇ q11)) ((q7 ◇ q10) ◇ (q9 ◇ q11))).symm).trans (((congrArg (fun t => t ◇ (q9 ◇ q11)) (apc3 q7 q7 q7 q10 q8 q7 q7)).symm).trans (apc3 (q7 ◇ q8) q7 q11 q9 (q10 ◇ q7) q7 q7))).symm
  have apc6 : forall (q7 q10 q8 q12 q13:G), (q12 ◇ (q7 ◇ q8)) = (q12 ◇ (q7 ◇ q10)):=by
    intro q7 q10 q8 q12 q13
    exact (((apc5 q12 q13 (q7 ◇ q10) ((q12 ◇ q13) ◇ (q7 ◇ q10)) ((q12 ◇ q13) ◇ (q7 ◇ q10))).symm).trans (((congrArg (fun t => (q12 ◇ q13) ◇ t) (apc3 q7 q7 q7 q10 q8 q7 q7)).symm).trans (apc3 q12 q7 (q10 ◇ q7) (q7 ◇ q8) q13 q7 q7))).symm
  have apc7 : forall (q14 q15 q16 q17:G), (q15 ◇ (q16 ◇ q14)) = (q15 ◇ q16):=by
    intro q14 q15 q16 q17
    exact ((apc5 q15 (q17 ◇ q15) (q16 ◇ q14) ((q15 ◇ (q17 ◇ q15)) ◇ (q16 ◇ q14)) ((q15 ◇ (q17 ◇ q15)) ◇ (q16 ◇ q14))).symm).trans (((apc6 q16 q14 q14 (q15 ◇ (q17 ◇ q15)) q14).symm).trans ((h q15 q16 q17 q14).symm))
  exact (calc
    ((x ◇ x) ◇ y) = (x ◇ y):=apc5 x x y ((x ◇ x) ◇ y) ((x ◇ x) ◇ y)
    _ = ((x ◇ z) ◇ (y ◇ y)):=((apc5 x z (y ◇ y) ((x ◇ z) ◇ (y ◇ y)) ((x ◇ z) ◇ (y ◇ y))).trans (apc7 y x y (x ◇ (y ◇ y)))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_47952_to_60023 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_47952_to_60023
