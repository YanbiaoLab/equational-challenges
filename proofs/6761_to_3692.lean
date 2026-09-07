-- Equation6761 → Equation3692
-- Recorded verdict: true
-- Premise: x = y ◇ (x ◇ ((z ◇ z) ◇ (x ◇ y)))
-- Conclusion: x ◇ x = (y ◇ y) ◇ (z ◇ z)
-- Original submission SHA-256: 960f673017f8738586bd50a5170fa69393492aaa4daba9e8957c915cdacae43c
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (x ◇ ((z ◇ z) ◇ (x ◇ y)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = (y ◇ y) ◇ (z ◇ z)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 : G), (((q1 ◇ q1) ◇ (q0 ◇ q0)) ◇ (q1 ◇ q1)) = (q0 ◇ q0) := by
    intro q0 q1
    exact ((rfl).symm).trans ((((congrArg (fun t => ((q1 ◇ q1) ◇ (q0 ◇ q0)) ◇ t) ((h (q1 ◇ q1) (q0 ◇ q0) q0).symm)).symm).trans ((h (q0 ◇ q0) ((q1 ◇ q1) ◇ (q0 ◇ q0)) q1).symm)).trans (rfl))
  have apc1 : forall (q2 : G), ((q2 ◇ q2) ◇ ((q2 ◇ q2) ◇ (q2 ◇ q2))) = (q2 ◇ q2) := by
    intro q2
    exact ((rfl).symm).trans ((((congrArg (fun t => t ◇ ((q2 ◇ q2) ◇ (q2 ◇ q2))) (apc0 q2 q2)).symm).trans (apc0 q2 (q2 ◇ q2))).trans (rfl))
  have apc2 : forall (q3 : G), (q3 ◇ (q3 ◇ (q3 ◇ q3))) = q3 := by
    intro q3
    exact ((rfl).symm).trans ((((congrArg (fun t => q3 ◇ t) (congrArg (fun t => q3 ◇ t) (apc0 q3 q3))).symm).trans ((h q3 q3 (q3 ◇ q3)).symm)).trans (rfl))
  have apc3 : forall (q4 : G), ((q4 ◇ q4) ◇ (q4 ◇ q4)) = (q4 ◇ q4) := by
    intro q4
    exact ((rfl).symm).trans ((((congrArg (fun t => (q4 ◇ q4) ◇ t) (apc1 q4)).symm).trans (apc2 (q4 ◇ q4))).trans (rfl))
  have apc4 : forall (q0 q5 q1 : G), (((q0 ◇ q0) ◇ (q5 ◇ (q1 ◇ q1))) ◇ (q5 ◇ q5)) = q5 := by
    intro q0 q5 q1
    exact ((rfl).symm).trans ((((congrArg (fun t => ((q0 ◇ q0) ◇ (q5 ◇ (q1 ◇ q1))) ◇ t) (congrArg (fun t => q5 ◇ t) ((h q5 (q1 ◇ q1) q0).symm))).symm).trans ((h q5 ((q0 ◇ q0) ◇ (q5 ◇ (q1 ◇ q1))) q1).symm)).trans (rfl))
  have apc6 : forall (q6 q7 q8 : G), (((q7 ◇ q7) ◇ ((q6 ◇ q6) ◇ (q8 ◇ q8))) ◇ (q6 ◇ q6)) = (q6 ◇ q6) := by
    intro q6 q7 q8
    exact ((rfl).symm).trans ((((congrArg (fun t => ((q7 ◇ q7) ◇ ((q6 ◇ q6) ◇ (q8 ◇ q8))) ◇ t) (apc3 q6)).symm).trans (apc4 q7 (q6 ◇ q6) q8)).trans (rfl))
  have apc15 : forall (q9 q10 q11 : G), ((q10 ◇ q10) ◇ (((q10 ◇ q10) ◇ (q9 ◇ q9)) ◇ ((q11 ◇ q11) ◇ (q9 ◇ q9)))) = ((q10 ◇ q10) ◇ (q9 ◇ q9)) := by
    intro q9 q10 q11
    exact ((rfl).symm).trans ((((congrArg (fun t => (q10 ◇ q10) ◇ t) (congrArg (fun t => ((q10 ◇ q10) ◇ (q9 ◇ q9)) ◇ t) (congrArg (fun t => (q11 ◇ q11) ◇ t) (apc0 q9 q10)))).symm).trans ((h ((q10 ◇ q10) ◇ (q9 ◇ q9)) (q10 ◇ q10) q11).symm)).trans (rfl))
  have apc16 : forall (q12 q13 : G), (((q13 ◇ q13) ◇ (q12 ◇ q12)) ◇ (((q13 ◇ q13) ◇ (q12 ◇ q12)) ◇ ((q13 ◇ q13) ◇ (q12 ◇ q12)))) = ((q13 ◇ q13) ◇ (q12 ◇ q12)) := by
    intro q12 q13
    exact ((rfl).symm).trans ((((congrArg (fun t => t ◇ (((q13 ◇ q13) ◇ (q12 ◇ q12)) ◇ ((q13 ◇ q13) ◇ (q12 ◇ q12)))) (apc15 q12 q13 q12)).symm).trans (apc4 q13 ((q13 ◇ q13) ◇ (q12 ◇ q12)) (q12 ◇ q12))).trans (rfl))
  have apc17 : forall (q14 q15 : G), (((q15 ◇ q15) ◇ (q14 ◇ q14)) ◇ ((q15 ◇ q15) ◇ (q14 ◇ q14))) = ((q15 ◇ q15) ◇ (q14 ◇ q14)) := by
    intro q14 q15
    exact ((rfl).symm).trans ((((congrArg (fun t => ((q15 ◇ q15) ◇ (q14 ◇ q14)) ◇ t) (apc16 q14 q15)).symm).trans (apc2 ((q15 ◇ q15) ◇ (q14 ◇ q14)))).trans (rfl))
  have apc18 : forall (q16 q17 : G), ((q17 ◇ q17) ◇ ((q17 ◇ q17) ◇ (q16 ◇ q16))) = ((q17 ◇ q17) ◇ (q16 ◇ q16)) := by
    intro q16 q17
    exact ((rfl).symm).trans ((((congrArg (fun t => (q17 ◇ q17) ◇ t) (apc17 q16 q17)).symm).trans (apc15 q16 q17 q17)).trans (rfl))
  have apc19 : forall (q18 q19 : G), (q19 ◇ q19) = (q18 ◇ q18) := by
    intro q18 q19
    exact ((apc0 q19 q18).symm).trans ((((congrArg (fun t => t ◇ (q18 ◇ q18)) (apc18 q19 q18)).symm).trans (apc6 q18 q18 q19)).trans (rfl))
  exact (apc19 (y ◇ y) x).trans ((congrArg (fun t => (y ◇ y) ◇ t) (apc19 y z)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_6761_to_3692 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_6761_to_3692
