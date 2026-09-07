-- Equation41895 → Equation57048
-- Recorded verdict: true
-- Premise: x * y = y * (x * (y * (x * z)))
-- Conclusion: x * (y * z) = (y * (y * z)) * w
-- Original submission SHA-256: 12bdb542d04e4fc309f05576e7c747b0832b3696459d80aef8af3c30a4c66fe8
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = y ◇ (x ◇ (y ◇ (x ◇ z)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ z) = (y ◇ (y ◇ z)) ◇ w
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1:G), (q1 ◇ (q1 ◇ q0)) = (q0 ◇ q1):=by
    intro q0 q1
    exact ((congrArg (fun t => q1 ◇ t) ((h q1 q0 q0).symm)).symm).trans ((h q0 q1 (q1 ◇ q0)).symm)
  have apc1 : forall (q2 q3:G), ((q3 ◇ q2) ◇ q2) = (q2 ◇ q2):=by
    intro q2 q3
    exact ((congrArg (fun t => t ◇ q2) (apc0 q3 q2)).symm).trans (((apc0 (q2 ◇ (q2 ◇ q3)) q2).symm).trans ((h q2 q2 q3).symm))
  have apc2 : forall (q4 q5:G), (q5 ◇ (q4 ◇ q5)) = ((q5 ◇ q4) ◇ q5):=by
    intro q4 q5
    exact ((congrArg (fun t => q5 ◇ t) (apc0 q4 q5)).symm).trans (apc0 (q5 ◇ q4) q5)
  have apc4 : forall (q6 q7:G), ((q6 ◇ q7) ◇ (q7 ◇ q7)) = ((q7 ◇ q6) ◇ q7):=by
    intro q6 q7
    exact (((congrArg (fun t => (q6 ◇ q7) ◇ t) (apc1 q7 q6)).symm).trans (apc0 q7 (q6 ◇ q7))).trans (apc2 q6 q7)
  have apc5 : forall (q8 q9:G), (((q8 ◇ q8) ◇ q9) ◇ (q8 ◇ q8)) = (q8 ◇ q8):=by
    intro q8 q9
    exact ((((((congrArg (fun t => (q9 ◇ (q8 ◇ q8)) ◇ t) (apc1 q8 q8)).trans (apc1 (q8 ◇ q8) q9)).trans (apc4 q8 q8)).trans (apc1 q8 q8)).symm).trans (((congrArg (fun t => (q9 ◇ (q8 ◇ q8)) ◇ t) (apc4 q8 q8)).symm).trans (apc4 q9 (q8 ◇ q8)))).symm
  have apc6 : forall (q10 q11:G), (q11 ◇ (q10 ◇ q10)) = (q10 ◇ q10):=by
    intro q10 q11
    exact (((apc5 q10 q11).symm).trans ((((congrArg (fun t => ((q10 ◇ q10) ◇ q11) ◇ t) (apc5 q10 q11)).symm).trans (apc0 (q10 ◇ q10) ((q10 ◇ q10) ◇ q11))).trans (apc0 q11 (q10 ◇ q10)))).symm
  have apc9 : forall (q12 q13 q14:G), (q13 ◇ q14) = (q12 ◇ q12):=by
    intro q12 q13 q14
    exact (((((congrArg (fun t => q14 ◇ t) (congrArg (fun t => q13 ◇ t) (apc6 q12 q14))).trans (congrArg (fun t => q14 ◇ t) (apc6 q12 q13))).trans (apc6 q12 q14)).symm).trans (((congrArg (fun t => q14 ◇ t) (congrArg (fun t => q13 ◇ t) (congrArg (fun t => q14 ◇ t) (apc6 q12 q13)))).symm).trans ((h q13 q14 (q12 ◇ q12)).symm))).symm
  exact (apc9 (x ◇ (y ◇ z)) x (y ◇ z)).trans ((apc9 (x ◇ (y ◇ z)) (y ◇ (y ◇ z)) w).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_41895_to_57048 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_41895_to_57048
