-- Equation46704 → Equation61129
-- Recorded verdict: true
-- Premise: x * y = (z * w) * (z * (x * z))
-- Conclusion: (x * y) * x = (z * (y * w)) * x
-- Original submission SHA-256: 668181dcdb56687ea065f0af3241182152386db61c3a38099e8b5d56cafa2a2b
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ w) ◇ (z ◇ (x ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ x = (z ◇ (y ◇ w)) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z w:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w
    exact (h x y z w).trans ((h x x z w).symm)
  have apc1 : forall (q0 q1 q2 q3:G), ((q2 ◇ q0) ◇ (q2 ◇ q0)) = (q1 ◇ q1):=by
    intro q0 q1 q2 q3
    exact (((apc0 (q2 ◇ q0) (q2 ◇ (q1 ◇ q2)) q0 q0).symm).trans ((h q1 q3 q2 q0).symm)).trans (apc0 q1 q3 (q1 ◇ q3) (q1 ◇ q3))
  have apc3 : forall (q4 q5 q6 q7 q8:G), ((q6 ◇ q4) ◇ (q6 ◇ q4)) = (q6 ◇ q5):=by
    intro q4 q5 q6 q7 q8
    exact (((congrArg (fun t => (q6 ◇ q4) ◇ t) (apc0 q6 ((q7 ◇ q8) ◇ (q7 ◇ q8)) (q6 ◇ ((q7 ◇ q8) ◇ (q7 ◇ q8))) (q6 ◇ ((q7 ◇ q8) ◇ (q7 ◇ q8))))).trans (apc0 (q6 ◇ q4) (q6 ◇ q6) ((q6 ◇ q4) ◇ (q6 ◇ q6)) ((q6 ◇ q4) ◇ (q6 ◇ q6)))).symm).trans (((congrArg (fun t => (q6 ◇ q4) ◇ t) (congrArg (fun t => q6 ◇ t) ((apc1 q8 q6 q7 q8).symm))).symm).trans ((h q6 q5 q6 q4).symm))
  have apc5 : forall (q9 q10 q11 q12:G), ((q10 ◇ q10) ◇ (q10 ◇ q10)) = ((q11 ◇ q9) ◇ q12):=by
    intro q9 q10 q11 q12
    exact ((apc0 (q10 ◇ q10) ((q11 ◇ q9) ◇ (q11 ◇ q9)) ((q10 ◇ q10) ◇ ((q11 ◇ q9) ◇ (q11 ◇ q9))) ((q10 ◇ q10) ◇ ((q11 ◇ q9) ◇ (q11 ◇ q9)))).symm).trans (((congrArg (fun t => t ◇ ((q11 ◇ q9) ◇ (q11 ◇ q9))) (apc1 q9 q10 q11 q9)).symm).trans (apc3 (q11 ◇ q9) q12 (q11 ◇ q9) q9 q9))
  exact ((apc5 y ((x ◇ y) ◇ x) x x).symm).trans (apc5 (y ◇ w) ((x ◇ y) ◇ x) z x)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_46704_to_61129 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_46704_to_61129
