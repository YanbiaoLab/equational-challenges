-- Equation53323 → Equation4520
-- Recorded verdict: true
-- Premise: x * y = (((y * y) * x) * x) * z
-- Conclusion: x * (y * z) = (x * w) * z
-- Original submission SHA-256: f4d527baaf177f6ddf575ed39c8693d137910fd913b57d9bc74d24bbfe431da8
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (((y ◇ y) ◇ x) ◇ x) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ z) = (x ◇ w) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1:G), (((q0 ◇ q0) ◇ q0) ◇ q1) = ((q0 ◇ q0) ◇ (q0 ◇ q0)):=by
    intro q0 q1
    exact ((congrArg (fun t => t ◇ q1) ((h (q0 ◇ q0) q0 (q0 ◇ q0)).symm)).symm).trans ((h (q0 ◇ q0) (q0 ◇ q0) q1).symm)
  have apc1 : forall (q2 q3:G), (((q2 ◇ q2) ◇ (q2 ◇ q2)) ◇ q3) = (q2 ◇ q2):=by
    intro q2 q3
    exact ((congrArg (fun t => t ◇ q3) (apc0 q2 q2)).symm).trans ((h q2 q2 q3).symm)
  have apc2 : forall (q4 q5:G), ((q4 ◇ q4) ◇ q5) = (q4 ◇ q4):=by
    intro q4 q5
    exact (((congrArg (fun t => t ◇ q5) (apc1 q4 (q4 ◇ q4))).symm).trans (apc0 (q4 ◇ q4) q5)).trans (apc1 q4 ((q4 ◇ q4) ◇ (q4 ◇ q4)))
  have apc3 : forall (q6 q7 q8:G), ((q6 ◇ q7) ◇ q8) = (q7 ◇ q7):=by
    intro q6 q7 q8
    exact (((congrArg (fun t => t ◇ q8) ((h q6 q7 (((q7 ◇ q7) ◇ q6) ◇ q6)).symm)).symm).trans (apc2 (((q7 ◇ q7) ◇ q6) ◇ q6) q8)).trans (((((congrArg (fun t => t ◇ (((q7 ◇ q7) ◇ q6) ◇ q6)) (congrArg (fun t => t ◇ q6) (apc2 q7 q6))).trans (congrArg (fun t => ((q7 ◇ q7) ◇ q6) ◇ t) (congrArg (fun t => t ◇ q6) (apc2 q7 q6)))).trans (congrArg (fun t => t ◇ ((q7 ◇ q7) ◇ q6)) (apc2 q7 q6))).trans (congrArg (fun t => (q7 ◇ q7) ◇ t) (apc2 q7 q6))).trans (apc2 q7 (q7 ◇ q7)))
  have apc6 : forall (q9 q10 q11:G), (q10 ◇ q10) = (q9 ◇ q9):=by
    intro q9 q10 q11
    exact (((apc3 q9 q9 q11).symm).trans (((congrArg (fun t => t ◇ q11) (apc3 q9 q9 q10)).symm).trans (apc3 (q9 ◇ q9) q10 q11))).symm
  have apc7 : forall (q12 q13:G), (q12 ◇ q13) = (q12 ◇ q12):=by
    intro q12 q13
    exact (((apc3 ((q13 ◇ q13) ◇ q12) q12 q12).symm).trans ((h q12 q13 q12).symm)).symm
  exact (calc
    (x ◇ (y ◇ z)) = (x ◇ x):=apc7 x (y ◇ z)
    _ = ((x ◇ w) ◇ (x ◇ w)):=apc6 (x ◇ w) x w
    _ = ((x ◇ w) ◇ z):=(apc7 (x ◇ w) z).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_53323_to_4520 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_53323_to_4520
