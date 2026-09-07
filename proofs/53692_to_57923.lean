-- Equation53692 → Equation57923
-- Recorded verdict: true
-- Premise: x * y = (((z * w) * y) * x) * x
-- Conclusion: x * (y * z) = ((y * y) * z) * y
-- Original submission SHA-256: 7d07bb9325af063e3b1a238c86c1e4690e86f0afb77826c6cb16e51ab022cc48
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (((z ◇ w) ◇ y) ◇ x) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ z) = ((y ◇ y) ◇ z) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2:G), (((q2 ◇ q0) ◇ q1) ◇ q1) = (q1 ◇ q2):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ q1) (congrArg (fun t => t ◇ q1) ((h q2 q0 q0 q0).symm))).symm).trans ((h q1 q2 ((q0 ◇ q0) ◇ q0) q2).symm)
  have apc1 : forall (q3 q4 q5:G), (q5 ◇ (q4 ◇ q3)) = ((q5 ◇ q4) ◇ q5):=by
    intro q3 q4 q5
    exact (((congrArg (fun t => t ◇ q5) (apc0 q3 q5 q4)).symm).trans (apc0 q5 q5 (q4 ◇ q3))).symm
  have apc2 : forall (q6 q1:G), ((q1 ◇ q6) ◇ q1) = (q1 ◇ q1):=by
    intro q6 q1
    exact ((congrArg (fun t => t ◇ q1) ((h q1 q6 q6 q6).symm)).symm).trans ((h q1 q1 (q6 ◇ q6) q6).symm)
  have apc3 : forall (q6 q1 q3 q4 q5:G), (q5 ◇ (q4 ◇ q3)) = (q5 ◇ q5):=by
    intro q6 q1 q3 q4 q5
    exact (apc1 q3 q4 q5).trans (apc2 q4 q5)
  have apc4 : forall (q7 q8 q9:G), ((q9 ◇ q7) ◇ q8) = (q9 ◇ q9):=by
    intro q7 q8 q9
    exact ((((apc0 q7 (q9 ◇ q7) q9).trans (apc2 q7 q9)).symm).trans (((congrArg (fun t => t ◇ (q9 ◇ q7)) (apc2 q8 (q9 ◇ q7))).symm).trans ((h (q9 ◇ q7) q8 q9 q7).symm))).symm
  have apc5 : forall (x y z w:G), (z ◇ z) = (x ◇ x):=by
    intro x y z w
    exact ((((congrArg (fun t => t ◇ x) (congrArg (fun t => t ◇ x) (apc4 w y z))).trans (congrArg (fun t => t ◇ x) (apc4 z x z))).trans (apc4 z x z)).symm).trans ((((h x y z w).symm).trans (h x y x x)).trans (((congrArg (fun t => t ◇ x) (congrArg (fun t => t ◇ x) (apc4 x y x))).trans (congrArg (fun t => t ◇ x) (apc4 x x x))).trans (apc4 x x x)))
  have apc6 : forall (q10 q11 q12 q13:G), (q10 ◇ q11) = (q10 ◇ q10):=by
    intro q10 q11 q12 q13
    exact (((apc3 (q10 ◇ (q12 ◇ q13)) (q10 ◇ (q12 ◇ q13)) q13 q12 q10).symm).trans (((apc0 q11 q10 (q12 ◇ q13)).symm).trans ((h q10 q11 q12 q13).symm))).symm
  exact (calc
    (x ◇ (y ◇ z)) = (x ◇ x):=apc6 x (y ◇ z) x x
    _ = (((y ◇ y) ◇ z) ◇ ((y ◇ y) ◇ z)):=apc5 ((y ◇ y) ◇ z) x x x
    _ = (((y ◇ y) ◇ z) ◇ y):=(apc6 ((y ◇ y) ◇ z) y x x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_53692_to_57923 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_53692_to_57923
