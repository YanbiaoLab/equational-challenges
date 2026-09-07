-- Equation43126 → Equation4408
-- Recorded verdict: true
-- Premise: x * y = z * (z * ((w * z) * x))
-- Conclusion: x * (x * y) = (y * y) * x
-- Original submission SHA-256: f04a4481de28cb21c40214fb5326aee921b9da1e50c05aa820bb83766b27e96f
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ (z ◇ ((w ◇ z) ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ (x ◇ y) = (y ◇ y) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (x y z w:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w
    exact (h x y z w).trans ((h x x z w).symm)
  have apc1 : forall (q0 q1 q2:G), (q1 ◇ q1) = (q0 ◇ q0):=by
    intro q0 q1 q2
    exact (((apc0 q1 (q1 ◇ ((q0 ◇ q1) ◇ q0)) q0 q0).symm).trans ((h q0 q2 q1 q0).symm)).trans (apc0 q0 q2 (q0 ◇ q2) (q0 ◇ q2))
  have apc2 : forall (q3 q4 q5 q6:G), ((q3 ◇ q3) ◇ q4) = (q5 ◇ q5):=by
    intro q3 q4 q5 q6
    exact ((((congrArg (fun t => q5 ◇ t) (apc0 q5 (q6 ◇ q6) (q5 ◇ (q6 ◇ q6)) (q5 ◇ (q6 ◇ q6)))).trans (apc0 q5 (q5 ◇ q5) (q5 ◇ (q5 ◇ q5)) (q5 ◇ (q5 ◇ q5)))).symm).trans ((((congrArg (fun t => q5 ◇ t) (congrArg (fun t => q5 ◇ t) (apc1 q6 (q3 ◇ q5) q6))).symm).trans ((h (q3 ◇ q5) q4 q5 q3).symm)).trans (congrArg (fun t => t ◇ q4) (apc0 q3 q5 (q3 ◇ q5) (q3 ◇ q5))))).symm
  have apc3 : forall (q6 q3 q4 q5:G), ((q5 ◇ q5) ◇ q5) = ((q3 ◇ q3) ◇ q4):=by
    intro q6 q3 q4 q5
    exact ((apc2 q3 q4 q5 q6).trans ((apc2 q5 q5 q5 q6).symm)).symm
  have apc6 : forall (q7 q8 q9:G), ((q9 ◇ q9) ◇ (q9 ◇ q9)) = ((q7 ◇ q7) ◇ q8):=by
    intro q7 q8 q9
    exact (((apc3 q7 q7 q8 q9).symm).trans (apc0 (q9 ◇ q9) q9 q7 q7)).symm
  have apc7 : forall (q10 q11 q12 q13:G), ((q11 ◇ q11) ◇ q10) = (q11 ◇ q11):=by
    intro q10 q11 q12 q13
    exact ((((congrArg (fun t => q11 ◇ t) (apc0 q11 ((q12 ◇ q12) ◇ q13) (q11 ◇ ((q12 ◇ q12) ◇ q13)) (q11 ◇ ((q12 ◇ q12) ◇ q13)))).trans (apc0 q11 (q11 ◇ q11) (q11 ◇ (q11 ◇ q11)) (q11 ◇ (q11 ◇ q11)))).symm).trans (((congrArg (fun t => q11 ◇ t) (congrArg (fun t => q11 ◇ t) (apc6 q12 q13 q11))).symm).trans ((h (q11 ◇ q11) q10 q11 q11).symm))).symm
  exact (calc
    (x ◇ (x ◇ y)) = (x ◇ x):=apc0 x (x ◇ y) x x
    _ = ((x ◇ x) ◇ x):=(apc7 x x x x).symm
    _ = ((y ◇ y) ◇ x):=(congrArg (fun t => t ◇ x) (apc1 x y x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_43126_to_4408 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_43126_to_4408
