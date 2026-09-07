-- Equation53902 → Equation54000
-- Recorded verdict: true
-- Premise: x ◇ (x ◇ y) = y ◇ (x ◇ (z ◇ x))
-- Conclusion: x ◇ (x ◇ y) = z ◇ (w ◇ (w ◇ y))
-- Original submission SHA-256: be9a93893479d8e5f57f58700395e1d7168f4c5254fbe054f214ab04e2a361ab
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (x ◇ y) = y ◇ (x ◇ (z ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (x ◇ y) = z ◇ (w ◇ (w ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z:G), (y ◇ (x ◇ (z ◇ x))) = (y ◇ (x ◇ (x ◇ x))):=by
    intro x y z
    exact ((h x y z).symm).trans (h x y x)
  have apc1 : forall (x y z:G), (y ◇ (x ◇ (x ◇ x))) = (x ◇ (x ◇ y)):=by
    intro x y z
    exact ((h x y x).trans (apc0 x y x)).symm
  have apc2 : forall (q0 q1 q2:G), (q1 ◇ (q2 ◇ (q2 ◇ (q0 ◇ q2)))) = ((q0 ◇ q2) ◇ ((q0 ◇ q2) ◇ q1)):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => q1 ◇ t) ((h q2 (q0 ◇ q2) q0).symm)).symm).trans ((h (q0 ◇ q2) q1 q2).symm)
  have apc3 : forall (q3 q4 q5:G), ((q3 ◇ q5) ◇ ((q3 ◇ q5) ◇ q4)) = (q5 ◇ (q5 ◇ q4)):=by
    intro q3 q4 q5
    exact (((apc1 q5 q4 (q4 ◇ (q5 ◇ (q5 ◇ q5)))).symm).trans (((congrArg (fun t => q4 ◇ t) ((h q5 q5 q3).symm)).symm).trans (apc2 q3 q4 q5))).symm
  have apc4 : forall (q6 q7 q8:G), (q7 ◇ (q7 ◇ q8)) = (q6 ◇ (q6 ◇ q8)):=by
    intro q6 q7 q8
    exact ((((congrArg (fun t => (q6 ◇ (q6 ◇ q7)) ◇ t) (congrArg (fun t => t ◇ q8) (apc1 q6 q7 (q7 ◇ (q6 ◇ (q6 ◇ q6)))))).trans (apc3 q6 q8 (q6 ◇ q7))).trans (apc3 q6 q8 q7)).symm).trans ((((congrArg (fun t => t ◇ ((q7 ◇ (q6 ◇ (q6 ◇ q6))) ◇ q8)) (apc1 q6 q7 q6)).symm).trans (apc3 q7 q8 (q6 ◇ (q6 ◇ q6)))).trans ((apc3 q6 q8 (q6 ◇ q6)).trans (apc3 q6 q8 q6)))
  have apc5 : forall (q9 q10 q11:G), (q9 ◇ (q9 ◇ (q11 ◇ q10))) = (q10 ◇ (q10 ◇ q10)):=by
    intro q9 q10 q11
    exact ((apc4 q9 q10 (q11 ◇ q10)).symm).trans ((h q10 q10 q11).symm)
  have apc6 : forall (q12 q13:G), (q12 ◇ (q12 ◇ q13)) = (q12 ◇ (q12 ◇ q12)):=by
    intro q12 q13
    exact ((apc1 q12 q13 (q13 ◇ (q12 ◇ (q12 ◇ q12)))).symm).trans ((((congrArg (fun t => q13 ◇ t) (apc5 q13 q12 q12)).symm).trans (apc5 q13 (q12 ◇ q12) q13)).trans ((apc3 q12 (q12 ◇ q12) q12).trans (apc5 q12 q12 q12)))
  have apc9 : forall (q9 q14 q11:G), (q14 ◇ (q9 ◇ (q9 ◇ q9))) = (q11 ◇ (q11 ◇ q14)):=by
    intro q9 q14 q11
    exact ((congrArg (fun t => q14 ◇ t) (apc6 q9 q11)).symm).trans (((congrArg (fun t => q14 ◇ t) (apc4 q9 q11 q11)).symm).trans ((h q11 q14 q11).symm))
  have apc11 : forall (q15 q16:G), (q16 ◇ (q16 ◇ q15)) = (q15 ◇ (q15 ◇ q15)):=by
    intro q15 q16
    exact (((apc6 q15 (q15 ◇ q15)).symm).trans (apc9 q15 q15 q16)).symm
  have apc15 : forall (x y z q12 q13:G), (y ◇ (x ◇ (z ◇ x))) = (x ◇ (x ◇ x)):=by
    intro x y z q12 q13
    exact (((apc6 x y).symm).trans (h x y z)).symm
  exact (calc
    (x ◇ (x ◇ y)) = (y ◇ (y ◇ y)):=apc11 y x
    _ = (z ◇ (y ◇ (y ◇ y))):=(apc15 y z y w w).symm
    _ = (z ◇ (w ◇ (w ◇ y))):=(congrArg (fun t => z ◇ t) (apc11 y w)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_53902_to_54000 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_53902_to_54000
